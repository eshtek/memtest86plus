// SPDX-License-Identifier: GPL-2.0
// Copyright (C) 2026 Eshtek Inc.

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "boot.h"
#include "bootparams.h"
#include "efi.h"

#include "cpuinfo.h"
#include "memsize.h"
#include "pmem.h"
#include "tsc.h"
#include "vmem.h"

#include "config.h"
#include "display.h"
#include "error.h"
#include "reports.h"

#include "build_version.h"

#include "efivar.h"

//------------------------------------------------------------------------------
// Constants
//------------------------------------------------------------------------------

#define MAX_RT_REGIONS      32

#define PAYLOAD_BUF_SIZE    256

#define EFI_VAR_ATTRS       (EFI_VARIABLE_NON_VOLATILE | EFI_VARIABLE_BOOTSERVICE_ACCESS | EFI_VARIABLE_RUNTIME_ACCESS)

#define ONE_GB              UINT64_C(0x40000000)

// memtest's fixed virtual layout: [0,2GB) and [3.5GB,4GB) are permanently identity mapped,
// [2GB,3GB) is the test window (restored via map_window), and [3GB,3.5GB) is the pd3
// device-mapping window - the one range firmware runtime regions can land in that isn't
// identity mapped by default.
#define VM_DEV_START        (3 * ONE_GB)
#define VM_DEV_END          (3 * ONE_GB + ONE_GB / 2)

// Physical address field of a 2MB PDE, plus flags. PDE_2MB_PRESENT is the present+page-size
// pair we require when verifying a mapping; PDE_2MB_IDENTITY (present+write+page-size, 0x83,
// matching map_region) is what we write when forcing an identity mapping.
#define PDE_ADDR_MASK       UINT64_C(0x000fffffffe00000)
#define PDE_2MB_PRESENT     0x81
#define PDE_2MB_IDENTITY    0x83

#if (ARCH_BITS == 64)
// Table-pointer entries (pml4/pdpt levels): present + writable, pointing at the next-level
// table, whose physical address sits in bits [51:12].
#define PT_TABLE_FLAGS      UINT64_C(0x3)
#define PT_ADDR_MASK        UINT64_C(0x000ffffffffff000)

// Page-table pool for identity-mapping runtime regions above 4GB (boards with above-4G
// decoding put runtime MMIO up there). Each pool PD maps one 1GB slot with 2MB pages; each
// pool PDPT serves one 512GB pml4 slot beyond the first (the first reuses the boot `pdp`
// table, whose entries 4..511 are free). Demand is counted at init and the feature is
// disabled if it would exceed the pool - in practice boards expose one or two high runtime
// regions spanning a handful of GBs.
#define MAX_HIGH_PDS        8
#define MAX_HIGH_PDPTS      4
#endif

//------------------------------------------------------------------------------
// Types
//------------------------------------------------------------------------------

typedef struct {
    uint64_t    start;
    uint64_t    end;
} rt_region_t;

typedef efi_status_t (efiapi *efi_set_variable_t)(efi_char16_t *, efi_guid_t *, uint32_t, uintn_t, void *);
typedef efi_status_t (efiapi *efi_get_variable_t)(efi_char16_t *, efi_guid_t *, uint32_t *, uintn_t *, void *);

//------------------------------------------------------------------------------
// Private Variables
//------------------------------------------------------------------------------

// Vendor GUID for the results variable: b6c2f11a-8a95-4f5e-9c3f-4d1e2a7b9c05
static efi_guid_t results_guid = {
    0xb6c2f11a, 0x8a95, 0x4f5e, { 0x9c, 0x3f, 0x4d, 0x1e, 0x2a, 0x7b, 0x9c, 0x05 }
};

static efi_char16_t results_name[] = {
    'M', 'T', '8', '6', 'P', 'l', 'u', 's', 'R', 'e', 's', 'u', 'l', 't', 0
};

// EFI_GLOBAL_VARIABLE_GUID - owner of BootNext.
static efi_guid_t global_variable_guid = {
    0x8be4df61, 0x93ca, 0x11d2, { 0xaa, 0x0d, 0x00, 0xe0, 0x98, 0x03, 0x2b, 0x8c }
};

static efi_char16_t bootnext_name[] = {
    'B', 'o', 'o', 't', 'N', 'e', 'x', 't', 0
};

static efi_char16_t bootcurrent_name[] = {
    'B', 'o', 'o', 't', 'C', 'u', 'r', 'r', 'e', 'n', 't', 0
};

static efi_set_variable_t   efi_set_variable = NULL;
static efi_get_variable_t   efi_get_variable = NULL;

static rt_region_t          rt_regions[MAX_RT_REGIONS];
static int                  num_rt_regions = 0;

static bool                 need_window_remap = false;
static bool                 efi_var_usable = false;

// Snapshot of pd3 taken before map_runtime_window_identity() overwrites device-window slots,
// restored once the firmware calls return. The overwrite used to be treated as harmless
// ("we're about to reboot"), but mid-run writes broke that assumption: the screen framebuffer
// mapping lives in those slots, and clobbering it sent the next display update into whatever
// device the runtime MMIO region decodes (PCIe ECAM at 0xC0000000 on the boxes that froze) -
// hanging the machine right after an otherwise successful pass-end write.
static uint64_t             saved_pd3[512];

#if (ARCH_BITS == 64)
static uint64_t             high_pds[MAX_HIGH_PDS][512] __attribute__((aligned(4096)));
static uint64_t             high_pdpts[MAX_HIGH_PDPTS][512] __attribute__((aligned(4096)));

// Distinct 1GB slots (>= 4GB) covering the high runtime regions, and the distinct 512GB
// pml4 slots beyond the first that contain them. Both fixed at init.
static uint64_t             high_gb_slots[MAX_HIGH_PDS];
static int                  num_high_gb_slots = 0;
static uint64_t             high_pml4_slots[MAX_HIGH_PDPTS];
static int                  num_high_pml4_slots = 0;
#endif

//------------------------------------------------------------------------------
// Private Functions
//------------------------------------------------------------------------------

// Reload CR3 to flush stale TLB entries after editing the page tables.
static void reload_cr3(void)
{
    uintptr_t cr3;
    __asm__ __volatile__("mov %%cr3, %0" : "=r" (cr3));
    __asm__ __volatile__("mov %0, %%cr3" : : "r" (cr3) : "memory");
}

// The firmware runs in physical mode, so every region it touches must be identity mapped
// when we call it. [0,2GB) and [3.5GB,4GB) are permanently identity mapped, and [2GB,3GB)
// is restored by map_window(). The gap is [3GB,3.5GB): those pd3 entries hold whatever
// device/ACPI mappings map_region() built during the run, not identity. Real firmware
// (e.g. Gigabyte Z690/AMI) marks runtime MMIO in this range - e.g. a 256MB block at 3GB -
// and calling SetVariable would then dereference an address that maps to the wrong physical
// page. The caller snapshots pd3 first and restores it afterwards: the framebuffer mapping
// lives in these slots, and leaving them identity-mapped sends every later screen write into
// that runtime MMIO instead - a machine hang on boxes where it decodes PCIe config space.
// Runtime regions above 4GB are handled separately: on 64-bit builds
// map_high_runtime_identity() maps them from a static page-table pool for the duration of
// the SetVariable call; on 32-bit builds (PAE, 4-entry root, 4GB virtual space) they are
// unmappable and the feature is rejected at init.
static void map_runtime_window_identity(void)
{
    bool changed = false;
    for (int i = 0; i < num_rt_regions; i++) {
        uint64_t start = rt_regions[i].start;
        uint64_t end   = rt_regions[i].end;

        if (start < VM_DEV_START) start = VM_DEV_START;
        if (end > VM_DEV_END) end = VM_DEV_END;
        if (start >= end) continue;

        start &= ~(uint64_t)(VM_PAGE_SIZE - 1);
        for (uint64_t addr = start; addr < end; addr += VM_PAGE_SIZE) {
            pd3[(addr - VM_DEV_START) >> VM_PAGE_SHIFT] = addr | PDE_2MB_IDENTITY;
            changed = true;
        }
    }
    if (changed) reload_cr3();
}

// Post-condition check for map_runtime_window_identity(): confirm every runtime region in
// the [3GB,3.5GB) window is now identity mapped in pd3. A belt-and-braces guard against a
// mapping bug before we hand control to firmware - if it ever fails we skip the call rather
// than risk a hang.
static bool rt_regions_mapped(void)
{
    for (int i = 0; i < num_rt_regions; i++) {
        uint64_t start = rt_regions[i].start;
        uint64_t end   = rt_regions[i].end;

        if (start < VM_DEV_START) start = VM_DEV_START;
        if (end > VM_DEV_END) end = VM_DEV_END;
        if (start >= end) continue;

        start &= ~(uint64_t)(VM_PAGE_SIZE - 1);
        for (uint64_t addr = start; addr < end; addr += VM_PAGE_SIZE) {
            uint64_t pde = pd3[(addr - VM_DEV_START) >> VM_PAGE_SHIFT];
            if ((pde & PDE_2MB_PRESENT) != PDE_2MB_PRESENT || (pde & PDE_ADDR_MASK) != addr) {
                return false;
            }
        }
    }
    return true;
}

#if (ARCH_BITS == 64)
// Records the 1GB slots (and any pml4 slots beyond the first) needed to identity map the
// part of a runtime region above 4GB. Called at init, so pool exhaustion disables the
// feature up front rather than failing at write time. Returns false if the pool is too
// small for this board.
static bool record_high_region(uint64_t start, uint64_t end)
{
    if (start < 4 * ONE_GB) start = 4 * ONE_GB;

    for (uint64_t base = start & ~(ONE_GB - 1); base < end; base += ONE_GB) {
        int i = 0;
        while (i < num_high_gb_slots && high_gb_slots[i] != base) i++;
        if (i < num_high_gb_slots) continue;

        if (num_high_gb_slots == MAX_HIGH_PDS) return false;
        high_gb_slots[num_high_gb_slots++] = base;

        uint64_t pml4_base = base & ~((UINT64_C(1) << 39) - 1);
        if (pml4_base != 0) {
            int j = 0;
            while (j < num_high_pml4_slots && high_pml4_slots[j] != pml4_base) j++;
            if (j == num_high_pml4_slots) {
                if (num_high_pml4_slots == MAX_HIGH_PDPTS) return false;
                high_pml4_slots[num_high_pml4_slots++] = pml4_base;
            }
        }
    }
    return true;
}

// Identity-maps every recorded high 1GB slot from the static pool. Built fresh on every
// call and torn down by unmap_high_runtime_identity() right after SetVariable returns: the
// program relocates itself during testing and the pool tables move with it, so entries
// written here would dangle if they outlived the call. The boot `pdp` covers pml4 slot 0
// (its entries 4..511 are alignment padding, free for us); other pml4 slots get a pool
// PDPT first. All tables live in the image, which is always identity mapped, so a table's
// virtual address doubles as the physical address the paging entries need.
static void map_high_runtime_identity(void)
{
    if (num_high_gb_slots == 0) return;

    for (int i = 0; i < num_high_pml4_slots; i++) {
        uint64_t *pdpt = high_pdpts[i];
        for (int j = 0; j < 512; j++) {
            pdpt[j] = 0;
        }
        pml4[(high_pml4_slots[i] >> 39) & 511] = (uint64_t)(uintptr_t)pdpt | PT_TABLE_FLAGS;
    }
    for (int i = 0; i < num_high_gb_slots; i++) {
        uint64_t base = high_gb_slots[i];
        uint64_t *pd = high_pds[i];
        for (int j = 0; j < 512; j++) {
            pd[j] = (base + ((uint64_t)j << VM_PAGE_SHIFT)) | PDE_2MB_IDENTITY;
        }
        int pml4_idx = (int)((base >> 39) & 511);
        uint64_t *pdpt = pml4_idx == 0 ? pdp : (uint64_t *)(uintptr_t)(pml4[pml4_idx] & PT_ADDR_MASK);
        pdpt[(base >> 30) & 511] = (uint64_t)(uintptr_t)pd | PT_TABLE_FLAGS;
    }
    reload_cr3();
}

static void unmap_high_runtime_identity(void)
{
    if (num_high_gb_slots == 0) return;

    for (int i = 0; i < num_high_gb_slots; i++) {
        uint64_t base = high_gb_slots[i];
        if (((base >> 39) & 511) == 0) {
            pdp[(base >> 30) & 511] = 0;
        }
    }
    for (int i = 0; i < num_high_pml4_slots; i++) {
        pml4[(high_pml4_slots[i] >> 39) & 511] = 0;
    }
    reload_cr3();
}

// Post-condition check for map_high_runtime_identity(): walk the live tables and confirm
// every 2MB page of every high runtime region is identity mapped. Same belt-and-braces
// guard as rt_regions_mapped() - on failure we skip the firmware call rather than risk a
// hang.
static bool high_rt_regions_mapped(void)
{
    for (int i = 0; i < num_rt_regions; i++) {
        uint64_t start = rt_regions[i].start;
        uint64_t end   = rt_regions[i].end;

        if (end <= 4 * ONE_GB) continue;
        if (start < 4 * ONE_GB) start = 4 * ONE_GB;

        start &= ~(uint64_t)(VM_PAGE_SIZE - 1);
        for (uint64_t addr = start; addr < end; addr += VM_PAGE_SIZE) {
            uint64_t pml4e = pml4[(addr >> 39) & 511];
            if (!(pml4e & 1)) return false;
            const uint64_t *pdpt = (const uint64_t *)(uintptr_t)(pml4e & PT_ADDR_MASK);
            uint64_t pdpte = pdpt[(addr >> 30) & 511];
            if (!(pdpte & 1) || (pdpte & 0x80)) return false;
            const uint64_t *pd = (const uint64_t *)(uintptr_t)(pdpte & PT_ADDR_MASK);
            uint64_t pde = pd[(addr >> 21) & 511];
            if ((pde & PDE_2MB_PRESENT) != PDE_2MB_PRESENT || (pde & PDE_ADDR_MASK) != addr) {
                return false;
            }
        }
    }
    return true;
}
#endif

static char *append_char(char *pos, char *end, char c)
{
    if (pos < end) {
        *pos++ = c;
    }
    return pos;
}

static char *append_str(char *pos, char *end, const char *s)
{
    while (*s) {
        pos = append_char(pos, end, *s++);
    }
    return pos;
}

// Takes uintptr_t to avoid needing 64-bit division helpers on 32-bit builds.
static char *append_uint(char *pos, char *end, uintptr_t value, int min_width)
{
    char digits[20];
    int len = 0;

    if (value == 0) {
        digits[len++] = '0';
    }
    while (value > 0) {
        digits[len++] = '0' + value % 10;
        value /= 10;
    }
    while (len < min_width) {
        digits[len++] = '0';
    }
    while (len > 0) {
        pos = append_char(pos, end, digits[--len]);
    }
    return pos;
}

static uintptr_t irq_save(void)
{
    uintptr_t flags;
#ifdef __x86_64__
    __asm__ __volatile__("pushfq; popq %0; cli" : "=r" (flags) : : "memory");
#else
    __asm__ __volatile__("pushfl; popl %0; cli" : "=r" (flags) : : "memory");
#endif
    return flags;
}

static void irq_restore(uintptr_t flags)
{
    if (flags & 0x200) {
        __asm__ __volatile__("sti" : : : "memory");
    }
}

//------------------------------------------------------------------------------
// Public Functions
//------------------------------------------------------------------------------

void efivar_init(void)
{
    if (!enable_efi_var) return;

    const boot_params_t *boot_params = (boot_params_t *)boot_params_addr;
    const efi_info_t *efi_info = &boot_params->efi_info;

    uintptr_t rs_addr;

#if (ARCH_BITS == 64)
    if (efi_info->loader_signature != EFI64_LOADER_SIGNATURE) return;

    uintptr_t sys_tab_addr = (uintptr_t)efi_info->sys_tab_hi << 32 | (uintptr_t)efi_info->sys_tab;
    const efi64_system_table_t *sys_tab =
        (efi64_system_table_t *)map_region(sys_tab_addr, sizeof(efi64_system_table_t), true);
    if (sys_tab == NULL || sys_tab->header.signature != EFI_SYSTEM_TABLE_SIGNATURE) return;

    rs_addr = sys_tab->runtime_services;
#else
    if (efi_info->loader_signature != EFI32_LOADER_SIGNATURE) return;

    const efi32_system_table_t *sys_tab =
        (efi32_system_table_t *)map_region(efi_info->sys_tab, sizeof(efi32_system_table_t), true);
    if (sys_tab == NULL || sys_tab->header.signature != EFI_SYSTEM_TABLE_SIGNATURE) return;

    rs_addr = sys_tab->runtime_services;
#endif

    const efi_runtime_services_t *rs =
        (efi_runtime_services_t *)map_region(rs_addr, sizeof(efi_runtime_services_t), true);
    if (rs == NULL || rs->header.signature != EFI_RUNTIME_SERVICES_SIGNATURE) return;
    if (rs->set_variable == NULL) return;

    // Capture the runtime memory regions now - the EFI memory map lives in
    // loader data, which will be overwritten once testing starts.
    uintptr_t mem_map_addr = efi_info->mem_map;
#if (ARCH_BITS == 64)
    mem_map_addr |= (uintptr_t)efi_info->mem_map_hi << 32;
#endif
    size_t mem_map_size  = efi_info->mem_map_size;
    size_t mem_desc_size = efi_info->mem_desc_size;
    if (mem_map_addr == 0 || mem_desc_size == 0) return;

    mem_map_addr = map_region(mem_map_addr, mem_map_size, true);
    if (mem_map_addr == 0) return;

    size_t num_descs = mem_map_size / mem_desc_size;
    for (size_t i = 0; i < num_descs; i++) {
        const efi_memory_desc_t *desc = (const efi_memory_desc_t *)(mem_map_addr + i * mem_desc_size);
        if (!(desc->attribute & EFI_MEMORY_RUNTIME)) {
            continue;
        }

        uint64_t start = desc->phys_addr;
        uint64_t end   = start + (desc->num_pages << PAGE_SHIFT);

        if (end > 4 * ONE_GB) {
#if (ARCH_BITS == 64)
            // Above 4GB - typically runtime MMIO placed high by above-4G decoding.
            // Mappable via the high page-table pool as long as it stays within 4-level
            // paging's reach; a region we can't identity map makes the firmware unsafe
            // to call.
            if (end > (UINT64_C(1) << 48)) return;
            if (!record_high_region(start, end)) return;
#else
            // PAE's 4-entry root maps only 4GB of virtual space, so a runtime region
            // above 4GB can never be identity mapped here - the firmware is unsafe to
            // call.
            return;
#endif
        }

        if (start < VM_DEV_START && end > 2 * ONE_GB) {
            need_window_remap = true;
        }

        if (num_rt_regions == MAX_RT_REGIONS) return;
        rt_regions[num_rt_regions].start = start;
        rt_regions[num_rt_regions].end   = end;
        num_rt_regions++;
    }

#ifdef EFIVAR_TEST_HIGH_REGIONS
    // Test hook, never defined by the shipping Makefiles: injects fake high runtime
    // regions so the >4GB mapping path can be exercised in QEMU/OVMF, whose firmware
    // never places runtime regions up there. The firmware won't dereference the fakes,
    // so they don't need to be RAM-backed.
    {
        static const uint64_t fakes[][2] = {
            { UINT64_C(0x140000000), UINT64_C(0x144000000) },   // 5GB, pdp[4..] path
            { UINT64_C(0x8000000000), UINT64_C(0x8008000000) }, // 512GB, pml4 pool path
        };
        for (unsigned int i = 0; i < sizeof(fakes) / sizeof(fakes[0]); i++) {
            if (!record_high_region(fakes[i][0], fakes[i][1])) return;
            if (num_rt_regions == MAX_RT_REGIONS) return;
            rt_regions[num_rt_regions].start = fakes[i][0];
            rt_regions[num_rt_regions].end   = fakes[i][1];
            num_rt_regions++;
        }
    }
#endif

#ifdef EFIVAR_TEST_UNUSABLE
    // Test hook, never defined by the shipping Makefiles: leave the feature disabled, as
    // on firmware we cannot safely call - for exercising the write-failure path.
    return;
#endif

    efi_set_variable = rs->set_variable;
    efi_get_variable = (efi_get_variable_t)rs->get_variable;
    efi_var_usable = true;
}

// Undo the temporary firmware-call mappings: put the run's device mappings back into pd3
// (framebuffer included) and drop any high-region tables. Must run on every exit path of
// efivar_write_results once the snapshot has been taken.
static void restore_run_mappings(void)
{
    for (int i = 0; i < 512; i++) {
        pd3[i] = saved_pd3[i];
    }
#if (ARCH_BITS == 64)
    unmap_high_runtime_identity();
#endif
    reload_cr3();
}

bool efivar_write_results(int passes_completed, bool final)
{
    if (!efi_var_usable) return false;

    for (int i = 0; i < 512; i++) {
        saved_pd3[i] = pd3[i];
    }

    if (need_window_remap) {
        // Restore the identity mapping of [2GB,3GB). The next test window
        // re-establishes its own mapping, so no need to switch back.
        map_window(PAGE_C(2,GB));
    }
    // Identity-map any runtime region living in the [3GB,3.5GB) device window, then confirm
    // it took. Without this, firmware runtime MMIO placed there (seen on real Z690/AMI HW)
    // makes the physical-mode SetVariable call dereference the wrong page.
    map_runtime_window_identity();
    if (!rt_regions_mapped()) {
        restore_run_mappings();
        efi_var_usable = false;
        return false;
    }
#if (ARCH_BITS == 64)
    // Same for runtime regions above 4GB (seen on real ASUS/AMI HW with above-4G decoding:
    // a runtime MMIO block at 98GB), which need page-table entries of their own.
    map_high_runtime_identity();
    if (!high_rt_regions_mapped()) {
        restore_run_mappings();
        efi_var_usable = false;
        return false;
    }
#endif

    char buf[PAYLOAD_BUF_SIZE];
    char *end = buf + sizeof(buf) - 1;
    char *pos = buf;

    pos = append_str(pos, end, "MT86P fmt=1 version=" MT_VERSION "." GIT_HASH " state=");
    pos = append_str(pos, end, !final ? "running" : error_count == 0 ? "pass" : "fail");
    pos = append_str(pos, end, " passes=");
    pos = append_uint(pos, end, passes_completed, 1);
    pos = append_str(pos, end, " errors=");
    pos = append_uint(pos, end, (uintptr_t)error_count, 1);
    pos = append_str(pos, end, " ecc_errors=");
    pos = append_uint(pos, end, (uintptr_t)error_count_cecc, 1);

    if (clks_per_msec > 0 && run_start_time > 0) {
        pos = append_str(pos, end, " elapsed=");
        pos = append_uint(pos, end, (uintptr_t)((get_tsc() - run_start_time) / (1000 * (uint64_t)clks_per_msec)), 1);
    }

    pos = append_str(pos, end, " mem_mb=");
    pos = append_uint(pos, end, (uintptr_t)(num_pm_pages / 256), 1);

    int year, mon, day, hour, min, sec;
    rtc_get_datetime(&year, &mon, &day, &hour, &min, &sec);
    pos = append_str(pos, end, " rtc=\"");
    pos = append_uint(pos, end, year, 4);
    pos = append_char(pos, end, '-');
    pos = append_uint(pos, end, mon, 2);
    pos = append_char(pos, end, '-');
    pos = append_uint(pos, end, day, 2);
    pos = append_char(pos, end, ' ');
    pos = append_uint(pos, end, hour, 2);
    pos = append_char(pos, end, ':');
    pos = append_uint(pos, end, min, 2);
    pos = append_char(pos, end, ':');
    pos = append_uint(pos, end, sec, 2);
    pos = append_char(pos, end, '"');

    *pos = '\0';

    uintptr_t flags = irq_save();
    efi_status_t status = efi_set_variable(results_name, &results_guid, EFI_VAR_ATTRS,
                                           (uintn_t)(pos - buf + 1), buf);
    if (final) {
        // The firmware must delete BootNext when it consumes it, but real AMI boards have
        // been seen leaving it set - the self-reboot after this write then boots the test
        // AGAIN instead of returning to the OS. Delete it ourselves while the runtime
        // mappings are in place; a spec-compliant firmware just returns EFI_NOT_FOUND.
        // Done even when the results write failed - a boot loop is worse than a lost
        // result.
        efi_set_variable(bootnext_name, &global_variable_guid, 0, 0, NULL);

        // With `oneshot`, also delete the Boot#### entry we were booted from. Some AMI
        // firmware re-tries a boot option it considers failed (no OS-ready handshake
        // before the reset) on the next boot, ignoring BootOrder and needing no BootNext -
        // seen on Z690 AERO D: a completed run's reboot landed back in memtest even after
        // BootNext was deleted. A nonexistent entry can't be retried. Opt-in only: a user
        // who boots memtest from a permanent boot entry must never lose it.
        if (one_shot_boot && efi_get_variable != NULL) {
            uint16_t current = 0;
            uintn_t size = sizeof(current);
            efi_status_t get_status =
                efi_get_variable(bootcurrent_name, &global_variable_guid, NULL, &size, &current);
            if (get_status == 0 && size == sizeof(current)) {
                static const char hex_digits[] = "0123456789ABCDEF";
                efi_char16_t entry_name[9] = { 'B', 'o', 'o', 't', 0, 0, 0, 0, 0 };
                entry_name[4] = hex_digits[(current >> 12) & 0xf];
                entry_name[5] = hex_digits[(current >> 8) & 0xf];
                entry_name[6] = hex_digits[(current >> 4) & 0xf];
                entry_name[7] = hex_digits[current & 0xf];
                efi_set_variable(entry_name, &global_variable_guid, 0, 0, NULL);
            }
        }
    }
    irq_restore(flags);

    restore_run_mappings();

    return status == EFI_SUCCESS;
}
