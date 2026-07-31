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

// Physical address field of a 2MB PDE, plus the present and page-size flags.
#define PDE_ADDR_MASK       UINT64_C(0x000fffffffe00000)
#define PDE_2MB_FLAGS       0x81

//------------------------------------------------------------------------------
// Types
//------------------------------------------------------------------------------

typedef struct {
    uint64_t    start;
    uint64_t    end;
} rt_region_t;

typedef efi_status_t (efiapi *efi_set_variable_t)(efi_char16_t *, efi_guid_t *, uint32_t, uintn_t, void *);

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

static efi_set_variable_t   efi_set_variable = NULL;

static rt_region_t          rt_regions[MAX_RT_REGIONS];
static int                  num_rt_regions = 0;

static bool                 need_window_remap = false;
static bool                 efi_var_usable = false;

//------------------------------------------------------------------------------
// Private Functions
//------------------------------------------------------------------------------

// The firmware runs in physical mode, so every region it needs must be
// identity mapped when we call it. Virtual [0,2GB) and [3.5GB,4GB) are
// permanently identity mapped. [2GB,3GB) is restored by map_window() before
// the call. Virtual [3GB,3.5GB) is backed by pd3 entries that map_region()
// may have retargeted to device mappings - verify any runtime region there
// is still identity mapped.
static bool rt_regions_mapped(void)
{
    for (int i = 0; i < num_rt_regions; i++) {
        uint64_t start = rt_regions[i].start;
        uint64_t end   = rt_regions[i].end;

        if (start < 3 * ONE_GB) start = 3 * ONE_GB;
        if (end > 3 * ONE_GB + ONE_GB / 2) end = 3 * ONE_GB + ONE_GB / 2;

        start &= ~(uint64_t)(VM_PAGE_SIZE - 1);
        for (uint64_t addr = start; addr < end; addr += VM_PAGE_SIZE) {
            uint64_t pde = pd3[(addr - 3 * ONE_GB) >> VM_PAGE_SHIFT];
            if ((pde & PDE_2MB_FLAGS) != PDE_2MB_FLAGS || (pde & PDE_ADDR_MASK) != addr) {
                return false;
            }
        }
    }
    return true;
}

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

        // Runtime regions we can't identity map make the firmware unsafe to call.
        if (end > 4 * ONE_GB) return;

        if (start < 3 * ONE_GB && end > 2 * ONE_GB) {
            need_window_remap = true;
        }

        if (num_rt_regions == MAX_RT_REGIONS) return;
        rt_regions[num_rt_regions].start = start;
        rt_regions[num_rt_regions].end   = end;
        num_rt_regions++;
    }

    efi_set_variable = rs->set_variable;
    efi_var_usable = true;
}

bool efivar_write_results(int passes_completed, bool final)
{
    if (!efi_var_usable) return false;

    if (need_window_remap) {
        // Restore the identity mapping of [2GB,3GB). The next test window
        // re-establishes its own mapping, so no need to switch back.
        map_window(PAGE_C(2,GB));
    }
    if (!rt_regions_mapped()) {
        efi_var_usable = false;
        return false;
    }

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
    irq_restore(flags);

    return status == EFI_SUCCESS;
}
