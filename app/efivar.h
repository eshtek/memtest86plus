// SPDX-License-Identifier: GPL-2.0
#ifndef EFIVAR_H
#define EFIVAR_H
/**
 * \file
 *
 * Provides the ability to record the test results in a UEFI variable, so the
 * OS booted after the test run can retrieve them (e.g. on Linux, through
 * efivarfs). Only supported on x86/x86_64 UEFI boots; a no-op elsewhere.
 *
 *//*
 * Copyright (C) 2026 Eshtek Inc.
 */

#include <stdbool.h>

#if defined(__i386__) || defined(__x86_64__)

/**
 * Locates the EFI runtime services and captures the memory regions needed to
 * call them, while the boot params and EFI memory map are still intact. Must
 * be called during startup, before testing begins. A no-op unless the
 * "efivar" boot option was given and we were booted via UEFI.
 */
void efivar_init(void);

/**
 * Writes the current test results to the "MT86PlusResult" UEFI variable.
 * \param passes_completed  - the number of fully completed test passes.
 * \param final             - true if the test run is complete (maxpasses
 *                            reached); records a final pass/fail status.
 *
 * \returns
 * true if the variable was written successfully.
 */
bool efivar_write_results(int passes_completed, bool final);

#else

static inline void efivar_init(void) {}
static inline bool efivar_write_results(int passes_completed, bool final)
{
    (void)passes_completed;
    (void)final;
    return false;
}

#endif

#endif // EFIVAR_H
