// SPDX-License-Identifier: Apache-2.0


#ifndef __MemoryTrap_H
#define __MemoryTrap_H

#include "krmllib.h"

extern void mmap_strict_trap(uint8_t *arr, size_t len);

extern void mmap_trap(uint8_t *arr, size_t len);

extern void mmap_strict_untrap(uint8_t *arr, size_t len);

extern void mmap_untrap(uint8_t *arr, size_t len);


#define __MemoryTrap_H_DEFINED
#endif
