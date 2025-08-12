// SPDX-License-Identifier: Apache-2.0


#ifndef MemoryTrap_H
#define MemoryTrap_H

#include "krmllib.h"

extern void mmap_strict_trap(uint8_t *arr, size_t len);

extern void mmap_trap(uint8_t *arr, size_t len);

extern void mmap_strict_untrap(uint8_t *arr, size_t len);

extern void mmap_untrap(uint8_t *arr, size_t len);


#define MemoryTrap_H_DEFINED
#endif /* MemoryTrap_H */
