// SPDX-License-Identifier: Apache-2.0


#ifndef __Mman_H
#define __Mman_H

#include "krmllib.h"

#include "SizeClass.h"
#include "ArrayList.h"

extern uint8_t *mmap_u8_init(size_t len);

extern uint64_t *mmap_u64_init(size_t len);

extern ArrayList_cell *mmap_cell_status_init(size_t len);

extern bool *mmap_bool_init(size_t len);

extern size_t *mmap_ptr_us_init(void);

extern size_t *mmap_array_us_init(size_t len);

typedef struct size_class_s
{
  SizeClass_size_class_struct_ data;
  Steel_SpinLock_lock lock;
}
size_class;

extern size_class *mmap_sc_init(size_t len);

extern uint32_t *mmap_sizes_init(size_t len);

extern uint8_t *mmap_u8(size_t size);

extern void munmap_u8(uint8_t *ptr, size_t size);


#define __Mman_H_DEFINED
#endif
