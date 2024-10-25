#ifndef MEMORY_H_
#define MEMORY_H_

#include <stdint.h>
#include <stddef.h>
#include "ArrayList.h"

uint8_t *mmap_u8(size_t len);

uint64_t *mmap_u64(size_t len);

ArrayList_cell *mmap_cell_status (size_t len);

uint32_t *mmap_ptr_u32(void);

size_t *mmap_ptr_us(void);

void mmap_trap (uint8_t* ptr, size_t len);

#endif // MEMORY_H_

