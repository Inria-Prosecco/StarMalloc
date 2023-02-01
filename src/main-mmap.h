#ifndef MAIN_MMAP_H_
#define MAIN_MMAP_H_

#include <stdint.h>
#include <stddef.h>

static uint8_t *mmap_u8(size_t len);

static uint64_t *mmap_u64(size_t len);

static ArrayList_cell__int32_t *mmap_cell_status(size_t len);

static uint32_t *mmap_ptr_u32(void);

static size_t *mmap_ptr_us(void);

#endif // MAIN_MMAP_H_

