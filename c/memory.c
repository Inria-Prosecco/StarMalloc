#include "memory.h"

#include <errno.h>
#include <sys/mman.h>

#include "internal/StarMalloc.h"
#include "fatal_error.h"
#include "Constants.h"

/// Mman.fst

// syscall wrapper: initialization (fatal error on failure)
uint8_t *mmap_init(size_t size) {
  size_t size2 = size + Constants_max_slab_size;
  void* ptr = mmap(NULL, size2, PROT_READ|PROT_WRITE, MAP_ANONYMOUS|MAP_PRIVATE|MAP_NORESERVE, -1, 0);
  if (ptr == MAP_FAILED) {
    if (errno != ENOMEM) {
      fatal_error("non-ENOMEM mmap failure");
    }
    fatal_error("mmap failed during initialization (returned NULL)");
  }
  uintptr_t addr = (uintptr_t) ptr;
  if (addr % Constants_max_slab_size != 0) {
    ptr += (size_t) (Constants_max_slab_size - addr % Constants_max_slab_size);
  }
  addr = (uintptr_t) ptr;
  if (addr % Constants_max_slab_size != 0) {
    fatal_error("mmap failed during initialization (misaligned)");
  }
  return ptr;
}

// syscall wrapper (large allocator allocation wrapper, can return NULL)
uint8_t *mmap_noinit(size_t size) {
  if (size > PTRDIFF_MAX) {
    fatal_error("allocation size should be <= PTRDIFF_MAX, returning NULL");
  }
  void* ptr = mmap(NULL, size, PROT_READ|PROT_WRITE, MAP_ANONYMOUS|MAP_PRIVATE|MAP_NORESERVE, -1, 0);
  if (ptr == MAP_FAILED) {
    if (errno != ENOMEM) {
      fatal_error("non-ENOMEM mmap failure");
    }
    return NULL;
  }
  return ptr;
}

// syscall wrapper (large allocator deallocation wrapper)
void munmap_u8(uint8_t* ptr, size_t len) {
  bool b = munmap((void*) ptr, len);
  if (b && errno != ENOMEM) {
    fatal_error("non-ENOMEM munmap failure");
  }
  return;
}

// monomorphised functions

// large allocator allocation wrapper
uint8_t *mmap_u8(size_t len) {
  return (uint8_t*) mmap_noinit(len * sizeof(uint8_t));
}

// slabs allocator init: initial large slabs mapping
uint8_t *mmap_u8_init(size_t len) {
  return (uint8_t*) mmap_init(len * sizeof(uint8_t));
}

// slabs allocator init: initial large slabs mapping
uint64_t *mmap_u64_init(size_t len) {
  return (uint64_t*) mmap_init(len * sizeof(uint64_t));
}

// slabs allocator init: initial large slabs mapping
ArrayList_cell *mmap_cell_status_init(size_t len) {
  return (ArrayList_cell*) mmap_init(len * sizeof(ArrayList_cell));
}

// slabs allocator init
size_t *mmap_ptr_us_init() {
  return (size_t*) mmap_init(sizeof(size_t));
}

// slabs allocator init
size_t *mmap_array_us_init(size_t len) {
  return (size_t*) mmap_init(len * sizeof(size_t));
}

// slabs allocator init
size_class* mmap_sc_init(size_t len) {
  return (size_class*) mmap_init(len * sizeof(size_class));
}

// slabs allocator init
uint32_t* mmap_sizes_init (size_t len) {
  return (uint32_t*) mmap_init(len * sizeof(uint32_t));
}

/// Mman2

// large allocator init
Impl_Trees_Cast_M_node** mmap_ptr_metadata_init() {
  return (Impl_Trees_Cast_M_node**) mmap_init(sizeof(Impl_Trees_Cast_M_node*));
}

/// MemoryTrap.fst

// syscall wrapper
void mmap_strict_trap (uint8_t* ptr, size_t len) {
  void* p = mmap((void*) ptr, len, PROT_NONE, MAP_ANONYMOUS|MAP_PRIVATE|MAP_FIXED, -1, 0);
  if (p == MAP_FAILED && errno != ENOMEM) {
    fatal_error("non-ENOMEM mmap failure");
  }
  return;
}

// syscall wrapper
void mmap_strict_untrap (uint8_t* ptr, size_t len) {
  void* p = mmap((void*) ptr, len, PROT_READ|PROT_WRITE, MAP_ANONYMOUS|MAP_PRIVATE|MAP_FIXED, -1, 0);
  if (p == MAP_FAILED && errno != ENOMEM) {
    fatal_error("non-ENOMEM mmap failure");
  }
  return;
}

// syscall wrapper
void mmap_trap (uint8_t* ptr, size_t len) {
  return;
}

// wrapper
void mmap_untrap (uint8_t* ptr, size_t len) {
  return;
}
