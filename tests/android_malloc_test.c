#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

void malloc_std(void) {
  uint8_t* ptr = (uint8_t*) malloc(100);
  assert (ptr != NULL);
  ptr[99] = 1;
  free(ptr);
}

void malloc_overflow(void) {
  uint8_t* ptr = malloc(SIZE_MAX);
  assert (ptr == NULL);
  //errno
}

void calloc_std(void) {
  size_t alloc_len = 100;
  char* ptr = (char*) calloc(1, alloc_len);
  assert (ptr != NULL);
  for (size_t i = 0; i < alloc_len; i++) {
    assert (ptr[i] == 0);
  }
  ptr[99] = 1;
  free(ptr);
}

//calloc_mem_init_disabled

void calloc_illegal(void) {
  assert (calloc(-1, 100) == NULL);
  //errno
}

void calloc_overflow(void) {
  assert (calloc(1, SIZE_MAX) == NULL);
  //errno
  assert (calloc(SIZE_MAX, SIZE_MAX) == NULL);
  //errno
  assert (calloc(2, SIZE_MAX) == NULL);
  //errno
  assert (calloc(SIZE_MAX, 2) == NULL);
  //errno
}

//memalign_multiple
//memalign_overflow
//memalign_non_power2
//memalign_realloc

void malloc_realloc_larger(void) {
  char* ptr = (char*) malloc(100);
  assert (ptr != NULL);
  ptr[99] = 1;
  memset(ptr, 67, 100);
  ptr = (char*) realloc(ptr, 200);
  assert (ptr != NULL);
  for (size_t i = 0; i < 100; i++) {
    assert (ptr[i] == 67);
  }
  free(ptr);
}

void malloc_realloc_smaller(void) {
  char* ptr = (char*) malloc(200);
  assert (ptr != NULL);
  ptr[199] = 1;
  memset(ptr, 67, 200);
  ptr = (char*) realloc(ptr, 100);
  assert (ptr != NULL);
  for (size_t i = 0; i < 100; i++) {
    assert (ptr[i] == 67);
  }
  free(ptr);
}

void malloc_multiple_realloc(void) {
  char* ptr = (char*) malloc(200);
  assert (ptr != NULL);
  ptr[199] = 1;
  memset(ptr, 0x23, 200);
  ptr = (char*) realloc(ptr, 100);
  assert (ptr != NULL);
  for (size_t i = 0; i < 100; i++) {
    assert (ptr[i] == 0x23);
  }
  //ptr[99] = 1;
  ptr = (char*) realloc(ptr, 50);
  assert (ptr != NULL);
  for (size_t i = 0; i < 50; i++) {
    assert (ptr[i] == 0x23);
  }
  //ptr[49] = 1;
  ptr = (char*) realloc(ptr, 150);
  assert (ptr != NULL);
  for (size_t i = 0; i < 50; i++) {
    assert (ptr[i] == 0x23);
  }
  memset(ptr, 0x23, 150);
  //ptr[149] = 1;
  ptr = (char*) realloc(ptr, 425);
  assert (ptr != NULL);
  for (size_t i = 0; i < 150; i++) {
    assert (ptr[i] == 0x23);
  }
  //ptr[424] = 1;
  free(ptr);
}

void calloc_realloc_larger(void) {
  char* ptr = (char*) calloc(1, 100);
  assert (ptr != NULL);
  //ptr[99] = 1;
  ptr = (char*) realloc(ptr, 200);
  assert (ptr != NULL);
  for (size_t i = 0; i < 100; i++) {
    assert (ptr[i] == 0);
  }
  free(ptr);
}

void calloc_realloc_smaller(void) {
  char* ptr = (char*) calloc(1, 200);
  assert (ptr != NULL);
  //ptr[199] = 1;
  ptr = (char*) realloc(ptr, 100);
  assert (ptr != NULL);
  for (size_t i = 0; i < 100; i++) {
    assert (ptr[i] == 0);
  }
  free(ptr);
}

void calloc_multiple_realloc(void) {
  char* ptr = (char*) calloc(1, 200);
  assert (ptr != NULL);
  //ptr[199] = 1;
  ptr = (char*) realloc(ptr, 100);
  assert (ptr != NULL);
  for (size_t i = 0; i < 100; i++) {
    assert (ptr[i] == 0);
  }
  //ptr[99] = 1;
  ptr = (char*) realloc(ptr, 50);
  assert (ptr != NULL);
  for (size_t i = 0; i < 50; i++) {
    assert (ptr[i] == 0);
  }
  //ptr[49] = 1;
  ptr = (char*) realloc(ptr, 150);
  assert (ptr != NULL);
  for (size_t i = 0; i < 50; i++) {
    assert (ptr[i] == 0);
  }
  memset(ptr, 0, 150);
  //ptr[149] = 1;
  ptr = (char*) realloc(ptr, 425);
  assert (ptr != NULL);
  for (size_t i = 0; i < 150; i++) {
    assert (ptr[i] == 0);
  }
  //ptr[424] = 1;
  free(ptr);
}

void realloc_overflow(void) {
  assert(realloc(NULL, SIZE_MAX) == NULL);
  //errno
  void* ptr = malloc(100);
  assert (ptr != NULL);
  assert (realloc(ptr, SIZE_MAX) == NULL);
  //errno
  free(ptr);
}

//pvalloc_std
//pvalloc_overflow
//valloc_std
//valloc_overflow
//malloc_info
//malloc_info_matches_mallinfo
//calloc_usable_size

void malloc_0(void) {
  void* ptr = malloc(0);
  assert (ptr != NULL);
  free(ptr);
}

void calloc_0_0(void) {
  void* ptr = calloc(0, 0);
  assert (ptr != NULL);
  free(ptr);
}

void calloc_0_1(void) {
  void* ptr = calloc(0, 1);
  assert (ptr != NULL);
  free(ptr);
}

void calloc_1_0(void) {
  void* ptr = calloc(1, 0);
  assert (ptr != NULL);
  free(ptr);
}

void realloc_nullptr_0(void) {
  //malloc(ptr, 0)
  void* ptr = realloc(NULL, 0);
  assert (ptr != NULL);
  free(ptr);
}

void realloc_0(void) {
  void* ptr = malloc(1024);
  assert (ptr != NULL);
  //free(ptr)
  void* ptr2 = realloc(ptr, 0);
  assert (ptr2 == NULL);
}

//TODO? verify_alignment
//mallopt_smoke
//mallopt_decay
//mallopt_purge
//mallopt_scudo_only_options
//reallocarray_overflow
//reallocarray
//mallinfo
//mallinfo2
//TODO? alloc_after_fork
//error_on_unexpected_option
//init_zygote_child_profiling
//set_allocation_limit
//set_allocation_limit_multiple
//set_allocation_limit_realloc_increase
//set_allocation_limit_realloc_decrease
//set_allocation_limit_realloc_free
//set_allocation_limit_multiple_threads
//multiple_enable_gwp_asan
//memtag_stack_is_on
//zero_init
//disable_mte
//allocation_slack
//realloc_mte_crash
//TODO: zeroed_allocations_small_medium_sizes
//TODO: zeroed_allocations_large_sizes
//TODO: zeroed_allocations_realloc

int main() {
  //malloc_std();
  //malloc_overflow();
  calloc_std();
  //calloc_illegal();
  //calloc_overflow();
  //malloc_realloc_larger();
  //malloc_realloc_smaller();
  //malloc_multiple_realloc();
  //calloc_realloc_larger();
  //calloc_realloc_smaller();
  //calloc_multiple_realloc();
  //realloc_overflow();
  //malloc_0();
  //calloc_0_0();
  //calloc_0_1();
  //calloc_1_0();
  //realloc_nullptr_0();
  //realloc_0();
  return 0;
}
