#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

// https://github.com/microsoft/mimalloc/blob/master/test/test-api.c

// malloc

void malloc_zero(void) {
  void* ptr = malloc(0);
  assert (ptr != NULL);
  free(ptr);
}

void malloc_nomem1(void) {
  void* ptr = malloc((size_t) PTRDIFF_MAX + (size_t)1);
  assert (ptr == NULL);
  free(ptr);
}

void malloc_null(void) {
  free(NULL);
}

void calloc_overflow(void) {
  void* ptr = calloc(&calloc, SIZE_MAX/1000);
  assert (ptr == NULL);
}

void calloc0(void) {
  char* ptr = calloc(0, 1000);
  assert (ptr[15] == 0);
  free(ptr);
}

void malloc_large(void) {
  void* ptr = malloc(67108872);
  assert (ptr != NULL);
  free(ptr);
}

// extended

//posix_memalign1
//posix_memalign_no_align
//posix_memalign_zero
//posix_memalign_nopow2
//posix_memalign_nomem

// aligned API

//malloc_aligned1
//malloc_aligned2
//malloc_aligned3
//malloc_aligned4
//malloc_aligned5
//malloc_aligned6
//malloc_aligned7
//malloc_aligned8
//malloc_aligned9
//malloc_aligned10
//malloc_aligned11
//malloc_aligned_at1
//malloc_aligned_at2
//memalign1

// realloc

void realloc_null(void) {
  void* ptr = realloc(NULL, 4);
  assert (ptr != NULL);
  free(ptr);
}

void realloc_null_sizezero(void) {
  void* ptr = realloc(NULL, 0);
  assert (ptr != NULL);
  free(ptr);
}

void realloc_sizezero(void) {
  void* ptr = malloc(4);
  void* ptr2 = realloc(NULL, 0);
  assert (ptr != NULL);
  free(ptr2);
}

//reallocarray_null_sizezero

int main () {
  malloc_zero();
  malloc_nomem1();
  malloc_null();
  calloc_overflow();
  calloc0();
  malloc_large();
  realloc_null();
  realloc_null_sizezero();
  realloc_sizezero();
  return 0;
}
