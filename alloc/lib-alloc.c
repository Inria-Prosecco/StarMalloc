#ifndef __LIB_ALLOC_C
#define __LIB_ALLOC_C

#include "Main.h"
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

uint64_t* metadata = NULL;
Impl_Core_node__Aux_a* Main_metadata_ptr = NULL;
uint64_t size_metadata = 0;
uint64_t status = 0;

void malloc_init() {
  //metadata = (void*) Main_malloc(1048576, 3l);
  status = 1;
}

uint64_t* Aux_trees_malloc(uint64_t v) {
  uint64_t* ptr = (uint64_t*) metadata[size_metadata];
  *ptr = v;
  size_metadata += sizeof(uint64_t);
  return ptr;
}

Impl_Core_node__Aux_a
*Aux_trees_malloc2(Impl_Core_node__Aux_a n) {
  Impl_Core_node__Aux_a * ptr = (Impl_Core_node__Aux_a*) metadata[size_metadata];
  *ptr = n;
  size_metadata += sizeof(Impl_Core_node__Aux_a);
  return ptr;
}



// WARNING:
// calling stdlib malloc before or inside the definition
// of this function, that is the only malloc version to be used
// will result in segfaults
// TODO:
// expose option to force reservation of the allocated memory
// htop: VIRT \neq RES

void* malloc (size_t size) {
  if (status == 0) malloc_init ();

  //volatile
  //K____Impl_Core_node__Aux_a__uint64_t
  //K____Impl_Core_node__Aux_a__uint64_t r = Main_malloc2(metadata, size, 3l);

  //Impl_Core_node__Aux_a* ptr = fst___Impl_Core_node_uint64_t___uint32_t__uint64_t(r);

  K____Impl_Core_node__Aux_a__uint64_t ptr = (K____Impl_Core_node__Aux_a__uint64_t) Main_malloc(Main_metadata_ptr, size);

//snd___Impl_Core_node_uint64_t___uint32_t__uint64_t
//
  void* ptr_snd = (void*) ptr.snd;
  *ptr_snd;
  return ptr_snd;
}

uint64_t free_count = 0;
void free (void* ptr) {
  free_count++;
  //if (f_cnt % 2 == 0)
  //  puts("a");
  //else
  //  puts("b");
}

// required for realloc
// this small implementation is likely not very robust
void* memcpy2 (void* dst, const void* src, long unsigned int cnt) {
  char* dst2 = (char*) dst;
  char* src2 = (char*) src;
  while (cnt) {
    *(dst2++) = *(src2++);
    cnt--;
  }
}

// TODO: does not enforce zeroing
void* calloc(long unsigned int nb_elem, long unsigned int size_elem) {
  long unsigned int size = nb_elem * size_elem;
  void* ptr = malloc(size);
  return ptr;
}

void* realloc(void* ptr, size_t size) {
  // why the spec would allow this, seriously...
  if (ptr == NULL) {
    return malloc(size);
  }
  void* ptr2 = (void*) malloc (size);
  memcpy2(ptr2, ptr, size);
  free(ptr);
  return ptr2;
}
//
//- bench les arbres avec alloc custom
//- variable globale côté Steel
#endif
