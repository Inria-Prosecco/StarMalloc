#include "Main.h"
#include <stdbool.h>
#include <stdint.h>
//#include <stdio.h>

// WARNING:
// calling stdlib malloc before or inside the definition
// of this function, that is the only malloc version to be used
// will result in segfaults
// TODO:
// expose option to force reservation of the allocated memory
// htop: VIRT \neq RES

void* malloc (size_t size) {
  //if (status == 0) malloc_init ();
  //malloc_count += 1;

  //volatile
  //K____Impl_Core_node__Aux_a__uint64_t
  //K____Impl_Core_node__Aux_a__uint64_t r = Main_malloc2(metadata, size, 3l);

  //Impl_Core_node__Aux_a* ptr = fst___Impl_Core_node_uint64_t___uint32_t__uint64_t(r);

  //K____Impl_Core_node__Aux_a__uint64_t ptr = (K____Impl_Core_node__Aux_a__uint64_t) Main_malloc(Main_metadata_ptr, size);

//snd___Impl_Core_node_uint64_t___uint32_t__uint64_t
//
  //void* ptr_snd = (void*) ptr.snd;
  //*ptr_snd;
  //return NULL;
  void* ptr = (void*) Main_malloc(size);
  *ptr;
  //void* ptr = NULL;
  return ptr;
}

uint64_t free_count = 0;
void free (void* ptr) {
  free_count++;
  //if (f_cnt % 2 == 0)
  //  puts("a");
  //else
  //  puts("b");
}

uint64_t size () {
  return Main_size ();
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
  printf("src: %p\n", ptr);
  printf("dst: %p\n", ptr2);
  // size is incorrect here,
  // need to know size of the previous allocation,
  // otherwise a bus error can be raised
  memcpy2(ptr2, ptr, size);
  free(ptr);
  return ptr2;
}
//
//- bench les arbres avec alloc custom
//- variable globale côté Steel

//int main() {
//  int i = 2;
//  //puts("NIQUE\n");
//  uint64_t* ptr = malloc(1267);
//  printf("OK : %lui\n", malloc_count);
//  puts("Test");
//  printf("OK : %lui\n", malloc_count);
//  puts("Test2");
//  printf("OK : %lui\n", malloc_count);
//  ptr[0] = 2;
//  for (uint32_t i = 0; i < 1024ul; i++) {
//    ptr = malloc(1048576);
//    ptr[1] = 1ul;
//    ptr = realloc(ptr, 1048577);
//    free(ptr);
//  }
//  printf("OK : %lui\n", malloc_count);
//  return 0;
//}
