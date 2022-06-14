#include "Main.h"
#include <stdint.h>
#include <pthread.h>

const uint64_t uint64_size = sizeof(uint64_t);
const uint64_t metadata_node_size = sizeof(Impl_Core_node__Aux_a);
const uint64_t allocated_size = 1048576;

// whether initialization already occured
uint64_t status = 0UL;
// pointer to the currently progressively allocated metadata region
uint8_t* metadata = NULL;
// metadata size of the currently progressively allocated metadata region
uint64_t size_metadata = 0UL;

// root of the metadata tree
Impl_Core_node__Aux_a* metadata_ptr = NULL;

static pthread_mutex_t m;


void malloc_init() {
  metadata = (uint8_t*) Main_mmap(allocated_size, 3l);
  metadata_ptr = Main_create_leaf();
  pthread_mutex_init(&m, NULL);
  status = 1;
  puts("Init, mmap.");
}

void malloc_check() {
  if (! status) malloc_init ();
  if (size_metadata + uint64_size >= allocated_size ||
      size_metadata + metadata_node_size >= allocated_size) {
    puts("Mmap again.");
    metadata = Main_mmap(allocated_size, 3l);
    size_metadata = 0UL;
  }
}

void lock() {
  pthread_mutex_lock(&m);
}

void unlock() {
  pthread_mutex_unlock(&m);
}


uint64_t* Aux_trees_malloc(uint64_t v) {
  malloc_check();
  uint64_t* ptr = (uint64_t*) &metadata[size_metadata];
  *ptr = v;
  size_metadata += sizeof(uint64_t);
  return ptr;
}

Impl_Core_node__Aux_a* Aux_trees_malloc2(Impl_Core_node__Aux_a n) {
  malloc_check();
  Impl_Core_node__Aux_a* ptr = (Impl_Core_node__Aux_a*) &metadata[size_metadata];
  *ptr = n;
  size_metadata += sizeof(Impl_Core_node__Aux_a);
  return ptr;
}

Impl_Core_node__Aux_a* Main_get_metadata () {
  return metadata_ptr;
}

void Main_set_metadata(Impl_Core_node__Aux_a* metadata) {
  metadata_ptr = metadata;
}
