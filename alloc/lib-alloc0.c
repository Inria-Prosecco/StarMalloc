#include "Main.h"
#include <stdint.h>

uint64_t* metadata = NULL;
Impl_Core_node__Aux_a* metadata_ptr = NULL;
uint64_t size_metadata = 0UL;
uint64_t status = 0UL;

void malloc_init() {
  metadata = (uint64_t*) Main_mmap(1048576, 3l);
  metadata_ptr = Main_create_leaf();
  status = 1;
}

uint64_t* Aux_trees_malloc(uint64_t v) {
  if (! status) malloc_init ();
  uint64_t* ptr = &metadata[size_metadata];
  *ptr = v;
  size_metadata += sizeof(uint64_t);
  return ptr;
}

Impl_Core_node__Aux_a* Aux_trees_malloc2(Impl_Core_node__Aux_a n) {
  if (! status) malloc_init ();
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
