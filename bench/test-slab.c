#include <stdint.h>
#include <stddef.h>

void* slab_malloc(size_t size);

int main(){
  uint8_t* ptr = NULL;
  uint32_t bound = 256ul;
  for (uint32_t i = 0; i < 256; ++i) {
    ptr = slab_malloc(12);
    ptr[1] = 1;
    ptr = slab_malloc(37);
    ptr[1] = 1;
    ptr = slab_malloc(29);
    ptr[1] = 1;
  }
  return 0;
}
