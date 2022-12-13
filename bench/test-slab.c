#include <stdint.h>
#include <stddef.h>

void* slab_malloc(size_t size);

int main(){
  uint8_t* ptr = NULL;
  uint32_t bound = 256ul;
  uint32_t size_class = 64ul;
  for (uint32_t i = 0; i < 256; ++i) {
    ptr = slab_malloc(size_class);
    ptr[1] = 1;
  }
  return 0;
}
