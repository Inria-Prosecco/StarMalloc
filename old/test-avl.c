#include <stdint.h>
#include <stddef.h>
#include "krmlinit.h"

uint8_t* large_malloc(uint64_t size);

void krmlinit_globals(void);

static uint32_t init_status = 0UL;

void* smalloc(size_t size) {
  if (!init_status) { krmlinit_globals(); init_status=1UL; }
  return large_malloc(size);
}

void* sfree(void* ptr) {
  bool r = large_free(ptr);
  return;
}

int main(){
  uint8_t* ptr = NULL;
  uint32_t bound = 256ul;
  for (uint32_t i = 0; i < 256; ++i) {
    ptr = smalloc(12);
    ptr[1] = 1;
    sfree(ptr);
    ptr = smalloc(37);
    ptr[1] = 1;
    sfree(ptr);
    ptr = smalloc(29);
    ptr[1] = 1;
    sfree(ptr);
  }
  return 0;
}
