#include <stdint.h>
#include <stddef.h>
#include "krmlinit.h"
#include "StarMalloc.h"

void krmlinit_globals(void);

static uint32_t init_status = 0UL;

void* malloc(size_t size) {
  if (!init_status) { krmlinit_globals(); init_status=1UL; }
  return StarMalloc_malloc(size);
}

// krmllib name conflict: cannot call function "free"
void* _free(void* ptr) {
  bool r = StarMalloc_free(ptr);
  return;
}

int main(){
  uint8_t* ptr = NULL;
  uint32_t bound = 256ul;
  for (uint32_t i = 0; i < 256; ++i) {
    ptr = malloc(12);
    ptr[1] = 1;
    _free(ptr);
    ptr = malloc(37);
    ptr[1] = 1;
    _free(ptr);
    ptr = malloc(29);
    ptr[1] = 1;
    _free(ptr);
    ptr = malloc(4096*17+1);
    ptr[1] = 1;
    _free(ptr);
  }
  return 0;
}
