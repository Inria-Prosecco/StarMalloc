#include <stdint.h>
#include <stddef.h>
#include "../src/lib-alloc.c"

int main(){
  uint8_t* ptr = NULL;
  uint32_t bound = 256ul;
  for (uint32_t i = 0; i < 256; ++i) {
    ptr = malloc(12);
    ptr[1] = 1;
    free(ptr);
    ptr = malloc(37);
    ptr[1] = 1;
    free(ptr);
    ptr = malloc(29);
    ptr[1] = 1;
    free(ptr);
    ptr = malloc(4096*17+1);
    ptr[1] = 1;
    free(ptr);
  }
  return 0;
}
