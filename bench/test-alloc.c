#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

int main(){
  uint32_t* ptr = NULL;
  for (uint32_t i = 0; i < 1024ul; i++) {
    ptr = malloc(1048576);
    ptr[1] = 1ul;
    ptr = realloc(ptr, 1048577);
    free(ptr);
  }
  printf("OK.\n");
  return 0;
}
