#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

int main(){
  uint32_t* ptr = NULL;
  //printf("OK.\n");
  for (uint32_t i = 0; i < 256ul; i++) {
    //ptr = malloc(1048576);
    ptr = malloc(100);
    ptr[1] = 1ul;
    //ptr = realloc(ptr, 1048577);
    free(ptr);
  }
  // only for static test
  //uint64_t s = 0UL;
  //s = _size ();
  //printf("Size: %lui\n", s);
  //s = _size ();
  //printf("Size: %lui\n", s);
  return 0;
}
