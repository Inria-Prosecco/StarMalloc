#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

int main(){
  uint32_t* ptr = NULL;
  for (uint32_t i = 0; i < 1024ul; i++) {
    ptr = malloc(1048576);
    ptr[1] = 1ul;
  }
  printf("Done.\n");
  while (1) {}
  return  0;
}
