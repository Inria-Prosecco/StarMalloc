#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

int main(){
  uint8_t* ptr = NULL;
  ptr = malloc(100);
  ptr[1] = 1ul;
  ptr[4096] = 1ul;
  free(ptr);
  return 0;
}
