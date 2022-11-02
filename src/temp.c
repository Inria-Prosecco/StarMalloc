#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

int main(){
  //uint32_t test[1024ul];
  uint32_t* test = malloc(10485760000ul);
  for (uint32_t i = 0; i < 65536ul; i++) {
    test[i*65536+1] = 1ul;
  }
  while (1) {
    //printf("This a test\n");
  }
  return  0;
}
