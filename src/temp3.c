#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

int main(){
  volatile char* ptr = NULL;
  size_t len = 1048576*1024;
  ptr = mmap(NULL, len, PROT_READ|PROT_WRITE, MAP_ANON|MAP_SHARED, -1, 0);
  volatile char* ptr2;
  int32_t i = 0;
  for (ptr2 = ptr; ptr2 < ptr + len; ptr2 += 4096) {
    //ptr = mmap(NULL, 1048576, PROT_READ|PROT_WRITE, MAP_ANON|MAP_SHARED, -1, 0);
    //ptr = malloc(1048576);
    ptr2[7ul] = i;
    *ptr2;
    i++;
  }
  for (uint32_t j = 0; j < 131072; j++) {
    ptr = mmap(NULL, 1048576, PROT_READ|PROT_WRITE, MAP_ANON|MAP_PRIVATE, -1, 0);
    *ptr;
  }
  printf("Done: %i.\n", i);
  while (1) {};
  return  0;
}
