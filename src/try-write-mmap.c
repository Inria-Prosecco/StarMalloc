#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

int main(){
  uint32_t* ptr = NULL;
  size_t len = 1048576*1024;
  ptr = mmap(NULL, len, PROT_READ|PROT_WRITE, MAP_ANON|MAP_SHARED, -1, 0);
  ptr[1ul] = 0ul;
  //munmap(ptr, len);
  printf("Done.\n");
  while (1) {}
  return 0;
}
