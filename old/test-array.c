#include "ArrayTest.c"
#include <stdlib.h>
#include <stdbool.h>

int main(int argc, char** argv) {
  uint32_t x1 = 0;
  uint32_t x2 = 7;
  uint32_t n = 42;
  uint32_t r = ArrayTest_temp(x1, x2, n);

  printf("%lui\n", r);
  return 0;
}
