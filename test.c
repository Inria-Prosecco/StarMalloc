#include "P1_UInt32.c"

int main() {
  uint32_t p = P1_UInt32_main ();
  printf("r=%ui\n", p);
  uint64_t h = P1_UInt32_main2 ();
  printf("h=%lui\n", h);
  uint64_t s = P1_UInt32_main3 ();
  printf("s=%lui\n", s);
  uint64_t r = P1_UInt32_main4 ();
  printf("r=%lui\n", r);
  return 0;
}
