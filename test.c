#include "P1_UInt32.c"

int main(int argc, char** argv) {
  if (argc == 1) {
    puts("Please supply an argument.");
    return 1;
  }
  if (argc > 2) {
    puts("Please supply less arguments.");
    return 2;
  }
  printf("%s\n", argv[0]);
  //uint32_t p = P1_UInt32_main ();
  //printf("r=%ui\n", p);
  //uint64_t h = P1_UInt32_main2 ();
  //printf("h=%lui\n", h);
  //uint64_t s = P1_UInt32_main3 ();
  //printf("s=%lui\n", s);
  //uint64_t r = P1_UInt32_main4 ();
  //printf("r=%lui\n", r);
  uint64_t x = strtoull(argv[1], NULL, 0);
  uint64_t s1 = 0;
  uint64_t s2 = 0;
  uint64_t r1 = 0;
  uint64_t r2 = 0;
  void* ptr = NULL;
  ptr = P1_UInt32_main5(x);
  s1 = P1_UInt32_sot_wds(ptr);
  printf("s1=%lui\n", s1);
  r1 = P1_UInt32_main6_aux(ptr, x, true);
  printf("r1=%lui\n", r1);
  ptr = P1_UInt32_main7_aux (ptr, x);
  s2 = P1_UInt32_sot_wds(ptr);
  printf("s2=%lui\n", s2);
  r2 = P1_UInt32_main6_aux(ptr, x, false);
  printf("r2=%lui\n", r2);
  return 0;
}
