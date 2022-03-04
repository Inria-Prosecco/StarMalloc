#include "P1_UInt32.c"
#include <stdlib.h>
#include <stdbool.h>

int main(int argc, char** argv) {
  if (argc == 1) {
    puts("Please supply an argument.");
    return 1;
  }
  if (argc > 2) {
    puts("Please supply less arguments.");
    return 2;
  }
  //printf("%s\n", argv[0]);
  uint64_t x = strtoull(argv[1], NULL, 0);
  uint64_t* random_data = malloc(x * sizeof(uint64_t));
  arc4random_buf(random_data, x * sizeof(uint64_t));
  void* ptr = NULL;
  uint64_t rd = 0;
  uint64_t s = 0;
  puts("AVL implementation test.");
  puts("The supplied number of random values");
  puts("will be inserted into an empty tree,");
  puts("the presence of these values will be");
  puts("checked, then these values will be");
  puts("removed from the tree.");

  for (size_t i = 0; i < x; i++) {
    rd = random_data[i];
    //printf("rd=%lui\n", rd);
    ptr = P1_UInt32_insert_avl(true, P1_UInt32_compare, ptr, rd);
  }
  s = P1_UInt32_sot_wds(ptr);
  puts("Should be equal to the supplied argument.");
  printf("s=%lui\n", s);

  //bool b = false;
  //for (size_t i = 0; i < x; i++) {
  //  rd = random_data[i];
  //  b = P1_UInt32_member(P1_UInt32_compare, ptr, rd);
  //  if (! b) {
  //    puts("Error: some element was not properly inserted.");
  //    return 1;
  //  }
  //}

  //for (size_t i = 0; i < x; i++) {
  //  rd = random_data[i];
  //  ptr = P1_UInt32_delete_avl(P1_UInt32_compare, ptr, rd);
  //}
  //puts("Should be equal to zero.");
  //s = P1_UInt32_sot_wds(ptr);
  //printf("s=%lui\n", s);

  //uint64_t s1 = 0;
  //uint64_t s2 = 0;
  //uint64_t r1 = 0;
  //uint64_t r2 = 0;
  //void* ptr = NULL;
  //ptr = P1_UInt32_main5(x);
  //s1 = P1_UInt32_sot_wds(ptr);
  //printf("s1=%lui\n", s1);
  //r1 = P1_UInt32_main6_aux(ptr, x, true);
  //printf("r1=%lui\n", r1);
  //ptr = P1_UInt32_main7_aux (ptr, x);
  //s2 = P1_UInt32_sot_wds(ptr);
  //printf("s2=%lui\n", s2);
  //r2 = P1_UInt32_main6_aux(ptr, x, false);
  //printf("r2=%lui\n", r2);
  return 0;
}
