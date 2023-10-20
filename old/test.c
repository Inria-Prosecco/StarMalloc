#include "Impl_Test.c"
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
  int64_t* random_data = malloc(x * sizeof(int64_t));
  arc4random_buf(random_data, x * sizeof(int64_t));
  void* ptr = NULL;
  int64_t rd = 0;
  Impl_Test_a v = { .fst = (uint32_t)0U, .snd = (uint32_t)0U };
  uint64_t s = 0;
  //puts("AVL implementation test.");
  //puts("The supplied number of random values");
  //puts("will be inserted into an empty tree,");
  //puts("the presence of these values will be");
  //puts("checked, then these values will be");
  //puts("removed from the tree.");

  for (size_t i = 0; i < x; i++) {
    //rd = random_data[i];
    rd += i + 2;
    v = (Impl_Test_a) { .fst = rd, .snd = (uint32_t)0U };
    //printf("rd=%li\n", rd);
    ptr = Impl_Test_insert_avl(true, Impl_Test_compare, ptr, v);
  }
  s = Impl_Test_sot_wds(ptr);
  //puts("Should be equal to the supplied argument.");
  //printf("s=%lui\n", s);
  printf("%lui\n", s);

  bool b = false;
  rd = 0;
  for (size_t i = 0; i < x; i++) {
    rd += i + 2;
    v = (Impl_Test_a) { .fst = rd, .snd = (uint32_t)0U };
    b = Impl_Test_member(Impl_Test_compare, ptr, v);
    if (! b) {
      puts("Error: some element was not properly inserted.");
      return 1;
    }
  }

  rd = 0;
  for (size_t i = 0; i < x; i++) {
    rd += i + 2;
    v = (Impl_Test_a) { .fst = rd, .snd = (uint32_t)0U };
    ptr = Impl_Test_delete_avl(Impl_Test_compare, ptr, v);
  }
  puts("Should be equal to zero.");
  s = Impl_Test_sot_wds(ptr);
  printf("s=%lui\n", s);

  //uint64_t s1 = 0;
  //uint64_t s2 = 0;
  //uint64_t r1 = 0;
  //uint64_t r2 = 0;
  //void* ptr = NULL;
  //ptr = Impl_Test_main5(x);
  //s1 = Impl_Test_sot_wds(ptr);
  //printf("s1=%lui\n", s1);
  //r1 = Impl_Test_main6_aux(ptr, x, true);
  //printf("r1=%lui\n", r1);
  //ptr = Impl_Test_main7_aux (ptr, x);
  //s2 = Impl_Test_sot_wds(ptr);
  //printf("s2=%lui\n", s2);
  //r2 = Impl_Test_main6_aux(ptr, x, false);
  //printf("r2=%lui\n", r2);
  return 0;
}
