#include "Impl_Test_Mono.h"
#include <stdbool.h>
#include <stdio.h>
#include <stdint.h>

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
  uint64_t x = strtoull(argv[1], NULL, 0);
  uint64_t* random_data = malloc(x * sizeof(int64_t));
  arc4random_buf(random_data, x * sizeof(int64_t));
  Aux_a v = { .fst = 0UL, .snd = 0UL };
  //Impl_Core_node__Aux_a* ptr = Impl_Test_Mono_create_tree(v);
  Impl_Core_node__Aux_a* ptr = Impl_Test_Mono_create_leaf ();
  uint64_t rd = 0;
  uint64_t s = 0;
  for (size_t i = 0; i < x; i++) {
    rd = random_data[i];
    v = (Impl_Test_Mono_a) {.fst = rd, .snd = 0UL};
    //printf("rd=%lui\n", rd);
    ptr = Impl_Test_Mono_insert_avl(true, Impl_Test_Mono_compare, ptr, v);
  }
  s = Impl_Test_Mono_sot_wds(ptr);
  puts("Should be equal to the supplied argument.");
  printf("s=%lu\n", s);

  bool b = false;
  for (size_t i = 0; i < x; i++) {
    rd = random_data[i];
    v = (Impl_Test_Mono_a) {.fst = rd, .snd = 0UL};
    b = Impl_Test_Mono_member(Impl_Test_Mono_compare, ptr, v);
    if (! b) {
      puts("Error: some element was not properly inserted.");
      return 1;
    }
  }

  for (size_t i = 0; i < x; i++) {
    rd = random_data[i];
    v = (Impl_Test_Mono_a) {.fst = rd, .snd = 0UL};
    ptr = Impl_Test_Mono_delete_avl(Impl_Test_Mono_compare, ptr, v);
  }
  //v = (Impl_Test_Mono_a) { .fst = 0UL, .snd = 0UL };
  //ptr = Impl_Test_Mono_delete_avl(Impl_Test_Mono_compare, ptr, v);
  puts("Should be equal to zero.");
  s = Impl_Test_Mono_sot_wds(ptr);
  printf("s=%lu\n", s);

  return 0;
}
