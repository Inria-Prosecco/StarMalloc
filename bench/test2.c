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
  uint64_t n = strtoull(argv[1], NULL, 0);
  printf("s=%lu\n", n);
  //uint64_t* random_data = malloc(n * sizeof(int64_t));
  //arc4random_buf(random_data, n * sizeof(int64_t));
  uint32_t x = 7;
  uint32_t a = 1997;
  uint32_t a2 = 13;
  Aux_a v = { .fst = 0UL, .snd = 0UL };
  //Impl_Core_node__Aux_a* ptr = Impl_Test_Mono_create_tree(v);
  Impl_Core_node__Aux_a* ptr = Impl_Test_Mono_create_leaf ();
  uint64_t rd = 0;
  uint64_t s = 0;
  for (size_t i = 0; i < n; i++) {
    //rd = random_data[i];
    //x = a * x + a2;
    x = i;
    rd = x;
    v = (Impl_Test_Mono_a) {.fst = rd, .snd = 0UL};
    //printf("rd=%lui\n", rd);
    ptr = Impl_Test_Mono_insert_avl(true, Impl_Test_Mono_compare, ptr, v);
  }
  s = Impl_Test_Mono_sot_wds(ptr);
  puts("Should be equal to the supplied argument.");
  printf("s=%lu\n", s);

  bool b = false;

  x = 7;
  for (size_t i = 0; i < n; i++) {
    //rd = random_data[i];
    //x = a * x + a2;
    x = i;
    rd = x;
    v = (Impl_Test_Mono_a) {.fst = rd, .snd = 0UL};
    b = Impl_Test_Mono_member(Impl_Test_Mono_compare, ptr, v);
    if (! b) {
      puts("Error: some element was not properly inserted.");
      return 1;
    }
  }

  x = 7;
  for (size_t i = 0; i < n; i++) {
    //rd = random_data[i];
    //x = a * x + a2;
    x = i;
    rd = x;
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
