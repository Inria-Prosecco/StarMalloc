#include <stddef.h>
#include <stdint.h>
//#include <stdio.h>
//
#include "Slabs.h"

uint32_t Utils2_ffs64(uint64_t x) {
  return __builtin_ffsll(~x);
}


Selectors_LList_cell__Slabs_blob
*Slabs_singleton_array_to_ref(Selectors_LList_cell__Slabs_blob *arr) {
  return arr;
}



//int main(){
//  uint64_t v;
//  v = 1UL;
//  v = 4UL;
//  //v = 2UL;
//  uint32_t r = ffs64(v);
//  printf("%lu", r);
//  return 0;
//}
