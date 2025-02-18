#include <stdlib.h>

int main(int argc){
  void* ptr = NULL;
  for (int i = 0; i < 10; i++) {
    ptr = malloc(128);
    free(ptr);
  }
  return 0;
}

