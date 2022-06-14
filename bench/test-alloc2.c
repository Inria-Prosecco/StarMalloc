#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdbool.h>

pthread_mutex_t m;
pthread_t t1, t2, t3;

uint64_t value = 0;
uint32_t* ptr = NULL;

void* impl1 (void* _) {
  for (int n = 0; n < 100; n++) {
    pthread_mutex_lock(&m);
    value += 1;
    pthread_mutex_unlock(&m);
    ptr = malloc(100);
    ptr[1] = 1ul;
    free(ptr);
  }
}

int main(){
  pthread_mutex_init(&m, NULL);
  pthread_create(&t1, NULL, impl1, NULL);
  pthread_create(&t2, NULL, impl1, NULL);
  pthread_create(&t3, NULL, impl1, NULL);
  pthread_join(t1, NULL);
  pthread_join(t2, NULL);
  pthread_join(t3, NULL);
  printf("%lui\n", value);
  pthread_mutex_destroy(&m);
  return 0;
}
