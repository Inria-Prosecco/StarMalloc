#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdbool.h>

#define N_THREADS 64

pthread_mutex_t m;
pthread_t threads[N_THREADS];

uint64_t value = 0;
uint32_t* ptr = NULL;

void* impl1 (void* _) {
  //printf("OK\n");
  for (int n = 0; n < 100; n++) {
    pthread_mutex_lock(&m);
    value += 1;
    pthread_mutex_unlock(&m);
    //puts("Alloc 1/2\n");
    ptr = malloc(100);
    //puts("Alloc 2/2\n");
    ptr[1] = 1ul;
    //puts("Free 1/2\n");
    free(ptr);
    //puts("Free 2/2\n");
  }
}

int main(){
  pthread_mutex_init(&m, NULL);
  //printf("Test\n");
  //puts("Test\n");
  //pthread_create(&threads[0], NULL, impl1, NULL);
  //pthread_join(threads[0], NULL);
  for (int i = 0; i < N_THREADS; i++) {
    pthread_create(&threads[i], NULL, impl1, NULL);
  }
  for (int i = 0; i < N_THREADS; i++) {
    pthread_join(threads[i], NULL);
  }
  printf("%lui\n", value);
  pthread_mutex_destroy(&m);
  return 0;
}
