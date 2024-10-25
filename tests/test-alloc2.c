#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdbool.h>

#define N_THREADS 256
#define N_ALLOC 1000

pthread_mutex_t m;
pthread_t threads[N_THREADS];

uint64_t value = 0;

void* impl1 (void* _) {
  //printf("OK\n");
  uint32_t* ptr = NULL;
  for (int n = 0; n < N_ALLOC; n++) {
    pthread_mutex_lock(&m);
    value += 1;
    pthread_mutex_unlock(&m);
    ptr = malloc(100);
    ptr[1] = 1ul;
    ptr = realloc(ptr, 4097);
    free(ptr);
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
