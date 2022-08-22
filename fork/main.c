#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
//#include <sys/types.h>
#include <unistd.h>
#include <stdatomic.h>

#define LOCAL 1
#if LOCAL
#define LOCAL_ATTR _Thread_local
#else
#define LOCAL_ATTR
#endif

static const unsigned n_arena = 16;

static LOCAL_ATTR unsigned thread_arena = n_arena;
static LOCAL_ATTR unsigned is_init = 0;
static atomic_uint thread_arena_counter = 0;

static inline unsigned init(void) {
  unsigned arena = thread_arena;
  thread_arena = arena = thread_arena_counter++ % n_arena;
  is_init = 1;
  return arena;
}

static unsigned alloc() {
  if (! is_init) init();
  return thread_arena;
}

static const int m = 10;

void* test1(void* _) {
  for (int n = 0; n < m; n++) {
    unsigned id = alloc();
    printf("t1: %i\n", id);
  }
}
void* test2(void* _) {
  for (int n = 0; n < m; n++) {
    unsigned id = alloc();
    printf("t2: %i\n", id);
  }
}
void* test3(void* _) {
  for (int n = 0; n < m; n++) {
    unsigned id = alloc();
    printf("t3: %i\n", id);
  }
}

pthread_t t1, t2, t3;
int main(){
  free(NULL);
  //fork();
  //printf("This is a test.\n");
  pthread_create(&t1, NULL, test1, NULL);
  pthread_create(&t2, NULL, test2, NULL);
  pthread_create(&t3, NULL, test3, NULL);
  pthread_join(t1, NULL);
  pthread_join(t2, NULL);
  pthread_join(t3, NULL);
  return 0;
}
