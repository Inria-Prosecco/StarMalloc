#include <stdint.h>
#include "config.h"
#include "SizeClass.h"
#include "SmallAlloc.h"
#include "Slabs.h"
#include "LargeAlloc.h"
//#include <pthread.h>

static uint8_t* region_start = NULL;
static uint64_t* md_bm_region_start = NULL;
static Selectors_LList_cell__Slabs_blob* md_region_start = NULL;
static size_t md_count = 0UL;


//static pthread_mutex_t init_mutex = PTHREAD_MUTEX_INITIALIZER;
//static pthread_mutex_t s_mutex = PTHREAD_MUTEX_INITIALIZER;
//static LOCAL_ATTR uint64_t init_status = 0UL;
static uint64_t init_status = 0UL;

const size_t page_size = 4096UL;
const size_t max_slabs = 1024UL;
const size_t region_size = page_size * max_slabs;

static Selectors_LList_cell__Slabs_blob** partial_slabs_ptr;
static Selectors_LList_cell__Slabs_blob** empty_slabs_ptr;
static Selectors_LList_cell__Slabs_blob* partial_slabs;
static Selectors_LList_cell__Slabs_blob* empty_slabs;


static SizeClass_size_class_struct scs_v = {
  .size = (uint32_t)16U,
  .partial_slabs = &partial_slabs,
  .empty_slabs = &empty_slabs,
  .metadata_allocated = (uint32_t)0U
};
static SizeClass_size_class_struct* scs = &scs_v;

void init() {
  //pthread_mutex_lock(&init_mutex);
  if (! init_status) {
    region_start = LargeAlloc_mmap(max_slabs * page_size, 3l);
    md_bm_region_start = LargeAlloc_mmap(max_slabs * sizeof(uint64_t[4]), 3l);
    md_region_start = LargeAlloc_mmap(max_slabs * sizeof(Slabs_blob), 3l);
    //scs.partial_slabs = &partial_slabs;
    //scs.empty_slabs = &empty_slabs;
    init_status = 1UL;
  }
  //pthread_mutex_unlock(&init_mutex);
}

Selectors_LList_cell__Slabs_blob* Slabs_alloc_metadata(uint32_t sc) {
  size_t slab_offset = md_count * page_size;
  size_t bitmap_offset = md_count * sizeof(uint64_t[4]);
  uint8_t* slab = region_start + slab_offset;
  uint64_t* bitmap = md_bm_region_start + bitmap_offset;
  Selectors_LList_cell__Slabs_blob* md = md_region_start + md_count;
  md->data.fst = bitmap;
  md->data.snd = slab;
  //slab[2] = 1;
  md_count += 1;
  //Slabs_blob b = { .fst = &(md->data).fst, .snd = slab};
  //Selectors_LList_cell__Slabs_blob mdv = { .next = NULL, .data = b};
  //*md = mdv;
  return md;
}

void slab_lock() {
  if (! init_status) init();
  //pthread_mutex_lock(&s_mutex);
}

void slab_unlock() {
  //pthread_mutex_unlock(&s_mutex);
}

void* slab_malloc (size_t size) {
  slab_lock();
  //uint8_t* r = SmallAlloc_small_alloc(16ul, partial_slabs_ptr, empty_slabs_ptr);
  uint8_t* r = SizeClass_allocate_size_class(scs);
  //r[2] = 1;
  //uint64_t x = 18 / 0;
  slab_unlock();
  return r;
}
