#include <stdint.h>
#include "config.h"
#include "SizeClass.h"
#include "SmallAlloc.h"
#include "Slabs.h"
#include "LargeAlloc.h"
//#include <pthread.h>

//static uint8_t* region_start = NULL;
//static uint64_t* md_bm_region_start = NULL;
//static Selectors_LList_cell__Slabs_blob* md_region_start = NULL;

//static pthread_mutex_t init_mutex = PTHREAD_MUTEX_INITIALIZER;
//static pthread_mutex_t s_mutex = PTHREAD_MUTEX_INITIALIZER;
//static LOCAL_ATTR uint64_t init_status = 0UL;
static uint64_t init_status = 0UL;

const size_t page_size = 4096UL;
const size_t max_slabs = 1024UL;

//static Selectors_LList_cell__Slabs_blob** partial_slabs_ptr;
//static Selectors_LList_cell__Slabs_blob** empty_slabs_ptr;
static Selectors_LList_cell__Slabs_blob* partial_slabs_sc16;
static Selectors_LList_cell__Slabs_blob* partial_slabs_sc32;
static Selectors_LList_cell__Slabs_blob* partial_slabs_sc64;
static Selectors_LList_cell__Slabs_blob* empty_slabs_sc16;
static Selectors_LList_cell__Slabs_blob* empty_slabs_sc32;
static Selectors_LList_cell__Slabs_blob* empty_slabs_sc64;
static uint32_t* md_count_sc16;
static uint32_t* md_count_sc32;
static uint32_t* md_count_sc64;

static SizeClass_size_class_struct scs16_v = {
  .size = (uint32_t)16U,
  .partial_slabs = &partial_slabs_sc16,
  .empty_slabs = &empty_slabs_sc16,
  .md_count = &md_count_sc16,
  .slab_region = NULL,
  .md_bm_region = NULL,
  .md_region = NULL,
};
static SizeClass_size_class_struct scs32_v = {
  .size = (uint32_t)32U,
  .partial_slabs = &partial_slabs_sc32,
  .empty_slabs = &empty_slabs_sc32,
  .md_count = &md_count_sc32,
  .slab_region = NULL,
  .md_bm_region = NULL,
  .md_region = NULL,
};
static SizeClass_size_class_struct scs64_v = {
  .size = (uint32_t)64U,
  .partial_slabs = &partial_slabs_sc64,
  .empty_slabs = &empty_slabs_sc64,
  .md_count = &md_count_sc64,
  .slab_region = NULL,
  .md_bm_region = NULL,
  .md_region = NULL,
};

static SizeClass_size_class_struct* scs16 = &scs16_v;
static SizeClass_size_class_struct* scs32 = &scs32_v;
static SizeClass_size_class_struct* scs64 = &scs64_v;

void init() {
  //pthread_mutex_lock(&init_mutex);
  if (! init_status) {
    scs16->slab_region = (uint8_t*) LargeAlloc_mmap(max_slabs * page_size, 3l);
    scs16->md_bm_region = (uint64_t*) LargeAlloc_mmap(max_slabs * sizeof(uint64_t[4]), 3l);
    scs16->md_region = (Selectors_LList_cell__Slabs_blob*) LargeAlloc_mmap(max_slabs * sizeof(Selectors_LList_cell__Slabs_blob), 3l);
    scs32->slab_region = (uint8_t*) LargeAlloc_mmap(max_slabs * page_size, 3l);
    scs32->md_bm_region = (uint64_t*) LargeAlloc_mmap(max_slabs * sizeof(uint64_t[4]), 3l);
    scs32->md_region = (Selectors_LList_cell__Slabs_blob*) LargeAlloc_mmap(max_slabs * sizeof(Selectors_LList_cell__Slabs_blob), 3l);
    scs64->slab_region = (uint8_t*) LargeAlloc_mmap(max_slabs * page_size, 3l);
    scs64->md_bm_region = (uint64_t*) LargeAlloc_mmap(max_slabs * sizeof(uint64_t[4]), 3l);
    scs64->md_region = (Selectors_LList_cell__Slabs_blob*) LargeAlloc_mmap(max_slabs * sizeof(Selectors_LList_cell__Slabs_blob), 3l);
    init_status = 1UL;
  }
  //pthread_mutex_unlock(&init_mutex);
}

Selectors_LList_cell__Slabs_blob*
Slabs_alloc_metadata(
  uint32_t sc,
  uint8_t* slab_region,
  uint64_t* md_bm_region,
  Selectors_LList_cell__Slabs_blob* md_region,
  uint32_t* md_count
) {
  size_t slab_offset = ((size_t) *md_count) * page_size;
  size_t bitmap_offset = ((size_t) *md_count) * sizeof(uint64_t[4]);
  size_t md_offset = ((size_t) *md_count) * sizeof(Selectors_LList_cell__Slabs_blob);
  uint8_t* slab = slab_region + slab_offset;
  uint64_t* bitmap = md_bm_region + bitmap_offset;
  Selectors_LList_cell__Slabs_blob* md = md_region + md_offset;

  //Slabs_blob b = { .fst = bitmap, .snd = slab};
  //Selectors_LList_cell__Slabs_blob md_v = { .next = NULL, .data = b};
  //*md = md_v;
  md->data.fst = bitmap;
  md->data.snd = slab;
  //slab[2] = 1;
  *md_count += 1;
  //Slabs_blob b = { .fst = &(md->data).fst, .snd = slab};
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
  //slab_unlock();
  if (size <= 16UL) {
    uint8_t* r = SizeClass_allocate_size_class(scs16);
    return r;
  } else if (size <= 32UL) {
    uint8_t* r = SizeClass_allocate_size_class(scs32);
    return r;
  } else {
    uint8_t* r = SizeClass_allocate_size_class(scs64);
    return r;
  }
}
