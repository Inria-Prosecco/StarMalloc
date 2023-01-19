#include <stdint.h>
#include "config.h"
#include "SizeClass.h"
#include "SmallAlloc.h"
#include "Slabs.h"
#include "LargeAlloc.h"
#include "BlobList.h"
//#include <pthread.h>

//static uint8_t* region_start = NULL;
//static uint64_t* md_bm_region_start = NULL;
//static BlobList_cell* md_region_start = NULL;

//static pthread_mutex_t init_mutex = PTHREAD_MUTEX_INITIALIZER;
//static pthread_mutex_t s_mutex = PTHREAD_MUTEX_INITIALIZER;
//static LOCAL_ATTR uint64_t init_status = 0UL;
static uint64_t init_status = 0UL;

const size_t page_size = 4096UL;
const size_t max_slabs = 1024UL;

static BlobList_cell* full_slabs_sc16;
static BlobList_cell* full_slabs_sc32;
static BlobList_cell* full_slabs_sc64;
static BlobList_cell* partial_slabs_sc16;
static BlobList_cell* partial_slabs_sc32;
static BlobList_cell* partial_slabs_sc64;
static BlobList_cell* empty_slabs_sc16;
static BlobList_cell* empty_slabs_sc32;
static BlobList_cell* empty_slabs_sc64;
static uint32_t* md_count_sc16;
static uint32_t* md_count_sc32;
static uint32_t* md_count_sc64;

static SizeClass_size_class_struct scs16_v = {
  .size = (uint32_t)16U,
  .partial_slabs = &partial_slabs_sc16,
  .empty_slabs = &empty_slabs_sc16,
  .full_slabs = &full_slabs_sc16,
  .md_count = &md_count_sc16,
  .slab_region = NULL,
  .md_bm_region = NULL,
  .md_region = NULL,
};
static SizeClass_size_class_struct scs32_v = {
  .size = (uint32_t)32U,
  .partial_slabs = &partial_slabs_sc32,
  .empty_slabs = &empty_slabs_sc32,
  .full_slabs = &full_slabs_sc32,
  .md_count = &md_count_sc32,
  .slab_region = NULL,
  .md_bm_region = NULL,
  .md_region = NULL,
};
static SizeClass_size_class_struct scs64_v = {
  .size = (uint32_t)64U,
  .partial_slabs = &partial_slabs_sc64,
  .empty_slabs = &empty_slabs_sc64,
  .full_slabs = &full_slabs_sc64,
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
    scs16->md_region = (BlobList_cell*) LargeAlloc_mmap(max_slabs * sizeof(BlobList_cell), 3l);
    scs32->slab_region = (uint8_t*) LargeAlloc_mmap(max_slabs * page_size, 3l);
    scs32->md_bm_region = (uint64_t*) LargeAlloc_mmap(max_slabs * sizeof(uint64_t[4]), 3l);
    scs32->md_region = (BlobList_cell*) LargeAlloc_mmap(max_slabs * sizeof(BlobList_cell), 3l);
    scs64->slab_region = (uint8_t*) LargeAlloc_mmap(max_slabs * page_size, 3l);
    scs64->md_bm_region = (uint64_t*) LargeAlloc_mmap(max_slabs * sizeof(uint64_t[4]), 3l);
    scs64->md_region = (BlobList_cell*) LargeAlloc_mmap(max_slabs * sizeof(BlobList_cell), 3l);
    init_status = 1UL;
  }
  //pthread_mutex_unlock(&init_mutex);
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
