// SPDX-License-Identifier: Apache-2.0


#ifndef internal_StarMalloc_H
#define internal_StarMalloc_H

#include "krmllib.h"

#include "SizeClass.h"
#include "Mman.h"
#include "Constants.h"
#include "../StarMalloc.h"

extern uint32_t Impl_Trees_Cast_M_avl_data_size;

typedef struct K___Prims_dtuple2___uint8_t_____size_t_s
{
  uint8_t *fst;
  size_t snd;
}
K___Prims_dtuple2___uint8_t_____size_t;

typedef struct Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t_s
Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t;

typedef struct Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t_s
Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t;

typedef struct Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t_s
{
  K___Prims_dtuple2___uint8_t_____size_t data;
  Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t *left;
  Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t *right;
  uint64_t size;
  uint64_t height;
}
Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t;

extern Constants_sc_full_ Impl_Trees_Types_sc_avl;

typedef struct Impl_Trees_Types_mmap_md_slabs_s
{
  uint8_t *slab_region;
  SizeClass_size_class_struct_ scs;
  Steel_SpinLock_lock lock;
}
Impl_Trees_Types_mmap_md_slabs;

void Impl_Trees_Types_init_mmap_md_slabs(Impl_Trees_Types_mmap_md_slabs *ret);

extern Impl_Trees_Types_mmap_md_slabs Impl_Trees_Types_metadata_slabs;

bool
Impl_BST_M_member(
  Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t *ptr,
  K___Prims_dtuple2___uint8_t_____size_t v
);

Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t
*Impl_AVL_M_insert_avl(
  Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t
  *(*f1)(Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t x0),
  void (*f2)(Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t *x0),
  bool r,
  Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t *ptr,
  K___Prims_dtuple2___uint8_t_____size_t new_data
);

typedef struct Impl_AVL_M_result_s
{
  Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t *ptr;
  K___Prims_dtuple2___uint8_t_____size_t data;
}
Impl_AVL_M_result;

Impl_AVL_M_result
Impl_AVL_M_remove_leftmost_avl(
  Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t
  *(*f1)(Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t x0),
  void (*f2)(Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t *x0),
  Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t *ptr
);

Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t
*Impl_AVL_M_delete_avl(
  Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t
  *(*f1)(Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t x0),
  void (*f2)(Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t *x0),
  Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t *ptr,
  K___Prims_dtuple2___uint8_t_____size_t data_to_rm
);

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1

typedef uint8_t FStar_Pervasives_Native_option__size_t_tags;

typedef struct FStar_Pervasives_Native_option__size_t_s
{
  FStar_Pervasives_Native_option__size_t_tags tag;
  size_t v;
}
FStar_Pervasives_Native_option__size_t;

FStar_Pervasives_Native_option__size_t
Map_M_find(
  Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t *ptr,
  K___Prims_dtuple2___uint8_t_____size_t v
);

typedef struct mmap_md_s
{
  Impl_Core_node__K___Prims_dtuple2___uint8_t_____size_t **data;
  Steel_SpinLock_lock lock;
}
mmap_md;

void init_mmap_md(mmap_md *ret);

extern mmap_md metadata;

typedef struct Main_Meta_size_classes_all_s
{
  size_class *size_classes;
  uint8_t *slab_region;
}
Main_Meta_size_classes_all;

Main_Meta_size_classes_all Main_Meta_init(void);

extern Main_Meta_size_classes_all Main_Meta_sc_all;


#define internal_StarMalloc_H_DEFINED
#endif /* internal_StarMalloc_H */
