// SPDX-License-Identifier: Apache-2.0


#ifndef __internal_StarMalloc_H
#define __internal_StarMalloc_H

#include "krmllib.h"

#include "../StarMalloc.h"

typedef struct Impl_Trees_Cast_M_data_s
{
  uint8_t *fst;
  size_t snd;
}
Impl_Trees_Cast_M_data;

typedef struct Impl_Trees_Cast_M_node_s Impl_Trees_Cast_M_node;

typedef struct Impl_Trees_Cast_M_node_s Impl_Trees_Cast_M_node;

typedef struct Impl_Trees_Cast_M_node_s
{
  Impl_Trees_Cast_M_data data;
  Impl_Trees_Cast_M_node *left;
  Impl_Trees_Cast_M_node *right;
  uint64_t size;
  uint64_t height;
}
Impl_Trees_Cast_M_node;

typedef struct Impl_Trees_Types_mmap_md_slabs_s
{
  uint8_t *slab_region;
  SizeClass_size_class_struct_ scs;
  Steel_SpinLock_lock lock;
}
Impl_Trees_Types_mmap_md_slabs;

void Impl_Trees_Types_init_mmap_md_slabs(Impl_Trees_Types_mmap_md_slabs *ret);

extern Impl_Trees_Types_mmap_md_slabs Impl_Trees_Types_metadata_slabs;

bool Impl_BST_M_member(Impl_Trees_Cast_M_node *ptr, Impl_Trees_Cast_M_data v);

Impl_Trees_Cast_M_node
*Impl_AVL_M_insert_avl(
  Impl_Trees_Cast_M_node *(*f1)(Impl_Trees_Cast_M_node x0),
  void (*f2)(Impl_Trees_Cast_M_node *x0),
  bool r,
  Impl_Trees_Cast_M_node *ptr,
  Impl_Trees_Cast_M_data new_data
);

typedef struct Impl_AVL_M_result_s
{
  Impl_Trees_Cast_M_node *ptr;
  Impl_Trees_Cast_M_data data;
}
Impl_AVL_M_result;

Impl_AVL_M_result
Impl_AVL_M_remove_leftmost_avl(
  Impl_Trees_Cast_M_node *(*f1)(Impl_Trees_Cast_M_node x0),
  void (*f2)(Impl_Trees_Cast_M_node *x0),
  Impl_Trees_Cast_M_node *ptr
);

Impl_Trees_Cast_M_node
*Impl_AVL_M_delete_avl(
  Impl_Trees_Cast_M_node *(*f1)(Impl_Trees_Cast_M_node x0),
  void (*f2)(Impl_Trees_Cast_M_node *x0),
  Impl_Trees_Cast_M_node *ptr,
  Impl_Trees_Cast_M_data data_to_rm
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
Map_M_find(Impl_Trees_Cast_M_node *ptr, Impl_Trees_Cast_M_data v);

typedef struct mmap_md_s
{
  Impl_Trees_Cast_M_node **data;
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


#define __internal_StarMalloc_H_DEFINED
#endif
