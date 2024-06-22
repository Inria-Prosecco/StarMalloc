// SPDX-License-Identifier: Apache-2.0


#ifndef __Utils2_H
#define __Utils2_H

#include "krmllib.h"

typedef void *Utils2_same_base_array;

uint32_t Utils2_nb_slots(uint32_t size_class);

size_t Utils2_rounding(uint32_t size_class);

typedef void *Utils2_zf_b;

uint64_t Utils2_full_n_aux(uint32_t bound);

uint64_t Utils2_full_n(uint32_t bound);

bool Utils2_has_free_slot_s(uint32_t size_class, uint64_t *md);

bool Utils2_is_empty_s(uint32_t size_class, uint64_t *md);

bool Utils2_is_partial_s(uint32_t size_class, uint64_t *md);

bool Utils2_is_full_s(uint32_t size_class, uint64_t *md);

typedef void *Utils2_zf_u64;

typedef void *Utils2_zf_u8;


#define __Utils2_H_DEFINED
#endif
