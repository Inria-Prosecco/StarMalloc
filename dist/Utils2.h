// SPDX-License-Identifier: Apache-2.0


#ifndef __Utils2_H
#define __Utils2_H

#include "krmllib.h"

#include "Constants.h"

size_t Utils2_rounding(uint32_t size_class);

uint64_t Utils2_full_n_aux(uint32_t bound);

uint64_t Utils2_full_n(uint32_t bound);

bool Utils2_is_empty_s(uint32_t size_class, uint64_t *md);

bool Utils2_is_empty_s2(uint32_t size_class, uint64_t *md, uint64_t *md_q);

bool Utils2_has_free_slot_s(uint32_t size_class, uint64_t *md);

bool Utils2_has_free_slot_s2(uint32_t size_class, uint64_t *md, uint64_t *md_q);

bool Utils2_is_partial_s(uint32_t size_class, uint64_t *md);

bool Utils2_is_partial_s2(uint32_t size_class, uint64_t *md, uint64_t *md_q);

bool Utils2_is_full_s(uint32_t size_class, uint64_t *md);

bool Utils2_is_full_s2(uint32_t size_class, uint64_t *md, uint64_t *md_q);

void Utils2_reset_to_empty(uint32_t size_class, uint64_t *md);


#define __Utils2_H_DEFINED
#endif
