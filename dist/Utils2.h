// SPDX-License-Identifier: Apache-2.0


#ifndef Utils2_H
#define Utils2_H

#include "krmllib.h"

uint32_t Utils2_nb_slots(uint32_t size_class);

size_t Utils2_rounding(uint32_t size_class);

uint64_t Utils2_full_n_aux(uint32_t bound);

uint64_t Utils2_full_n(uint32_t bound);

bool Utils2_has_free_slot_s(uint32_t size_class, uint64_t *md);

bool Utils2_is_empty_s(uint32_t size_class, uint64_t *md);

bool Utils2_is_partial_s(uint32_t size_class, uint64_t *md);

bool Utils2_is_full_s(uint32_t size_class, uint64_t *md);


#define Utils2_H_DEFINED
#endif /* Utils2_H */
