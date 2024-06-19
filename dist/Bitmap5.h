// SPDX-License-Identifier: Apache-2.0


#ifndef __Bitmap5_H
#define __Bitmap5_H

#include "krmllib.h"

bool Bitmap5_bm_get(uint64_t *arr, uint32_t k);

void Bitmap5_bm_set(uint64_t *arr, uint32_t k);

void Bitmap5_bm_unset(uint64_t *arr, uint32_t k);


#define __Bitmap5_H_DEFINED
#endif
