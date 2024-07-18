// SPDX-License-Identifier: Apache-2.0


#ifndef __SizeClassSelection_H
#define __SizeClassSelection_H

#include "krmllib.h"

#include "ExternUtils.h"

uint32_t SizeClassSelection_log2u64(uint64_t x);

krml_checked_int_t SizeClassSelection_sort(krml_checked_int_t x);

uint32_t SizeClassSelection_inv_impl(uint32_t bound_input, uint32_t bound_len, uint32_t x);


#define __SizeClassSelection_H_DEFINED
#endif
