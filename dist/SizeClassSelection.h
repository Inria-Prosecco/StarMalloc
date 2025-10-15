// SPDX-License-Identifier: Apache-2.0


#ifndef SizeClassSelection_H
#define SizeClassSelection_H

#include "krmllib.h"

extern krml_checked_int_t SizeClassSelection__n;

extern krml_checked_int_t SizeClassSelection__k;

uint32_t SizeClassSelection_log2u64(uint64_t x);

uint32_t SizeClassSelection_inv_impl(uint32_t x);


#define SizeClassSelection_H_DEFINED
#endif /* SizeClassSelection_H */
