// SPDX-License-Identifier: Apache-2.0


#ifndef __SizeClassSelection_H
#define __SizeClassSelection_H

#include "krmllib.h"

uint32_t SizeClassSelection_log2u64(uint64_t x);

uint32_t SizeClassSelection_inv_impl(uint32_t x);


#define __SizeClassSelection_H_DEFINED
#endif
