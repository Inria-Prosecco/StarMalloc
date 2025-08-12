// SPDX-License-Identifier: Apache-2.0


#ifndef krmlinit_H
#define krmlinit_H

#include "krmllib.h"

#if defined(__GNUC__) && !(defined(_WIN32) || defined(_WIN64))
__attribute__ ((visibility ("hidden")))
#endif

void krmlinit_globals(void);


#define krmlinit_H_DEFINED
#endif /* krmlinit_H */
