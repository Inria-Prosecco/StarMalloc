// SPDX-License-Identifier: Apache-2.0


#ifndef __krmlinit_H
#define __krmlinit_H

#include "krmllib.h"

#include "StarMalloc.h"
#include "Config.h"

#if defined(__GNUC__) && !(defined(_WIN32) || defined(_WIN64))
__attribute__ ((visibility ("hidden")))
#endif

void krmlinit_globals(void);


#define __krmlinit_H_DEFINED
#endif
