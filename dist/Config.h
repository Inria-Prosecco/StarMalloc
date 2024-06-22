// SPDX-License-Identifier: Apache-2.0


#ifndef __Config_H
#define __Config_H

#include "krmllib.h"

#define CONFIG_NB_SIZE_CLASSES ((size_t)27U)

typedef size_t (*Config_sc_selection_f)(uint32_t x0);

extern bool Config_enable_sc_fast_selection;

#define CONFIG_NB_ARENAS ((size_t)4U)

extern size_t Config_metadata_max;

extern bool Config_enable_guard_pages;

extern size_t Config_guard_pages_interval;

extern bool Config_enable_quarantine;

extern bool Config_enable_quarantine_trap;

extern bool Config_enable_quarantine_strict_trap;

extern size_t Config_quarantine_queue_length;

extern size_t Config_quarantine_queue_threshold;

extern bool Config_enable_zeroing_malloc;

extern bool Config_enable_zeroing_free;

extern bool Config_enable_slab_canaries_malloc;

extern bool Config_enable_slab_canaries_free;

extern uint8_t Config_slab_canaries_magic1;

extern uint8_t Config_slab_canaries_magic2;


#define __Config_H_DEFINED
#endif
