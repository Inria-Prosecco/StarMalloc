// SPDX-License-Identifier: Apache-2.0


#include "Config.h"

size_t Config_metadata_max = (size_t)16777216U;

bool Config_enable_sc_fast_selection = true;

bool Config_enable_guard_pages = true;

size_t Config_guard_pages_interval = (size_t)2U;

bool Config_enable_quarantine = true;

bool Config_enable_quarantine_trap = true;

bool Config_enable_quarantine_strict_trap = false;

size_t Config_quarantine_queue_length = (size_t)1024U;

size_t Config_quarantine_queue_threshold = (size_t)256U;

bool Config_enable_zeroing_malloc = true;

bool Config_enable_zeroing_free = true;

bool Config_enable_slab_canaries_malloc = true;

bool Config_enable_slab_canaries_free = true;

uint8_t Config_slab_canaries_magic1 = 42U;

uint8_t Config_slab_canaries_magic2 = 23U;

