// SPDX-License-Identifier: Apache-2.0


#include "Constants.h"

uint32_t Constants_page_size = 4096U;

size_t Constants_max_sc_coef = 32U;

size_t Constants_sc_ex_slab_size = (size_t)4096U * 64U;

bool Constants_uu___is_Sc(Constants_sc_union projectee)
{
  if (projectee.tag == Constants_Sc)
    return true;
  else
    return false;
}

bool Constants_uu___is_Sc_ex(Constants_sc_union projectee)
{
  if (projectee.tag == Constants_Sc_ex)
    return true;
  else
    return false;
}

uint32_t Constants_get_sc(Constants_sc_union scu)
{
  if (scu.tag == Constants_Sc)
    return scu.case_Sc;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint32_t Constants_get_sc_ex(Constants_sc_union scu)
{
  if (scu.tag == Constants_Sc_ex)
    return scu.case_Sc_ex;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

