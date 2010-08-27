
#include "pyon_internal.h"

const struct tag_sizealign_t tag_sizealign_array[] =
  { {1, 1},				/* Int8Tag */
    {2, 2},				/* Int16Tag */
    {4, 4},				/* Int32Tag */
    {8, 8},				/* Int64Tag */
    {4, 4},				/* Float32Tag */
    {8, 8},				/* Float64Tag */
    {SIZEOF_PYON_PTR, ALIGNOF_PYON_PTR}	/* OwnedRefTag */
  };

const char bits_tag_size_array [] =
  { 4,				/* Bits32Tag */
    8,				/* Bits64Tag */
    4				/* OwnedRefBitsTag */
  };
