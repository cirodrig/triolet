// Common RTS headers in pyasm code

// Info table tags
#define TAG_FUN (uint8 0)
#define TAG_PAP (uint8 1)
#define TAG_CON (uint8 2)

// Get the smallest value greater than or equal to 'off' that is a multiple
// of 'align'.  'off' is nonnegative, and 'align' is positive.  This macro
// is used for computing structure field offsets and sizes.
#define PAD(off, align) ((off) + ((-(off)) % (align)))

// Create a new object and initialize its header.
// The first parameter is the name that the object is assigned to.
// The second parameter is the type.
// The third parameter is the info table.
#define ALLOC_OBJECT(v, type, infotable) \
  ALLOC_OBJECT_p = pointer primcall pyon_alloc (sizeof type); \
  ALLOC_OBJECT_p @! type.header.refct = word 1; \
  ALLOC_OBJECT_p @! type.header.info = infotable; \
  v = ALLOC_OBJECT_p as owned;

#include "arch/rts_x86.h"
