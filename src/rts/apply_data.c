#include "machine.h"

/* A lookup table, indexed by type tag, giving the size of a value stored in
 * a PAP's argument block.
 * The size is given as a multiple of the word size.
 */

#if WORD_SIZE == 4

unsigned char triolet_type_tag_pap_size[] = {
  0,				/* Bits0Tag */
  1,				/* Bits32Tag */
  2,				/* Bits64Tag */
  1,                            /* BitsOwnedTag */
  2                             /* BitsCursorTag */
};

#elif WORD_SIZE == 8

unsigned char triolet_type_tag_pap_size[] = {
  0,				/* Bits0Tag */
  255,				/* Bits32Tag is invalid */
  1,				/* Bits64Tag */
  1,                            /* BitsOwnedTag */
  2                             /* BitsCursorTag */
};

#else
# error "Unrecognized architecture"
#endif
