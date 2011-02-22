#include "machine.h"

/* A lookup table, indexed by type tag, giving the size of a value stored in
 * a PAP's argument block.
 * The size is given as a multiple of the word size.
 */

#if WORD_SIZE == 4

unsigned char pyon_type_tag_pap_size[] = {
  1,				/* Int8Tag */
  1,				/* Int16Tag */
  1,				/* Int32Tag */
  2,				/* Int64Tag */
  1,				/* Float32Tag */
  2,				/* Float64Tag */
  1,				/* BoxedTag */
};

#elif WORD_SIZE == 8

unsigned char pyon_type_tag_pap_size[] = {
  1,				/* Int8Tag */
  1,				/* Int16Tag */
  1,				/* Int32Tag */
  1,				/* Int64Tag */
  1,				/* Float32Tag */
  1,				/* Float64Tag */
  1,				/* BoxedTag */
};

#else
# error "Unrecognized architecture"
#endif
