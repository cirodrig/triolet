
/* A lookup table, indexed by type tag, giving the size of a value stored in
 * a PAP's argument block.  The size is given as a multiple of PAP_ARG_WORDSIZE
 * words. */
unsigned char pyon_type_tag_pap_size[] = {
  1,				/* Int8Tag */
  1,				/* Int16Tag */
  1,				/* Int32Tag */
  2,				/* Int64Tag */
  1,				/* Float32Tag */
  2,				/* Float64Tag */
  1,				/* BoxedTag */
};
