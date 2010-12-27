
// A partial application
record PAP(arg_size) {
  const ObjectHeader header;	      // Object header
  const owned fun;		      // The partially applied function
  const uint16 nargs;                 // Number of arguments stored in PAP
  // The size of the argument block.
  // Given as a number of PAP_ARG_WORDSIZE-sized words.
  const uint16 arg_size;
  // The argument block.  The argument block consists of a sequence of
  // arguments, concatenated with no padding.  The arguments may have been
  // converted to a larger-size format.
  const bytes(arg_size, value PAP_ARG_WORDSIZE) args;
};
