
#define PAP_WORDSIZE (word 8)

// For each data type that is handled by an 'apply' function, we define
// the data type's size, how to write it to memory at an address, and how
// to read it from memory into a variable.
#define POINTER_ARG_WORDSIZE (word 1)
#define POINTER_ARG_PUT(dst_addr, src) !(dst_addr) = (src)
#define POINTER_ARG_GET(dst_var, src) dst_var = pointer load (src)

// A partial application.  The argument is the size of the argument space
// in bytes.
//
// This is not arch-specific
record PAP(argsz) {
  const ObjectHeader header;		// Object header
  const owned fun;			// Partially applied function
  const uint16 nargs;                 // Number of arguments stored in PAP
  const uint16 arg_size;	      // Size of arguments in words
  const bytes(value argsz, value PAP_WORDSIZE) args; // Argument data
};
