// Common RTS headers in pyasm code

#include "machine.h"

// Info table tags
#define TAG_FUN (uint8 0)
#define TAG_PAP (uint8 1)
#define TAG_CON (uint8 2)

// Object header for global objects
#define INIT_OBJECT_HEADER (ObjectHeader { word 1, dummy_finalizer })

#if WORD_SIZE == 4
# define word uint32
# define intptr int32
#elif WORD_SIZE == 8
# define word uint64
# define intptr int64
#else
# error "Unrecognized architecture"
#endif

#if INT_SIZE == 4
# define int int32
# define uint uint32
#elif INT_SIZE == 8
# define int int64
# define uint uint64
#else
# error "Unrecognized architecture"
#endif
