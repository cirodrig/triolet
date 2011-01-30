// Common RTS headers in pyasm code

// Info table tags
#define TAG_FUN (uint8 0)
#define TAG_PAP (uint8 1)
#define TAG_CON (uint8 2)

// Object header for global objects
#define INIT_OBJECT_HEADER (ObjectHeader { word 1, dummy_finalizer })

#if defined(ARCH_I386)
# include "arch/rts_x86.h"
#elif defined(ARCH_X86_64)
# include "arch/rts_x86_64.h"
#else
# error "Unrecognized architecture"
#endif

