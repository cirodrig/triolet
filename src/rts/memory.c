
#include <stdlib.h>
#include "pyon_internal.h"

/* Allocate some heap data */
PyonPtr
pyon_alloc(uint32_t size)
{
  PyonPtr ptr = malloc(size);
#ifdef CHATTY_ALLOC
  fprintf(stderr, "Allocating   %p (%d bytes)\n", ptr, (int)size);
#endif
  return ptr;
}

/* Deallocate some heap data */
void
pyon_dealloc(PyonPtr p)
{
#ifdef CHATTY_ALLOC
  fprintf(stderr, "Deallocating %p\n", p);
#endif
  free(p);
}
