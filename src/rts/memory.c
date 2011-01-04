
#include <stdlib.h>
#include <stdio.h>
#include "pyon.h"

/* When defined, print a message on every allocation and deallocation. */
#define CHATTY_ALLOC

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
