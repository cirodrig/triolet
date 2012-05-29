
#include <stdlib.h>
#include <stdio.h>
#include <gc.h>
#include "pyon.h"
#include "struct.h"
#include "machine.h"

/* When defined, print a message on every allocation and deallocation. */
// #define CHATTY_ALLOC

/* Allocate some heap data */
PyonPtr
pyon_alloc(uint32_t size)
{
  PyonPtr ptr = GC_MALLOC(size);
#ifdef CHATTY_ALLOC
  fprintf(stderr, "Allocating - %p (%d bytes)\n", ptr, (int)size);
#endif
  return ptr;
}

/* Allocate some heap data that doesn't contain any pointers */
PyonPtr
pyon_alloc_nopointers(uint32_t size)
{
  PyonPtr ptr = GC_MALLOC_ATOMIC(size);
#ifdef CHATTY_ALLOC
  fprintf(stderr, "Allocating A %p (%d bytes)\n", ptr, (int)size);
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
  GC_FREE(p);
}

/* Allocate a box containing some heap data.  A pointer to the box is
   returned. */
PyonPtr
pyon_alloc_boxed(uint32_t size, uint32_t alignment)
{
  // The box's size consists of a word, followed by padding, followed
  // by the object
  uint32_t box_size = size + align(WORD_SIZE, alignment);
  PyonPtr ptr = pyon_alloc(box_size);

  // TODO: initialize the header

  return ptr;
}
