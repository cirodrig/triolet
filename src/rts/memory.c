
#include <stdlib.h>
#include <stdio.h>
#include <gc.h>
#include "triolet.h"
#include "struct.h"
#include "machine.h"

/* When defined, print a message on every allocation and deallocation. */
// #define CHATTY_ALLOC

#define MAX_GC_SIZE (1<<20)

/* Allocate some heap data */
TrioletPtr
triolet_alloc(uint32_t size)
{
#if 0
  if (size > MAX_GC_SIZE) 
	return malloc(size);
#endif

  TrioletPtr ptr = GC_MALLOC(size);
#ifdef CHATTY_ALLOC
  fprintf(stderr, "Allocating - %p (%d bytes)\n", ptr, (int)size);
#endif
  return ptr;
}

/* Allocate some heap data that doesn't contain any pointers */
TrioletPtr
triolet_alloc_nopointers(uint32_t size)
{
  TrioletPtr ptr = GC_MALLOC_ATOMIC(size);
#ifdef CHATTY_ALLOC
  fprintf(stderr, "Allocating A %p (%d bytes)\n", ptr, (int)size);
#endif
  return ptr;
}

/* Deallocate some heap data */
void
triolet_dealloc(TrioletPtr p)
{
#ifdef CHATTY_ALLOC
  fprintf(stderr, "Deallocating %p\n", p);
#endif
#if 1
  GC_FREE(p);
#endif
}

/* Allocate a box containing some heap data.  A pointer to the box is
   returned. */
TrioletPtr
triolet_alloc_boxed(uint32_t size, uint32_t alignment)
{
  // The box's size consists of a word, followed by padding, followed
  // by the object
  uint32_t box_size = size + align(WORD_SIZE, alignment);
  TrioletPtr ptr = triolet_alloc(box_size);

  // TODO: initialize the header

  return ptr;
}

// Do nothing.
// This function is inscrutable to the Triolet backend optimizer to
// selectively inhibit optimization.
TrioletPtr triolet_preserve(TrioletPtr p)
{
  return p;
}
