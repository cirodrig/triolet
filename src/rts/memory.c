
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

/* Copy a 4-byte value */
void
pyon_copy4(PyonPtr src, PyonPtr dst)
{
  *(uint32_t*)dst = *(uint32_t*)src;
}

/* Deallocate a global closure */
void
dealloc_global_closure(PyonPtr p)
{
  pyon_dealloc(p);
}

/* Entry point to 'dealloc' */
void
dealloc_exact_entry(PyonPtr closure, PyonPtr arg)
{
  pyon_dealloc(arg);
}

/* Entry point to 'dealloc' */
void
dealloc_inexact_entry(PyonPtr closure, PyonPtr args, PyonPtr ret)
{
  PyonPtr arg = *(PyonPtr *)args;
  pyon_dealloc(arg);
}

/* Entry point to 'copy4' */
void
copy4_exact_entry(PyonPtr closure, PyonPtr src, PyonPtr dst)
{
  pyon_copy4(src, dst);
}

/* Entry point to 'copy4' */
void
copy4_inexact_entry(PyonPtr closure, PyonPtr args, PyonPtr ret)
{
  int src_offset = 0;
  int dst_offset = src_offset + sizeof(PyonPtr);
  PyonPtr src = *PYON_OFF_PTR(args, src_offset);
  PyonPtr dst = *PYON_OFF_PTR(args, dst_offset);

  pyon_copy4(src, dst);
}

