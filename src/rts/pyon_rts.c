
#include <stdlib.h>

#include "pyon.h"

/*****************************************************************************/
/* Object layouts */

/* TODO: Don't use magic numbers for field offsets.  Compute them in a way
 * that's consistent with how the code generator computes them. */

/* Get a reference to a field of 'object' at byte offset 'offset' with type
 * 'type'.  The type should be a typedef or a pointer to typedef. */
#define FIELD_REF(object, type, offset) \
  (*(type *)((object) + (offset)))

#define OBJECT_REFCT(obj) FIELD_REF(obj, uint32_t, 0)
#define OBJECT_FREEFUN(obj) FIELD_REF(obj, free_function, 8)

#define CLOSURE_INFOTABLE(obj) FIELD_REF(obj, PyonPtr, 16)
#define CLOSURE_CAPTUREDVARS(obj) FIELD_REF(obj, PyonPtr, 24)

/*****************************************************************************/

/* Pointers to Pyon objects */
typedef void *PyonPtr;

/* Auto-generated Pyon code uses 'char*' as the type of pointers.  We use
 * the same type to avoid compile-time warnings. */
typedef char *ExternPyonPtr;

/* An object's 'free' method */
typedef void (*free_function)(PyonPtr);

/* Decrement an object's reference count, and free it if the reference count
 * falls to zero. */
static inline void decref(PyonPtr p)
{
  /* FIXME: thread safety */
  uint32_t rc = OBJECT_REFCT(p)--;
  if (rc == 0) {
    OBJECT_FREEFUN(p)(p);
  }
}

/* Increment an object's reference count. */
static inline void incref(PyonPtr p)
{
  /* FIXME: thread safety */
  OBJECT_REFCT(p)++;
}

/*****************************************************************************/
/* Exported functions */

/* Allocate some heap data */
ExternPyonPtr
alloc(uint32_t size)
{
  return malloc(size);
}

/* Deallocate some heap data */
void
dealloc(ExternPyonPtr p)
{
  free(p);
}

/* The deallocation function for a lambda closure.  Deallocate the closure
 * and the associated captured variable record. */
void free_lambda_closure(ExternPyonPtr p)
{
  decref((PyonPtr)CLOSURE_CAPTUREDVARS(p));
  dealloc(p);
}

