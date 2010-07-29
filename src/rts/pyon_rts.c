
#include <stdio.h>
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

#define PAP_NUM_FIELDS(obj) FIELD_REF(obj, uint32_t, 16)
#define PAP_FIRST_FIELD_TYPE(obj) FIELD_REF(obj, char, 20)

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

/* The deallocation function for a partial application.  Inspect the record
 * to determine how to deallocate it.
 *
 * This code must remain consistent with the code generator that creates PAPs.
 */
void free_pap(ExternPyonPtr p)
{
  /* Get the number of fields */
  int num_fields = PAP_NUM_FIELDS(p);
  int i;
  char *current_field_type = &PAP_FIRST_FIELD_TYPE(p);
  char *current_field;

  /* Deallocate each field */
  for (i = num_fields; i; i--) {
    int size;
    int align;
    switch(*current_field_type) {
    case 1:
    case 2:
    case 6: size = align = 1; goto pod; /* 8-byte value */
    case 3:
    case 7: size = align = 2; goto pod; /* 16-byte value */
    case 4:
    case 8:
    case 10: size = align = 4; goto pod; /* 32-byte value */
    case 5:
    case 9:
    case 11:
    case 12: size = align = 8; goto pod; /* 64-byte value */
    case 13:
      /* Owned object; adjust its reference count */
      size = align = 8;
      /* Adjust alignment */
      current_field = current_field + (-(int32_t)current_field) % align;
      decref((PyonPtr)current_field);
      goto done;
    default:
      fprintf(stderr, "free_pap: Invalid tag\n");
      exit(-1);
    }
  pod:
    /* Adjust alignment for current field */
    current_field = current_field + (-(int32_t)current_field) % align;
  done:
    /* Go to next field */
    current_field += size;
  }

  /* Deallocate */
  fprintf(stderr, "free_pap: Not implemented\n");
  exit(-1);
}
