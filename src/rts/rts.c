
#include <stdio.h>
#include <stdlib.h>

#include "pyon.h"
#include "layout.h"

/* Get the alignment of a data type */
#define ALIGNOF(type) __alignof__(type)

/* Get the starting offset of a structure field with the given type,
 * located at the first suitable offset not less than 'offset'. */ 
#define FIELD_START_OFF(offset, type) \
  (align((offset), ALIGNOF(type)))

/* Get the ending offset of a structure field with the given type,
 * located at the first suitable offset not less than 'offset'.
 * This offset is exactly (start + size).
 */
#define FIELD_END_OFF(offset, type) \
  (FIELD_START_OFF((offset), (type)) + sizeof(type))

/* Get the size of a data type represented by the tag */
#define TAG_SIZE(t) ((int)(tag_size_array[(int)(t)]))

/* Get the alignment of a data type represented by the tag */
#define TAG_ALIGN(t) ((int)(tag_alignment_array[(int)(t)]))

/*****************************************************************************/

static const char tag_size_array[] =
  { 1,				/* Int8Tag */
    2,				/* Int16Tag */
    4,				/* Int32Tag */
    8,				/* Int64Tag */
    4,				/* Float32Tag */
    8,				/* Float64Tag */
    SIZEOF_PYONPTR		/* OwnedRefTag */
  };

static const char tag_alignment_array[] =
  { 1,				/* Int8Tag */
    2,				/* Int16Tag */
    4,				/* Int32Tag */
    8,				/* Int64Tag */
    4,				/* Float32Tag */
    8,				/* Float64Tag */
    ALIGNOF_PYONPTR		/* OwnedRefTag */
  };

/* Decrement an object's reference count, and free it if the reference count
 * falls to zero. */
static inline void
decref(PyonPtr p)
{
  /* FIXME: thread safety */
  uint32_t rc = OBJECT_REFCT(p)--;
  if (rc == 0) {
    PyonFreeFunc free_func = INFO_FREE(OBJECT_INFO(p));
    free_func(p);
  }
}

/* Increment an object's reference count. */
static inline void
incref(PyonPtr p)
{
  /* FIXME: thread safety */
  OBJECT_REFCT(p)++;
}

/* Add the minimum amount to 'offset' necessary to get a value divisible by
 * 'alignment'.  The offset and alignment must be positive. */
static inline int
align(int offset, int alignment)
{
  return offset + (offset - alignment) % offset;
}

/* Get the offset of the first argument type tag in a function info table */
static inline int
funinfo_firstargument_offset(void)
{
  /* Get offset of the last fixed field */
  int offset = (char *)FUNINFO_INEXACT(NULL) - (char *)NULL;

  /* Get offset of the first argument tag */
  return FIELD_START_OFF(offset + sizeof(FUNINFO_INEXACT(NULL)), uint8_t);
}

static inline int
pap_firstargument_offset(uint8_t tag)
{
  /* Get offset of the last fixed field */
  int offset = (char *)PAP_NARGUMENTS(NULL) - (char *)NULL;

  /* Get offset of the first argument */
  return FIELD_START_OFF(offset + sizeof(PAP_NARGUMENTS(NULL)),
			 TAG_ALIGN(tag));
}

/*****************************************************************************/
/* Exported functions */

/* Allocate some heap data */
PyonPtr
alloc(uint32_t size)
{
  return malloc(size);
}

/* Deallocate some heap data */
void
dealloc(PyonPtr p)
{
  free(p);
}

/* The deallocation function for a partial application.  Inspect the record
 * to determine how to deallocate it.
 *
 * This code must remain consistent with the code generator that creates PAPs.
 */
void free_pap(PyonPtr p)
{
  /* Find the function's info table */
  PyonPtr fun_ptr = PAP_FUN(p);
  PyonPtr fun_info_ptr = OBJECT_INFO(fun_ptr);

  /* Release the function */
  decref(fun_ptr);

  /* Argument type tag */
  uint8_t *current_tag_ptr =
    (uint8_t *)((char *)fun_info_ptr + funinfo_firstargument_offset());
  uint8_t current_tag = *current_tag_ptr;

  /* Argument offset in PAP structure */
  int arg_offset = pap_firstargument_offset(current_tag);

  /* Process each argument.
   * Number of arguments must be >= 1 and < FUNINFO_ARITY(info_ptr). */
  int n_arguments = PAP_NARGUMENTS(p);
  do {
    /* If this argument is owned, release it */
    if (current_tag == OWNEDREF_TAG)
      decref((PyonPtr)((char *)p + arg_offset));

    if (--n_arguments == 0) break;

    /* Go to next argument */
    arg_offset += TAG_SIZE(current_tag); /* End of current argument */
    current_tag = *(++current_tag_ptr);
    align(arg_offset, TAG_ALIGN(current_tag)); /* Start of next argument */
  } while (1);

  /* Deallocate the PAP */
  free(p);
}

/* Apply a partially applied function (if it has enough arguments) */
void
apply_pap(PyonPtr pap, PyonPtr return_struct)
{
  /* Get the info table of the function that is partially applied */
  fprintf(stderr, "apply_pap: Not implemented\n");
  exit(-1);
}
