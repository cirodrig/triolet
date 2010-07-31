
#include <stdio.h>
#include <string.h>
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

/* ENTER_INEXACT(info)(fun, args, ret)
 * Call the inexact entry point of a function */
#define ENTER_INEXACT(fun) \
  ((void (*)(PyonPtr, PyonPtr, PyonPtr))&FUNINFO_INEXACT(fun))

/* Loop over each argument tag and argument in an argument block,
 * for arguments 0 to (n_args - 1).
 *
 * Syntax of usage:
 *
 * BEGIN_FOREACH_ARGUMENT(variable, variable, variable, variable, x, y) {
 *   function body(x, y);
 * } END_FOREACH_ARGUMENT(x, y);
 */

#define BEGIN_FOREACH_ARGUMENT(fun_info, args, start_offset, n_args, tag_var, arg_var) \
  {									\
    PyonPtr foreach_argument_args = (args);				\
    int foreach_argument_count;						\
    uint8_t *foreach_argument_tag_ptr =					\
      PYON_OFF_U8((fun_info), funinfo_firstargument_offset());		\
    int foreach_argument_offset = (start_offset);			\
    for (foreach_argument_count = (n_args);				\
	 foreach_argument_count;					\
	 foreach_argument_count--) {					\
      uint8_t foreach_argument_tag = *foreach_argument_tag_ptr++;	\
      foreach_argument_offset =						\
	align(foreach_argument_offset, TAG_ALIGN(foreach_argument_tag)); \
      uint8_t tag_var = foreach_argument_tag;				\
      void *arg_var = PYON_OFF_PTR(foreach_argument_tag_ptr, foreach_argument_offset);

#define END_FOREACH_ARGUMENT(tag_var, arg_var)				\
      foreach_argument_offset += TAG_SIZE(foreach_argument_tag);	\
    }									\
  }

#define BEGIN_FOREACH_PAP_ARGUMENT(fun_info, pap, tag_var, arg_var) \
  BEGIN_FOREACH_ARGUMENT(fun_info, pap, pap_firstargument_pre_offset(), \
			 PAP_NARGUMENTS(pap), tag_var, arg_var)


/*****************************************************************************/

static inline void
decref(PyonPtr p);

static inline void
incref(PyonPtr p);

static inline int
align(int offset, int alignment);

static inline int
funinfo_firstargument_offset(void);

static inline int
pap_firstargument_offset(PyonPtr fun_info);

static PyonPtr
new_pap_uint32(PyonPtr, int, void *, uint32_t);

static void
call_pap(PyonPtr pap, PyonPtr return_struct);

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

/* Get the offset of the first argument in a PAP, _before_ padding for
 * alignment.  The actual offset may be greater due to padding. */
static inline int
pap_firstargument_pre_offset(void)
{
  /* Get offset of the last fixed field */
  int offset = (char *)PAP_NARGUMENTS(NULL) - (char *)NULL;

  /* Add size of field */
  return offset + sizeof(PAP_NARGUMENTS(NULL));
}

/* Get the offset of the first argument in a PAP, using the function info
 * table to figure out its alignment.
 */
static inline int
pap_firstargument_offset(PyonPtr fun_info)
{
  /* Get the argument's tag */
  uint8_t tag = *PYON_OFF_U8(fun_info, funinfo_firstargument_offset());

  /* Return the aligned offset */
  return align(pap_firstargument_pre_offset(), TAG_ALIGN(tag));
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
  PyonPtr fun = PAP_FUN(p);
  PyonPtr fun_info = OBJECT_INFO(fun);

  /* Release the function */
  decref(fun);

  /* Process each argument.
   * Number of arguments must be >= 1 and <= FUNINFO_ARITY(info_ptr). */
  BEGIN_FOREACH_PAP_ARGUMENT(fun_info, p, tag, arg_ptr) {
    /* If this argument is owned, release it */
    if (tag == OWNEDREF_TAG) decref(*(PyonPtr *)arg_ptr);
  } END_FOREACH_ARGUMENT(tag, arg);

  /* Deallocate the PAP */
  free(p);
}

/* Apply an object to a 32-bit integer (or pointer) value */
PyonPtr
apply_i32_f(PyonPtr obj, uint32_t arg)
{
  PyonPtr ret;
  apply_i32(obj, arg, &ret);
  return ret;
}

void
apply_i32(PyonPtr obj, uint32_t arg, PyonPtr return_struct)
{
  /* What kind of object? */
  PyonPtr info = OBJECT_INFO(obj);
  switch(INFO_TAG(info)) {
  case FUN_TAG:
    {
      int arity = FUNINFO_ARITY(info);
      switch(arity) {
      case 1:
	/* Call the function */
	ENTER_INEXACT(info)(obj, &arg, return_struct);
	break;
      default:
	/* Create and return a PAP */
	*(PyonPtr *)return_struct = new_pap_uint32(obj, 0, NULL, arg);
	break;
      }
    }
    break;
  case PAP_TAG:
    {
      PyonPtr fun = PAP_FUN(obj);
      PyonPtr fun_info = OBJECT_INFO(fun);
      int arity = FUNINFO_ARITY(fun_info);
      int firstarg_offset = pap_firstargument_offset(fun_info);
      void *firstarg_ptr = PYON_OFF_PTR(obj, firstarg_offset);
      int n_pap_arguments = PAP_NARGUMENTS(obj);
      PyonPtr new_pap = new_pap_uint32(fun, n_pap_arguments, firstarg_ptr,
				       arg);
      
      /* If the function is fully applied, then call it.  Otherwise,
       * return the PAP. */
      if (n_pap_arguments + 1 == arity) {
	call_pap(new_pap, return_struct);
	decref(new_pap);
      }
      else
	*(PyonPtr *)return_struct = new_pap;
    }
    break;
  default:
    fprintf(stderr, "Internal error: %s\n", __func__);
    exit(-1);
  }
}

/* Call a PAP.  The PAP must contain a number of arguments equal to the
 * function arity. */
static void
call_pap(PyonPtr pap, PyonPtr return_struct)
{
  PyonPtr fun = PAP_FUN(pap);
  PyonPtr fun_info = OBJECT_INFO(fun);
  void *firstarg_ptr = PYON_OFF_PTR(pap, pap_firstargument_offset(fun_info));

  /* Call the entry point with the function closure and arguments */
  ENTER_INEXACT(fun_info)(fun, firstarg_ptr, return_struct);
}

/* Create a new PAP consisting of the function applied to the given argument
 * block, plus an int.
 */
static PyonPtr
new_pap_uint32(PyonPtr fun, int n_arguments, void *p_arguments, uint32_t arg)
{
  PyonPtr fun_info = OBJECT_INFO(fun);
  int arity = FUNINFO_ARITY(fun_info);

  /* Compute the size of the new PAP.  Increment reference counts of owned
   * arguments. */
  int arguments_start = pap_firstargument_offset(OBJECT_INFO(fun));
  int arguments_size = 0;
  BEGIN_FOREACH_ARGUMENT(fun_info, p_arguments, 0, n_arguments, tag, arg_ptr) {
    arguments_size = align(arguments_size, TAG_ALIGN(tag)) + TAG_SIZE(tag);

    if (tag == OWNEDREF_TAG) incref(*(PyonPtr *)arg_ptr);
  } END_FOREACH_ARGUMENT(tag, arg_ptr);

  /* Allocate memory */
  PyonPtr new_pap = alloc(arguments_start + arguments_size);

  /* Initialize the PAP */
  PAP_REFCT(new_pap) = 1;
  PAP_INFO(new_pap) = &pap_info;
  PAP_FUN(new_pap) = fun;
  incref(fun);
  PAP_NARGUMENTS(new_pap) = n_arguments;
  
  /* Copy arguments to the new PAP */
  memcpy(PYON_OFF_PTR(new_pap, arguments_start), p_arguments, arguments_size);

  return new_pap;
}
