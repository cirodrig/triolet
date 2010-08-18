
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "pyon_internal.h"

/* Print a message every time memory is allocated or deallocated. */
#undef CHATTY_ALLOC

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

static inline int
funinfo_firstargument_offset(void);

static inline int
pap_firstargument_offset(PyonPtr fun_info);

static inline PyonPtr
new_pap_u32(PyonPtr, int, void *, uint32_t);

static inline PyonPtr
new_pap_f32(PyonPtr, int, void *, float);

static PyonPtr
new_pap_bytes(PyonPtr fun, int n_arguments, void *p_arguments, void *arg_bytes);

static void
call_pap(PyonPtr pap, PyonPtr return_struct);

/* Get the offset of the first argument type tag in a function info table */
static inline int
funinfo_firstargument_offset(void)
{
  /* Get offset of the last fixed field */
  int offset = (char *)&FUNINFO_INEXACT(NULL) - (char *)NULL;

  /* Get offset of the first argument tag */
  return FIELD_START_OFF(offset + sizeof(FUNINFO_INEXACT(NULL)), uint8_t);
}

/* Get the offset of the first argument in a PAP, _before_ padding for
 * alignment.  The actual offset may be greater due to padding. */
static inline int
pap_firstargument_pre_offset(void)
{
  /* Get offset of the last fixed field */
  int offset = (char *)&PAP_NARGUMENTS(NULL) - (char *)NULL;

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

/* Create a new PAP containing the given arguments plus a uint32 */
static inline PyonPtr
new_pap_u32(PyonPtr fun, int n_arguments, void *p_arguments, uint32_t arg)
{
  return new_pap_bytes(fun, n_arguments, p_arguments, &arg);
}

/* Create a new PAP containing the given arguments plus a float */
static inline PyonPtr
new_pap_f32(PyonPtr fun, int n_arguments, void *p_arguments, float arg)
{
  return new_pap_bytes(fun, n_arguments, p_arguments, &arg);
}

/*****************************************************************************/
/* Exported functions */

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
  pyon_dealloc(p);
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
	*(PyonPtr *)return_struct = new_pap_u32(obj, 0, NULL, arg);
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
      PyonPtr new_pap = new_pap_u32(fun, n_pap_arguments, firstarg_ptr,
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

/* Apply an object to a 32-bit float value */
PyonPtr
apply_f32_f(PyonPtr obj, float arg)
{
  PyonPtr ret;
  apply_f32(obj, arg, &ret);
  return ret;
}

void
apply_f32(PyonPtr obj, float arg, PyonPtr return_struct)
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
	*(PyonPtr *)return_struct = new_pap_f32(obj, 0, NULL, arg);
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
      PyonPtr new_pap = new_pap_f32(fun, n_pap_arguments, firstarg_ptr, arg);
      
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
 * block, plus some additional argument bytes.
 */
static PyonPtr
new_pap_bytes(PyonPtr fun, int n_arguments, void *p_arguments, void *arg_bytes)
{
  PyonPtr fun_info = OBJECT_INFO(fun);
  int arity = FUNINFO_ARITY(fun_info);

  /* Compute the size of the new PAP and the offset of the new field.
   * Increment reference counts of owned arguments. */
  int arguments_start = pap_firstargument_offset(OBJECT_INFO(fun));
  int arguments_size = 0;
  int index = 0;
  int new_argument_offset;
  uint8_t new_argument_tag;
  BEGIN_FOREACH_ARGUMENT(fun_info, p_arguments, 0, n_arguments + 1, tag, arg_ptr) {
    arguments_size = align(arguments_size, TAG_ALIGN(tag));

    if (index < n_arguments) {
      /* Increment the field if it's an owned reference */
      if (tag == OWNEDREF_TAG) incref(*(PyonPtr *)arg_ptr);
    }
    else {
      /* Increment the new argument if it's an owned reference */
      if (tag == OWNEDREF_TAG) incref(*(PyonPtr *)arg_bytes);

      /* Save the new argument's offset and tag */
      new_argument_offset = arguments_size;
      new_argument_tag = tag;
    }

    arguments_size += TAG_SIZE(tag);
  } END_FOREACH_ARGUMENT(tag, arg_ptr);

  /* Allocate memory */
  PyonPtr new_pap = pyon_alloc(arguments_start + arguments_size);

  /* Initialize the PAP */
  PAP_REFCT(new_pap) = 1;
  PAP_INFO(new_pap) = &pap_info;
  PAP_FUN(new_pap) = fun;
  incref(fun);
  PAP_NARGUMENTS(new_pap) = n_arguments + 1;
  
  /* Copy arguments to the new PAP */
  memcpy(PYON_OFF_PTR(new_pap, arguments_start), p_arguments, arguments_size);
  memcpy(PYON_OFF_PTR(new_pap, new_argument_offset), arg_bytes,
	 TAG_SIZE(new_argument_tag));
  return new_pap;
}
