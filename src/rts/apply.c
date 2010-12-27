
#include "arch/apply_data_x86.c"

#if 0
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "pyon_internal.h"

static inline int
funinfo_firstargument_offset(void);

static inline int
pap_firstargument_offset(void);

static inline PyonPtr
new_pap_u32(PyonPtr, int, void *, uint32_t);

static inline PyonPtr
new_pap_f32(PyonPtr, int, void *, float);

static PyonPtr
new_pap_bytes(PyonPtr fun,
	      int n_arguments,
	      void *p_arguments,
	      int new_arg_size,
	      void *new_arg_bytes);

static void
call_pap(PyonPtr pap, PyonPtr return_struct);

/* Get the offset of the first argument type tag in a function info table */
static inline int __attribute__((always_inline))
funinfo_firstargument_offset(void)
{
  /* Get offset of the last fixed field */
  int offset = (char *)&FUNINFO_INEXACT(NULL) - (char *)NULL;

  /* Get offset of the first argument tag */
  return FIELD_START_OFF(offset + sizeof(FUNINFO_INEXACT(NULL)), uint8_t);
}

/* Get the offset of the first argument in a PAP. */
static inline int __attribute__((always_inline))
pap_firstargument_offset(void)
{
  /* Get offset of the last fixed field */
  int offset = (char *)&PAP_NARGUMENTS(NULL) - (char *)NULL;

  /* Add size of field */
  offset += sizeof(PAP_NARGUMENTS(NULL));
  
  /* Add padding */
  return align(offset, DYN_SCALAR_ALIGNMENT);
}

/*****************************************************************************/
/* Exported functions */

/* The deallocation function for a partial application.
 *
 * Release the reference to the function and arguments.  Then, deallocate the
 * PAP object.
 *
 * This code must remain consistent with the code generator that creates PAPs.
 */
void free_pap(PyonPtr pap)
{
  /* Find the function's info table */
  PyonPtr fun = PAP_FUN(pap);
  PyonPtr fun_info = OBJECT_INFO(fun);

  /* Release the function */
  decref(fun);

  /* Process each argument.
   * Number of arguments must be >= 1 and <= FUNINFO_ARITY(info_ptr). */
  {
    int nargs;
    uint8_t *current_tag_ptr =
      PYON_OFF_U8(fun_info, funinfo_firstargument_offset());
    int current_arg_off = pap_firstargument_offset();

    for (nargs = PAP_NARGUMENTS(pap); nargs; nargs--) {
      /* Get tag of current argument */
      uint8_t current_tag = *current_tag_ptr;

      /* Release owned references */
      if(current_tag == OWNED_REF_BITS_TAG) {
	PyonPtr arg = *PYON_OFF_PTR(pap, current_arg_off);
	decref(arg);
      }

      /* Go to next position */
      current_tag_ptr++;
      current_arg_off += BITS_TAG_SIZE(current_tag);
    }
  }

  /* Deallocate the PAP */
  pyon_dealloc(pap);
}

/* Apply an object to an owned pointer value */
PyonPtr
apply_o_f(PyonPtr obj, PyonPtr arg)
{
  incref(arg);
  /* Assumes sizeof(pointer) == sizeof(uint32_t) */
  return (PyonPtr)apply_i32_f(obj, (uint32_t)arg);
}

void
apply_o(PyonPtr obj, PyonPtr arg, PyonPtr return_struct)
{
  incref(arg);
  /* Assumes sizeof(pointer) == sizeof(uint32_t) */
  apply_i32(obj, (uint32_t)arg, return_struct);
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
	{
	  void (*inexact_entry)(PyonPtr, PyonPtr, PyonPtr) =
	    FUNINFO_INEXACT(info);
	  inexact_entry(obj, &arg, return_struct);
	  break;
	}
      default:
	/* Create and return a PAP */
	*(PyonPtr *)return_struct = new_pap_bytes(obj, 0, NULL,
						  sizeof(arg),
						  &arg);
	break;
      }
    }
    break;
  case PAP_TAG:
    {
      PyonPtr fun = PAP_FUN(obj);
      PyonPtr fun_info = OBJECT_INFO(fun);
      int arity = FUNINFO_ARITY(fun_info);
      int n_pap_arguments = PAP_NARGUMENTS(obj);
      PyonPtr new_pap;

      /* Create a new PAP that combines all arguments */
      {
	int firstarg_offset = pap_firstargument_offset();
	void *firstarg_ptr = PYON_OFF_PTR(obj, firstarg_offset);
	new_pap = new_pap_bytes(fun, n_pap_arguments, firstarg_ptr,
				sizeof(arg), &arg);
      }

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
	{
	  void (*inexact_entry)(PyonPtr, PyonPtr, PyonPtr) =
	    FUNINFO_INEXACT(info);
	  inexact_entry(obj, &arg, return_struct);
	  break;
	}
	break;
      default:
	/* Create and return a PAP */
	*(PyonPtr *)return_struct = new_pap_bytes(obj, 0, NULL,
						  sizeof(arg), &arg);
	break;
      }
    }
    break;
  case PAP_TAG:
    {
      PyonPtr fun = PAP_FUN(obj);
      PyonPtr fun_info = OBJECT_INFO(fun);
      int arity = FUNINFO_ARITY(fun_info);
      int n_pap_arguments = PAP_NARGUMENTS(obj);
      PyonPtr new_pap;

      /* Create a new PAP that combines all arguments */
      {
	int firstarg_offset = pap_firstargument_offset();
	void *firstarg_ptr = PYON_OFF_PTR(obj, firstarg_offset);
	new_pap = new_pap_bytes(fun, n_pap_arguments, firstarg_ptr,
				sizeof(arg), &arg);
      }

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

  int firstarg_offset = pap_firstargument_offset();
  void *firstarg_ptr = PYON_OFF_PTR(pap, firstarg_offset);

  /* Call the entry point with the function closure and arguments */
  void (*inexact_entry)(PyonPtr, PyonPtr, PyonPtr) = FUNINFO_INEXACT(fun_info);
  inexact_entry(fun, firstarg_ptr, return_struct);
}

/* Create a new PAP consisting of the function applied to the given argument
 * block, plus an extra argument with the given size and alignment.
 */
static PyonPtr
new_pap_bytes(PyonPtr fun,
	      int n_arguments,
	      void *p_arguments,
	      int new_arg_size,
	      void *new_arg_bytes)
{
  PyonPtr fun_info = OBJECT_INFO(fun);
  int arity = FUNINFO_ARITY(fun_info);

  /* Compute the size of the new PAP arguments and the offset of the new field.
   * Size may include padding bytes at the beginning.
   * Increment reference counts of owned arguments.
   */
  int arguments_size;		/* Size of current arguments */
  int new_arg_offset;		/* Offset of new argument relative to
				 * start of argument block */
  int combined_arguments_size;	/* Size after adding new argument */
  {
    int nargs;
    uint8_t *current_tag_ptr =
      PYON_OFF_U8(fun_info, funinfo_firstargument_offset());
    int current_arg_off = pap_firstargument_offset();

    for (nargs = n_arguments; nargs; nargs--) {
      /* Get tag and argument */
      uint8_t current_tag = *current_tag_ptr;

      /* Acquire owned references */
      if(current_tag == OWNED_REF_BITS_TAG) {
	PyonPtr arg = *PYON_OFF_PTR(p_arguments,
				    current_arg_off - pap_firstargument_offset());
	incref(arg);
      }

      /* Go to next position */
      current_tag_ptr++;
      current_arg_off += BITS_TAG_SIZE(current_tag);
    }
    arguments_size = current_arg_off - pap_firstargument_offset();
    new_arg_offset = current_arg_off;
    current_arg_off += new_arg_size;
    combined_arguments_size = current_arg_off - pap_firstargument_offset();
  }

  /* Allocate memory */
  PyonPtr new_pap =
    pyon_alloc(pap_firstargument_offset() + combined_arguments_size);

  /* Initialize the PAP */
  PAP_REFCT(new_pap) = 1;
  PAP_INFO(new_pap) = &pap_info;
  PAP_FUN(new_pap) = fun;
  incref(fun);
  PAP_NARGUMENTS(new_pap) = n_arguments + 1;
  
  /* Copy arguments to the new PAP */
  memcpy(PYON_OFF_PTR(new_pap, pap_firstargument_offset()),
	 p_arguments, arguments_size);
  memcpy(PYON_OFF_PTR(new_pap, new_arg_offset), new_arg_bytes, new_arg_size);
  return new_pap;
}
#endif
