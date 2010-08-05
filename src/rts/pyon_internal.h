
#ifndef _PYON_INTERNAL_H
#define _PYON_INTERNAL_H

#include "pyon.h"
#include "layout.h"
#include "struct.h"
#include "memory.h"
#include "apply.h"

/* ENTER_INEXACT(info)(fun, args, ret)
 * Call the inexact entry point of a function given its info table */
#define ENTER_INEXACT(info) \
  ((void (*)(PyonPtr, PyonPtr, PyonPtr))&FUNINFO_INEXACT(info))

/* ENTER_EXACT(info, fun, return_type, type_list, argument_list)
 * Call the exact entry point of a function given its info table.
 * The type list and argument list must be in parentheses. */
#define ENTER_EXACT(info, fun, return_type, type_list, argument_list)	\
  (((return_type (*)type_list)&FUNINFO_EXACT(info))argument_list)

/* CALL_EXACT(fun, return_type, type_list, argument_list)
 * Call the exact entry point of a function closure */
#define CALL_EXACT(fun, return_type, type_list, argument_list) \
  ENTER_EXACT(OBJECT_INFOTABLE(fun),fun, return_type, type_list, argument_list)

#endif
