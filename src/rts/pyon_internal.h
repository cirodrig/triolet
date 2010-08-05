
#ifndef _PYON_INTERNAL_H
#define _PYON_INTERNAL_H

#include "pyon.h"
#include "layout.h"
#include "struct.h"
#include "memory.h"
#include "apply.h"

/* ENTER_INEXACT(info)(fun, args, ret)
 * Call the inexact entry point of a function */
#define ENTER_INEXACT(info) \
  ((void (*)(PyonPtr, PyonPtr, PyonPtr))&FUNINFO_INEXACT(info))

#endif
