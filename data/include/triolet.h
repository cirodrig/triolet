/* The main Triolet/C API header file.
 */

#ifndef TRIOLET_H
#define TRIOLET_H

#ifdef __cplusplus
extern "C" {
#endif

#include <inttypes.h>
#include <gc.h>

/* Basic Triolet data types */
typedef int TrioletInt;
typedef unsigned int TrioletUInt;
typedef float TrioletFloat;
typedef int TrioletBool;
typedef void *TrioletPtr;

typedef struct {
  void *function;
  void *captured;
} TrioletClosure;

/* Triolet data structure interfaces */
#include "triolet_list.h"
#include "triolet_matrix.h"

static inline void Triolet_init(void) {
  /* N.B. the GC must be initialized from the main program, not from a library.
   * That is why this code is in a header file. */
  GC_INIT();
}

#ifdef __cplusplus
}
#endif

#endif
