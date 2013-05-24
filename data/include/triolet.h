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

extern int Triolet_is_initialized;
extern void Triolet_init_real(int *argc, char ***argv);

static inline void Triolet_init(int *argc, char ***argv) {
  /* N.B. the GC must be initialized from the main program, not from a library.
   * That is why this code is in a header file. */
  GC_INIT();

  if (!Triolet_is_initialized) Triolet_init_real(argc, argv);
}

#ifdef __cplusplus
}
#endif

#endif
