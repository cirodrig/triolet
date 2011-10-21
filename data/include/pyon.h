/* The main Pyon/C API header file.
 */

#ifndef PYON_H
#define PYON_H

#ifdef __cplusplus
extern "C" {
#endif

#include <inttypes.h>
#include <gc.h>

/* Basic Pyon data types */
typedef int PyonInt;
typedef unsigned int PyonUInt;
typedef float PyonFloat;
typedef int PyonBool;
typedef void *PyonPtr;

typedef struct {
  void *function;
  void *captured;
} PyonClosure;

typedef struct {
  PyonFloat real;
  PyonFloat imag;
} PyonComplexFloat;

/* Pyon data structure interfaces */
#include "pyon_list.h"
#include "pyon_matrix.h"

static inline void Pyon_init(void) {
  /* N.B. the GC must be initialized from the main program, not from a library.
   * That is why this code is in a header file. */
  GC_INIT();
}

#ifdef __cplusplus
}
#endif

#endif
