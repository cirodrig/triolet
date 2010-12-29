/* The main Pyon/C API header file.
 */

#ifndef PYON_H
#define PYON_H

#include <inttypes.h>

/* Basic Pyon data types */
typedef int32_t PyonInt;
typedef float PyonFloat;
typedef int32_t PyonBool;
typedef void *PyonPtr;

typedef struct {
  PyonFloat real;
  PyonFloat imag;
} PyonComplexFloat;

typedef void (*PyonFreeFunc)(PyonPtr);

/* Pyon data structure interfaces */
#include "pyon_list.h"

#endif
