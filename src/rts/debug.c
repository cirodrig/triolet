
#include <stdlib.h>
#include <stdio.h>
#include "triolet.h"

/* Debugging routines that can be called from pyon */

void triolet_db_word(uint32_t w) {
  fprintf(stderr, "triolet_db: %u\n", w);
}

void triolet_db_int(int32_t i) {
  fprintf(stderr, "triolet_db: %d\n", i);
}

void triolet_db_float(float f) {
  fprintf(stderr, "triolet_db: %g\n", f);
}

void triolet_db_pointer(void *p) {
  fprintf(stderr, "triolet_db: %p\n", p);
}

void triolet_exit(int arg) {
  exit(arg);
}
