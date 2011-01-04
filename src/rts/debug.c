
#include <stdlib.h>
#include <stdio.h>
#include "pyon.h"

/* Debugging routines that can be called from pyon */

void pyon_db_word(uint32_t w) {
  fprintf(stderr, "pyon_db: %u\n", w);
}

void pyon_db_int(int32_t i) {
  fprintf(stderr, "pyon_db: %d\n", i);
}

void pyon_db_pointer(void *p) {
  fprintf(stderr, "pyon_db: %p\n", p);
}
