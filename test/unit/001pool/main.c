// Very simple pool allocation tests.
// This file is an example of how to use the test case infrastructure.

#include <stddef.h>
#include <stdlib.h>
#include "cutils/Pool.h"

struct mystruct {
  double d;
  char *name;
  PoolMembership pool;
};

void finalize_mystruct(struct mystruct *p) {
  free(p->name);
}

PoolDescriptor mystruct_alloc = {
  offsetof(struct mystruct, pool),
  sizeof(struct mystruct),
  (void (*)(void *))&finalize_mystruct
};

int main()
{
  Pool *p = Pool_create();

  struct mystruct *s1 = Pool_malloc(p, &mystruct_alloc);
  struct mystruct *s2 = Pool_malloc(p, &mystruct_alloc);

  s1->name = malloc(10);
  s2->name = malloc(20);

  Pool_destroy(p);
  return 0;
}
