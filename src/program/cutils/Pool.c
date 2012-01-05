
#include <stdlib.h>
#include <stdio.h>
#include "cutils/Pool.h"

// define this macro to log pool-based memory allocation events
#undef LOG_POOL_ALLOCATION

Pool *
Pool_create(void)
{
  Pool *pool = malloc(sizeof(Pool));
  pool->first = NULL;
  return pool;
}

/* Destroy a memory pool and its contents. */
void Pool_destroy(Pool *pool)
{
  // destroy contents
  {
    PoolMembership *link = pool->first;
    while (link) {
      // get pointer to object
      void *obj = (void *)((char *)link - link->descriptor->offset);
      PoolMembership *next = link->next;

#ifdef LOG_POOL_ALLOCATION
      fprintf(stderr, "Pool D %p %p\n", (void *)pool, (void *)obj);
#endif
      // finalize and free object
      link->descriptor->finalize(obj);
      free(obj);

      // continue
      link = next;
    }
  }
  free(pool);
}

void *Pool_malloc(Pool *pool, const PoolDescriptor *type)
{
  void *obj = malloc(type->size);
  PoolMembership *link = (PoolMembership *)((char *)obj + type->offset);

#ifdef LOG_POOL_ALLOCATION
  fprintf(stderr, "Pool A %p %p\n", (void *)pool, (void *)obj);
#endif

  // Add to linked list
  link->next = pool->first;
  pool->first = link;

  // Initialize other fields
  link->descriptor = type;

  return obj;
}
