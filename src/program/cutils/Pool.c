
#include <stdlib.h>
#include "cutils/Pool.h"

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

  // Add to linked list
  link->next = pool->first;
  pool->first = link;

  // Initialize other fields
  link->descriptor = type;

  return obj;
}
