/* Pool allocation.

This module defines memory pools, which are collections of dynamically allocated
objects that are freed in a single step.

To participate in a memory pool, an object needs to contain a 'PoolLink' and
have an associated 'PoolDescriptor' object.
*/

#ifndef _POOL_H
#define _POOL_H

typedef struct Pool Pool;
typedef struct PoolMembership PoolMembership;
typedef struct PoolDescriptor PoolDescriptor;

/* A memory pool. */
struct Pool {
  PoolMembership *first;	/* First member of pool, or NULL */
};

/* Create a memory pool. */
Pool *Pool_create(void);

/* Destroy a memory pool and its contents. */
void Pool_destroy(Pool *);

/* Allocate an object belonging to a memory bool.  The object's
 * 'PoolMembership' field is initialized.  The object is freed by
 * 'Pool_destroy'. */
void *Pool_malloc(Pool *, const PoolDescriptor *);

/* Memory pool membership information in a dynamically allocated object.
 * The struct is used by putting it as an object field. */
struct PoolMembership {
  PoolMembership *next;		    /* Next member of pool, or NULL */
  const PoolDescriptor *descriptor; /* Descriptor for this object type */
};

/* A descriptor for a pool-allocated data type.
 * Typically, a descriptor can be statically defined.
 *
 * Use 'offsetof' to compute the offset.  */
struct PoolDescriptor {
  unsigned int offset;		  /* Offset of the 'PoolMembership'
				   * field relative to the start of the
				   * object */
  unsigned int size;		  /* Object size */
  void (*finalize)(void *object); /* Object finalizer */
};

#endif
