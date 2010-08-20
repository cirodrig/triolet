/*
 * Memory management
 */

/* The general-purpose memory allocator interface */
PyonPtr pyon_alloc(uint32_t);
void pyon_dealloc(PyonPtr);

#if 0
/* How to copy small values */
void pyon_copy4(PyonPtr src, PyonPtr dst);

/* How to deallocate a global closure */
void dealloc_global_closure(PyonPtr);

/* Entry points to Pyon functions */
void dummy_finalize_exact_entry(PyonPtr closure, PyonPtr arg);
void dummy_finalize_inexact_entry(PyonPtr closure, PyonPtr args, PyonPtr ret);
void dealloc_exact_entry(PyonPtr closure, PyonPtr arg);
void dealloc_inexact_entry(PyonPtr closure, PyonPtr args, PyonPtr ret);
void copy4_exact_entry(PyonPtr closure, PyonPtr src, PyonPtr dst);
void copy4_inexact_entry(PyonPtr closure, PyonPtr args, PyonPtr ret);
#endif

/* Decrement an object's reference count, and free it if the reference count
 * falls to zero. */
static inline void
decref(PyonPtr p)
{
  uint32_t rc = __sync_fetch_and_add(&OBJECT_REFCT(p), -1);
  if (rc == 1) {
    PyonFreeFunc free_func = INFO_FREE(OBJECT_INFO(p));
    free_func(p);
  }
}

/* Increment an object's reference count. */
static inline void __attribute__((always_inline))
incref(PyonPtr p)
{
  __sync_fetch_and_add(&OBJECT_REFCT(p), 1);
}

