
#include <inttypes.h>

/* Very low-level pointer manipulation.
 * Add a byte offset to a pointer. */
#define PYON_OFF(base, offset) ((PyonPtr)((char *)(base) + (offset)))

#define PYON_OFF_TYPE(base, offset, type) ((type *)((char *)(base) + (offset)))

#define PYON_OFF_U8(base, offset) PYON_OFF_TYPE(base, offset, uint8_t)
#define PYON_OFF_I8(base, offset) PYON_OFF_TYPE(base, offset, int8_t)
#define PYON_OFF_U16(base, offset) PYON_OFF_TYPE(base, offset, uint16_t)
#define PYON_OFF_I16(base, offset) PYON_OFF_TYPE(base, offset, int16_t)
#define PYON_OFF_U32(base, offset) PYON_OFF_TYPE(base, offset, uint32_t)
#define PYON_OFF_I32(base, offset) PYON_OFF_TYPE(base, offset, int32_t)
#define PYON_OFF_U64(base, offset) PYON_OFF_TYPE(base, offset, uint64_t)
#define PYON_OFF_I64(base, offset) PYON_OFF_TYPE(base, offset, int64_t)
#define PYON_OFF_F32(base, offset) PYON_OFF_TYPE(base, offset, float)
#define PYON_OFF_F64(base, offset) PYON_OFF_TYPE(base, offset, double)
#define PYON_OFF_PTR(base, offset) PYON_OFF_TYPE(base, offset, PyonPtr)

/* A pointer to a Pyon objects */
typedef void *PyonPtr;

/* An object's 'free' method */
typedef void (*PyonFreeFunc)(PyonPtr);

static inline int32_t pyon_atomic_add_s(int32_t *p, int delta)
{
  int32_t old = *p;
  *p += delta;
  return old;
}

/* The general-purpose memory allocator interface */
PyonPtr alloc(uint32_t);
void dealloc(PyonPtr);

/* How to deallocate a global closure */
void dealloc_global(PyonPtr);

/* How to copy small values */
void copy4(PyonPtr src, PyonPtr dst);

/* Object deallocation functions */
void free_pap(PyonPtr);

/* Entry points to Pyon functions */
void dealloc_exact_entry(PyonPtr closure, PyonPtr arg);
void dealloc_inexact_entry(PyonPtr closure, PyonPtr args, PyonPtr ret);
void copy4_exact_entry(PyonPtr closure, PyonPtr src, PyonPtr dst);
void copy4_inexact_entry(PyonPtr closure, PyonPtr args, PyonPtr ret);

/* Apply functions */
PyonPtr
apply_i32_f(PyonPtr obj, uint32_t arg);
void
apply_i32(PyonPtr obj, uint32_t arg, PyonPtr return_struct);

PyonPtr
apply_f32_f(PyonPtr obj, float arg);
void
apply_f32(PyonPtr obj, float arg, PyonPtr return_struct);

/*****************************************************************************/
/* Opaque data */

extern struct {} pap_info;
extern struct {} global_closure_info;

extern struct {} dealloc_closure;
extern struct {} copy4_closure;
