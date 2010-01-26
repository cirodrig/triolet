
#include <Python.h>
#include <HsFFI.h>

/* A Python reference to a Haskell value.
 *
 * This reference stores the value and its Haskell type.
 * The Haskell value may be relased when it is no longer needed, in which
 * case both pointers are NULL. 
 */
struct HsObject
{
  PyObject_HEAD
  HsStablePtr value;		/* Pointer to data */
  HsStablePtr type_rep;		/* Haskell type representation */
};

struct HsObject*
HsObject_new(HsStablePtr value, HsStablePtr type_rep);

/* The type object for HsObject types */
PyTypeObject HsObject_type;

