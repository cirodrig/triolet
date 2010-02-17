
#include "HsObject.h"
#include "PythonInterface/HsObject_stub.h"

/* Create a new reference to a Haskell value.  The second parameter should
 * be the value's type.  Ownership of the two
 * HsStablePtr parameters is stolen.
 */
struct HsObject*
HsObject_new(HsStablePtr value, HsStablePtr type_rep)
{
  struct HsObject *obj = PyObject_New(struct HsObject, &HsObject_type);
  obj->value = value;
  obj->type_rep = type_rep;

  return obj;
}

/* Free the reference, but do not deallocate the Python object */
static PyObject *
HsObject_release(struct HsObject *self, PyObject *args)
{
  /* No arguments (METH_NOARGS) */

  if (self->value) {
    hs_free_stable_ptr(self->value);
    hs_free_stable_ptr(self->type_rep);
    self->value = NULL;
    self->type_rep = NULL;
  }

  Py_RETURN_NONE;
}  

/* Compare the two object references.  The comparsion is an arbitrary total
 * ordering. */
static int
HsObject_compare(struct HsObject *obj1, struct HsObject *obj2)
{
  if (obj1->value < obj2->value) return -1;
  if (obj1->value == obj2->value) return 0;
  return 1;
}

/* Free the reference and the Python object */
static void
HsObject_dealloc(struct HsObject *obj)
{
  if (obj->value) {
    hs_free_stable_ptr(obj->value);
    hs_free_stable_ptr(obj->type_rep);
  }
  PyObject_Del(obj);
}

static PyObject *
HsObject_str(struct HsObject *self)
{
  /* String object used as name of empty references */
  static PyObject *empty_ref_str = NULL;

  if (self->value) {
    /* Get description of type */
    char *type_name = hsObject_getTypeString(self);

    /* Create description of object */
    PyObject *ret = PyString_FromFormat("<hs ref to %s at %p>",
					type_name, (void *)self->value);

    free(type_name);
    return ret;
  }
  /* else */
  /* Ensure that empty_ref_str is initialized */
  if (empty_ref_str == NULL) {
    empty_ref_str = PyString_FromString("<hs ref to nil>");
  }
  Py_INCREF(empty_ref_str);
  return empty_ref_str;
}

static struct PyMethodDef HsObject_methods[] = {
  { "release", (binaryfunc)&HsObject_release, METH_NOARGS,
    "Release this reference to the Haskell value."
  },
  { NULL, NULL, 0, NULL}
};

PyTypeObject HsObject_type = {
  PyObject_HEAD_INIT(NULL)
  0,				/*ob_size*/
  "HsObject",			/*tp_name*/
  sizeof(struct HsObject),	/*tp_basicsize*/
  0,				/*tp_itemsize*/
  (destructor)&HsObject_dealloc, /*tp_dealloc*/
  0,				/*tp_print*/
  0,				/*tp_getattr*/
  0,				/*tp_setattr*/
  (cmpfunc)&HsObject_compare,	/*tp_compare*/
  0,				/*tp_repr*/
  0,				/*tp_as_number*/
  0,				/*tp_as_sequence*/
  0,				/*tp_as_mapping*/
  0,				/*tp_hash */
  0,				/*tp_call*/
  (reprfunc)HsObject_str,	/*tp_str*/
  0,				/*tp_getattro*/
  0,				/*tp_setattro*/
  0,				/*tp_as_buffer*/
  Py_TPFLAGS_DEFAULT,		/*tp_flags*/
  "Haskell object references",	/* tp_doc */
  0,				/* tp_traverse */
  0,				/* tp_clear */
  0,				/* tp_richcompare */
  0,				/* tp_weaklistoffset */
  0,				/* tp_iter */
  0,				/* tp_iternext */
  HsObject_methods,		/* tp_methods */
  0,				/* tp_members */
  0,				/* tp_getset */
  0,				/* tp_base */
  0,				/* tp_dict */
  0,				/* tp_descr_get */
  0,				/* tp_descr_set */
  0,				/* tp_dictoffset */
  0,				/* tp_init */
  0,				/* tp_alloc */
  0,				/* tp_new */
};

