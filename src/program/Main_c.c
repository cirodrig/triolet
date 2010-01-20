
#include <Python.h>
#include <HsFFI.h>

#include "PythonInterface/HsObject.h"

/* Defined in Driver.hs */
extern PyObject *
parsePyonFile(const char *, PyObject *, int);

/* Python wrapper around parsePyonFile */ 
static PyObject *
parsePyonFile_wrapper(PyObject *self, PyObject *args)
{
  const char *filename;
  PyObject *globals_list;
  int next_id;

  if (PyArg_ParseTuple(args, "sO!i",
		       &filename, &PyList_Type, &globals_list, &next_id) == 0)
    return NULL;

  return parsePyonFile((void *)filename, globals_list, next_id);
}

static struct PyMethodDef haskell_methods[] = {
  { "parse",
    parsePyonFile_wrapper,
    METH_VARARGS,
    "parse(filename) -> (counter, module)\n"
    "Parse a Pyon source file.  Returns the first unassigned variable ID\n"
    "and the parsed module."
  },
  { NULL }
};

extern void
createHaskellModule(void)
{
  PyObject *haskell_module = Py_InitModule("haskell", haskell_methods);

  if (PyType_Ready(&HsObject_type) < 0) return;
  PyModule_AddObject(haskell_module, "HsObject", (PyObject *)&HsObject_type);
}

