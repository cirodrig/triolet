
#include <Python.h>
#include <HsFFI.h>

/* Defined in Driver.hs */
extern PyObject *
parsePyonFile(const char *);

/* Python wrapper around parsePyonFile */ 
static PyObject *
parsePyonFile_wrapper(PyObject *self, PyObject *args)
{
  const char *filename;
  if (PyArg_ParseTuple(args, "s", &filename) == 0)
    return NULL;
  return parsePyonFile((void *)filename);
}

static struct PyMethodDef haskell_methods[] = {
  { "parse",
    parsePyonFile_wrapper,
    METH_VARARGS,
    "Parse a Pyon source file"
  },
  { NULL }
};

extern void
createHaskellModule(void)
{
  Py_InitModule("haskell", haskell_methods);
}

