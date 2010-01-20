
#include <Python.h>

int
PyList_Check_Function(PyObject *obj)
{
  return PyList_Check(obj);
}

int
PyTuple_Check_Function(PyObject *obj)
{
  return PyTuple_Check(obj);
}
