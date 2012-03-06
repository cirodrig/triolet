
#include <stdio.h>
#include <stdlib.h>
#include "Signature.h"

const PyonType *
PyonType_Int(void)
{
  PyonType *p = malloc(sizeof(PyonType));
  *p = (PyonType){.tag = PyonIntTag};
  return p;
}

const PyonType *
PyonType_Float(void)
{
  PyonType *p = malloc(sizeof(PyonType));
  *p = (PyonType){.tag = PyonFloatTag};
  return p;
}

const PyonType *
PyonType_Bool(void)
{
  PyonType *p = malloc(sizeof(PyonType));
  *p = (PyonType){.tag = PyonBoolTag};
  return p;
}

const PyonType *
PyonType_NoneType(void)
{
  PyonType *p = malloc(sizeof(PyonType));
  *p = (PyonType){.tag = PyonNoneTypeTag};
  return p;
}

const PyonType *
PyonType_Tuple(int size)
{
  PyonType *p = malloc(sizeof(PyonType));
  const PyonType **members = malloc(size * sizeof (const PyonType *));
  *p = (PyonType){.tag = PyonTupleTypeTag};
  p->tuple.count = size;
  p->tuple.elems = members;
  return p;
}

/* Create a list type.  Steals ownership of 'elem'. */
const PyonType *
PyonType_List(const PyonType *elem)
{
  PyonType *p = malloc(sizeof(PyonType));
  *p = (PyonType){.tag = PyonListTypeTag};
  p->list.elem = elem;
  return p;
}

/* Create an array type.  Steals ownership of 'elem'. */
const PyonType *
PyonType_Array(int dim, int boxed, const PyonType *elem)
{
  PyonType *p = malloc(sizeof(PyonType));
  *p = (PyonType){.tag = PyonArrayTypeTag};
  p->array.dimensionality = dim;
  p->array.boxed = boxed;
  p->array.elem = elem;
  return p;
}

const PyonType *
PyonType_duplicate(const PyonType *p)
{
  switch(p->tag) {
  case PyonIntTag: return PyonType_Int();
  case PyonFloatTag: return PyonType_Float();
  case PyonBoolTag: return PyonType_Bool();
  case PyonNoneTypeTag: return PyonType_NoneType();
  case PyonTupleTypeTag:
    {
      int i;
      int count = p->tuple.count;
      const PyonType **elems = p->tuple.elems;
      const PyonType *t = PyonType_Tuple(count);
      for (i = 0; i < count; i++) t->tuple.elems[i] = elems[i];
      return t;
    }
  case PyonListTypeTag: return PyonType_List(PyonType_duplicate(p->list.elem));
  case PyonArrayTypeTag:
    return PyonType_Array(p->array.dimensionality,
                          p->array.boxed,
                          PyonType_duplicate(p->array.elem));
  default:
    fprintf(stderr, "PyonType_duplicate: Invalid argument\n");
    exit(-1);
  }
}

void
PyonType_destroy(const PyonType *p)
{
  switch (p->tag) {
  case PyonIntTag:
  case PyonFloatTag:
  case PyonBoolTag:
  case PyonNoneTypeTag:
    free((void *)p);
    return;
  case PyonTupleTypeTag:
    {
      int i;
      for (i = 0; i < p->tuple.count; i++)
	PyonType_destroy(p->tuple.elems[i]);
      free((void *)p);
      return;
    }
  case PyonListTypeTag:
    PyonType_destroy(p->list.elem);
    free((void *)p);
    return;
  case PyonArrayTypeTag:
    PyonType_destroy(p->array.elem);
    free((void *)p);
    return;
  default:
    fprintf(stderr, "PyonType_destroy: Invalid argument\n");
    exit(-1);
  }
}

const PyonTypes *
PyonTypes_duplicate(const PyonTypes *other)
{
  int size = other->count;
  const PyonTypes *p = PyonTypes_alloc(size);

  {
    int i;
    const PyonType **elems = p->elems;
    for (i = 0; i < size; i++)
      elems[i] = PyonType_duplicate(other->elems[i]);
  }
  return p;
}

const PyonTypes *
PyonTypes_alloc(int size)
{
  const PyonType **elems = malloc(size * sizeof(const PyonType *));
  PyonTypes *p = malloc(sizeof(PyonTypes));
  *p = (PyonTypes){.count = size, .elems = elems};
  return p;
}

void
PyonTypes_destroy(const PyonTypes *p)
{
  int i;
  const PyonType **elems = p->elems;
  for (i = 0; i < p->count; i++)
    PyonType_destroy(elems[i]);
  free((void *)p);
}

const PyonSignature *
PyonSignature_create (const PyonTypes *parameter_types,
		      const PyonType *return_type)
{
  PyonSignature *p = malloc(sizeof(PyonSignature));
  *p = (PyonSignature){.parameterTypes = parameter_types,
		       .returnType = return_type};
  return p;
}

void PyonSignature_destroy(const PyonSignature *p) {
  PyonTypes_destroy(p->parameterTypes);
  PyonType_destroy(p->returnType);
  free((void *)p);
}
