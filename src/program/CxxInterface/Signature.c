
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
PyonType_duplicate(const PyonType *p)
{
  switch(p->tag) {
  case PyonIntTag: return PyonType_Int();
  case PyonFloatTag: return PyonType_Float();
  case PyonBoolTag: return PyonType_Bool();
  case PyonNoneTypeTag: return PyonType_NoneType();
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
