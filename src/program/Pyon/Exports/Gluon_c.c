
#include <HsFFI.h>

// Undefine this symbol, which is redefined in Python.h, to eliminate a warning
#ifdef _POSIX_C_SOURCE
#undef _POSIX_C_SOURCE
#endif

#include <Python.h>

#include "PythonInterface/HsObject.h"
#include "Pyon/Exports/Gluon_stub.h"

/*****************************************************************************/
/* C wrappers for argument marshaling */

static PyObject *
pgmLabel(PyObject *self, PyObject *args)
{
  char *module_name;
  char *entity_name;

  if (!PyArg_ParseTuple(args, "ss", &module_name, &entity_name))
    return NULL;

  return gluon_pgmLabel(module_name, entity_name);
}

static PyObject *
mkVariable(PyObject *self, PyObject *args)
{
  int id;
  PyObject *label;
  PyObject *level;

  if (!PyArg_ParseTuple(args, "iO!O!",
			&id, &HsObject_type, &label, &HsObject_type, &level))
    return NULL;

  return gluon_mkVariable(id, label, level);
}

static PyObject *
mkNewVariable(PyObject *self, PyObject *args)
{
  PyObject *label;
  PyObject *level;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &label, &HsObject_type, &level))
    return NULL;

  return gluon_mkNewVariable(label, level);
}

static PyObject *
mkAnonymousVariable(PyObject *self, PyObject *args)
{
  int id;
  PyObject *level;

  if (!PyArg_ParseTuple(args, "iO!",
			&id, &HsObject_type, &level))
    return NULL;

  return gluon_mkAnonymousVariable(id, level);
}

static PyObject *
mkNewAnonymousVariable(PyObject *self, PyObject *args)
{
  PyObject *level;

  if (!PyArg_ParseTuple(args, "O!",
		        &HsObject_type, &level))
    return NULL;

  return gluon_mkNewAnonymousVariable(level);
}

static PyObject *
delayedType(PyObject *self, PyObject *arg)
{
  return gluon_delayedType(arg);
}

static PyObject *
Binder_plain(PyObject *self, PyObject *args)
{
  PyObject *var;
  PyObject *ty;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &var, &HsObject_type, &ty))
    return NULL;

  return gluon_Binder_plain(var, ty);
}

static PyObject *
Binder2_plain(PyObject *self, PyObject *args)
{
  PyObject *var;		/* Variable or None */
  PyObject *ty;

  if (!PyArg_ParseTuple(args, "OO!",
			&var, &HsObject_type, &ty))
    return NULL;

  return gluon_Binder2_plain(var, ty);
}

static PyObject *
mkAppE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *operator;
  PyObject *arguments;

  if (!PyArg_ParseTuple(args, "O!O!O",
			&HsObject_type, &pos, &HsObject_type, &operator, &arguments))
    return NULL;

  return gluon_mkAppE(pos, operator, arguments);
}

static PyObject *
mkConAppE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *operator;
  PyObject *arguments;

  if (!PyArg_ParseTuple(args, "O!O!O",
			&HsObject_type, &pos, &HsObject_type, &operator, &arguments))
    return NULL;

  return gluon_mkConAppE(pos, operator, arguments);
}

static PyObject *
mkLamE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *var;
  PyObject *type;
  PyObject *body;

  if (!PyArg_ParseTuple(args, "O!O!O!O!",
			&HsObject_type, &pos, &HsObject_type, &var,
			&HsObject_type, &type, &HsObject_type, &body))
    return NULL;

  return gluon_mkLamE(pos, var, type, body);
}

static PyObject *
mkFunE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *isLin;
  PyObject *var;
  PyObject *dom;
  PyObject *rng;

  if (!PyArg_ParseTuple(args, "O!O!O!O!O!",
			&HsObject_type, &pos, &PyBool_Type, &isLin,
			&HsObject_type, &var, &HsObject_type, &dom,
			&HsObject_type, &rng))
    return NULL;

  return gluon_mkFunE(pos, isLin == Py_True, var, dom, rng);
}

static PyObject *
mkArrowE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *isLin;
  PyObject *dom;
  PyObject *rng;

  if (!PyArg_ParseTuple(args, "O!O!O!O!",
			&HsObject_type, &pos, &PyBool_Type, &isLin,
			&HsObject_type, &dom, &HsObject_type, &rng))
    return NULL;

  return gluon_mkArrowE(pos, isLin == Py_True, dom, rng);
}

static PyObject *
mkVarE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *v;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &pos, &HsObject_type, &v))
    return NULL;

  return gluon_mkVarE(pos, v);
}

static PyObject *
mkConE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *c;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &pos, &HsObject_type, &c))
    return NULL;

  return gluon_mkConE(pos, c);
}

static PyObject *
mkTupE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *t;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &pos, &HsObject_type, &t))
    return NULL;

  return gluon_mkTupE(pos, t);
}

static PyObject *
mkTupTyE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *t;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &pos, &HsObject_type, &t))
    return NULL;

  return gluon_mkTupTyE(pos, t);
}

static PyObject *
mkLitE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *t;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &pos, &HsObject_type, &t))
    return NULL;

  return gluon_mkLitE(pos, t);
}

static PyObject *
Tuple_Core_cons(PyObject *self, PyObject *args)
{
  PyObject *param;
  PyObject *tail;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &param, &HsObject_type, &tail))
    return NULL;

  return gluon_Tuple_Core_cons(param, tail);
}

static PyObject *
Sum_Core_cons(PyObject *self, PyObject *args)
{
  PyObject *param;
  PyObject *tail;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &param, &HsObject_type, &tail))
    return NULL;

  return gluon_Sum_Core_cons(param, tail);
}

static PyObject *
isExp(PyObject *self, PyObject *arg)
{
  if (!PyObject_IsInstance(arg, (PyObject *)&HsObject_type)) {
    Py_RETURN_FALSE;
  }

  int rc = gluon_isExp(arg);
  return PyBool_FromLong((long)rc);
}

/*****************************************************************************/
/* Module definition */

static struct PyMethodDef gluon_methods[] = {
  {"pgmLabel", pgmLabel, METH_VARARGS,
   "Create a label value, given a module name and entity name."},
  {"mkVariable", mkVariable, METH_VARARGS,
   "Create a variable given an ID, label, and level."},
  {"mkNewVariable", mkNewVariable, METH_VARARGS,
   "Create a new variable given a label and level.  The variable is assigned\n"
   "a fresh ID."},
  {"mkAnonymousVariable", mkAnonymousVariable, METH_VARARGS,
   "Create an anonymous variable given an ID, and level."},
  {"mkNewAnonymousVariable", mkNewAnonymousVariable, METH_VARARGS,
   "Create a new variable given a level.  The variable is assigned\n"
   "a fresh ID."},
  {"delayedType", delayedType, METH_O,
   "Create a delayed type expression.  The parameter should be a\n"
   "zero-argument function.  It will be run when evaluation is forced."},
  {"Binder_plain", Binder_plain, METH_VARARGS,
   "Constructor for \"Binder Core ()\"."},
  {"Binder2_plain", Binder2_plain, METH_VARARGS,
   "Constructor for \"Binder' Core ()\"."},
  {"mkAppE", mkAppE, METH_VARARGS,
   "Create an application expression."},
  {"mkConAppE", mkConAppE, METH_VARARGS,
   "Create a constructor application expression."},
  {"mkLamE", mkLamE, METH_VARARGS,
   "Create a lambda expression."},
  {"mkFunE", mkFunE, METH_VARARGS,
   "Create a dependent function type expression."},
  {"mkArrowE", mkArrowE, METH_VARARGS,
   "Create a function type expression."},
  {"mkVarE", mkVarE, METH_VARARGS,
   "Create a variable expression."},
  {"mkConE", mkConE, METH_VARARGS,
   "Create a constructor expression."},
  {"mkTupE", mkTupE, METH_VARARGS,
   "Create a tuple expression."},
  {"mkTupTyE", mkTupTyE, METH_VARARGS,
   "Create a tuple type expression."},
  {"mkLitE", mkLitE, METH_VARARGS,
   "Create a literal expression."},
  {"Tuple_Core_cons", Tuple_Core_cons, METH_VARARGS,
   "Create a tuple."},
  {"Sum_Core_cons", Sum_Core_cons, METH_VARARGS,
   "Create a tuple type."},
  {"isExp", isExp, METH_O,
   "Return True if the parameter is a Gluon expression, False otherwise."},
  { NULL, NULL, 0, NULL}
};

static int
addGluonObject(PyObject *module, const char *name, void *(*factory)(void))
{
  PyObject *ptr = (PyObject *)factory();
  if (!ptr) return 0;

  PyModule_AddObject(module, (char *)name, ptr);
  return 1;
}

extern int
createGluonModule(void)
{
  /* Load the builtin Gluon definitions, if not already loaded */
  if (!gluon_builtinsLoaded() && !gluon_loadBuiltins()) return 0;

  PyObject *module = Py_InitModule("gluon", gluon_methods);

#define ADD_GLUON_OBJECT(name, factory) \
  if (!addGluonObject(module, name, factory)) return;

  ADD_GLUON_OBJECT("noSourcePos", gluon_noSourcePos);
  ADD_GLUON_OBJECT("ObjectLevel", gluon_mkObjectLevel);
  ADD_GLUON_OBJECT("TypeLevel", gluon_mkTypeLevel);
  ADD_GLUON_OBJECT("KindLevel", gluon_mkKindLevel);
  ADD_GLUON_OBJECT("SortLevel", gluon_mkSortLevel);
  ADD_GLUON_OBJECT("Tuple_Core_nil", gluon_Tuple_Core_nil);
  ADD_GLUON_OBJECT("Sum_Core_nil", gluon_Sum_Core_nil);
  ADD_GLUON_OBJECT("con_Int", gluon_con_Int);
  ADD_GLUON_OBJECT("con_Float", gluon_con_Float);
  ADD_GLUON_OBJECT("type_Pure", gluon_type_Pure);
}
