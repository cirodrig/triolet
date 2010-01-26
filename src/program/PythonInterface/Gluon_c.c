
#include <Python.h>

#include "PythonInterface/HsObject.h"
#include "PythonInterface/Gluon_stub.h"

/*****************************************************************************/
/* C wrappers for argument marshaling */

static PyObject *
loadBuiltins(PyObject *self, PyObject *args)
{
  return gluon_loadBuiltins();
}

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
Prod_Core_cons(PyObject *self, PyObject *args)
{
  PyObject *param;
  PyObject *tail;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &param, &HsObject_type, &tail))
    return NULL;

  return gluon_Prod_Core_cons(param, tail);
}

/*****************************************************************************/
/* Module definition */

static struct PyMethodDef gluon_methods[] = {
  {"loadBuiltins", loadBuiltins, METH_NOARGS,
   "Load the 'Builtin' gluon module."},
  {"pgmLabel", pgmLabel, METH_VARARGS,
   "Create a label value, given a module name and entity name."},
  {"mkVariable", mkVariable, METH_VARARGS,
   "Create a variable given an ID, label, and level."},
  {"Binder_plain", Binder_plain, METH_VARARGS,
   "Constructor for \"Binder Core ()\"."},
  {"Binder2_plain", Binder2_plain, METH_VARARGS,
   "Constructor for \"Binder' Core ()\"."},
  {"mkAppE", mkAppE, METH_VARARGS,
   "Create an application expression."},
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
  {"Prod_Core_cons", Prod_Core_cons, METH_VARARGS,
   "Create a tuple type."},
  { NULL, NULL, 0, NULL}
};

extern void
createGluonModule(void)
{
  PyObject *module = Py_InitModule("gluon", gluon_methods);

  PyModule_AddObject(module, "noSourcePos", (PyObject *)gluon_noSourcePos());
  PyModule_AddObject(module, "ObjectLevel", (PyObject *)gluon_mkObjectLevel());
  PyModule_AddObject(module, "TypeLevel", (PyObject *)gluon_mkTypeLevel());
  PyModule_AddObject(module, "KindLevel", (PyObject *)gluon_mkKindLevel());
  PyModule_AddObject(module, "SortLevel", (PyObject *)gluon_mkSortLevel());
  PyModule_AddObject(module, "Tuple_Core_nil",
		     (PyObject *)gluon_Tuple_Core_nil());
  PyModule_AddObject(module, "Prod_Core_nil",
		     (PyObject *)gluon_Prod_Core_nil());
}
