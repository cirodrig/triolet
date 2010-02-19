
#include <HsFFI.h>

// Undefine this symbol, which is redefined in Python.h, to eliminate a warning
#ifdef _POSIX_C_SOURCE
#undef _POSIX_C_SOURCE
#endif

#include <Python.h>

#include "PythonInterface/HsObject.h"
#include "Pyon/Exports/SystemF_stub.h"

/*****************************************************************************/

static PyObject *
getTupleCon(PyObject *self, PyObject *args)
{
  int size;
  if (!PyArg_ParseTuple(args, "i", &size))
    return NULL;

  return pyon_getTupleCon(size);
}

static PyObject *
newExpPlaceholder(PyObject *self, PyObject *args)
{
  return pyon_newExpPlaceholder();
}

static PyObject *
setExpPlaceholder(PyObject *self, PyObject *args)
{
  PyObject *placeholder;
  PyObject *value;

  if (!PyArg_ParseTuple(args, "O!O!", &HsObject_type, &placeholder,
			&HsObject_type, &value))
    return NULL;

  return pyon_setExpPlaceholder(placeholder, value);
}

static PyObject *
newVar(PyObject *self, PyObject *args)
{
  char *name;

  if (!PyArg_ParseTuple(args, "z", &name))
    return NULL;

  return pyon_newVar(name);
}

static PyObject *
mkIntL(PyObject *self, PyObject *arg)
{
  PyObject *as_long = PyNumber_Int(arg);

  if (!as_long) return NULL;

  PyObject *rv = pyon_mkIntL(PyInt_AS_LONG(as_long));

  Py_DECREF(as_long);
  return rv;
}

static PyObject *
mkFloatL(PyObject *self, PyObject *arg)
{
  PyObject *as_float = PyNumber_Float(arg);

  if (!as_float) return NULL;

  PyObject *rv = pyon_mkFloatL(PyFloat_AS_DOUBLE(as_float));
  Py_DECREF(as_float);
  return rv;
}

static PyObject *
mkBoolL(PyObject *self, PyObject *arg)
{
  if (!PyBool_Check(arg)) {
    PyErr_SetString(PyExc_TypeError, "Expecting a bool");
    return NULL;
  }

  return pyon_mkBoolL(arg == Py_True);
}

static PyObject *
mkTyPat(PyObject *self, PyObject *args)
{
  PyObject *tyvar;
  PyObject *kind;

  if (!PyArg_ParseTuple(args, "O!O!", &HsObject_type, &tyvar,
			&HsObject_type, &kind))
    return NULL;

  return pyon_mkTyPat(tyvar, kind);
}

static PyObject *
mkWildP(PyObject *self, PyObject *args)
{
  PyObject *type;

  if (!PyArg_ParseTuple(args, "O!", &HsObject_type, &type))
    return NULL;

  return pyon_mkWildP(type);
}

static PyObject *
mkVarP(PyObject *self, PyObject *args)
{
  PyObject *var;
  PyObject *type;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &var, &HsObject_type, &type))
    return NULL;

  return pyon_mkVarP(var, type);
}

static PyObject *
mkTupleP(PyObject *self, PyObject *args)
{
  PyObject *fields;

  if (!PyArg_ParseTuple(args, "O", &fields))
    return NULL;

  return pyon_mkTupleP(fields);
}

static PyObject *
mkVarE(PyObject *self, PyObject *args)
{
  PyObject *var;

  if (!PyArg_ParseTuple(args, "O!", &HsObject_type, &var))
    return NULL;

  return pyon_mkVarE(var);
}

static PyObject *
mkConE(PyObject *self, PyObject *args)
{
  PyObject *var;

  if (!PyArg_ParseTuple(args, "O!", &HsObject_type, &var))
    return NULL;

  return pyon_mkConE(var);
}

static PyObject *
mkLitE(PyObject *self, PyObject *args)
{
  PyObject *lit;
  PyObject *type;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &lit, &HsObject_type, &type))
    return NULL;

  return pyon_mkLitE(lit, type);
}

static PyObject *
mkUndefinedE(PyObject *self, PyObject *args)
{
  PyObject *type;

  if (!PyArg_ParseTuple(args, "O!", &HsObject_type, &type))
    return NULL;

  return pyon_mkUndefinedE(type);
}

static PyObject *
mkTupleE(PyObject *self, PyObject *args)
{
  PyObject *fields;

  if (!PyArg_ParseTuple(args, "O", &fields))
    return NULL;

  return pyon_mkTupleE(fields);
}

static PyObject *
mkTyAppE(PyObject *self, PyObject *args)
{
  PyObject *oper;
  PyObject *arg;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &oper, &HsObject_type, &arg))
    return NULL;

  return pyon_mkTyAppE(oper, arg);
}

static PyObject *
mkCallE(PyObject *self, PyObject *args)
{
  PyObject *oper;
  PyObject *arguments;

  if (!PyArg_ParseTuple(args, "O!O", &HsObject_type, &oper, &arguments))
    return NULL;

  return pyon_mkCallE(oper, arguments);
}

static PyObject *
mkIfE(PyObject *self, PyObject *args)
{
  PyObject *cond;
  PyObject *if_true;
  PyObject *if_false;

  if (!PyArg_ParseTuple(args, "O!O!O!",
			&HsObject_type, &cond, &HsObject_type, &if_true,
			&HsObject_type, &if_false))
    return NULL;

  return pyon_mkIfE(cond, if_true, if_false);
}

static PyObject *
mkFunE(PyObject *self, PyObject *args)
{
  PyObject *fun;

  if (!PyArg_ParseTuple(args, "O!", &HsObject_type, &fun))
    return NULL;

  return pyon_mkFunE(fun);
}

static PyObject *
mkLetE(PyObject *self, PyObject *args)
{
  PyObject *pat;
  PyObject *lhs;
  PyObject *body;

  if (!PyArg_ParseTuple(args, "O!O!O!",
			&HsObject_type, &pat, &HsObject_type, &lhs,
			&HsObject_type, &body))
    return NULL;

  return pyon_mkLetE(pat, lhs, body);
}

static PyObject *
mkLetrecE(PyObject *self, PyObject *args)
{
  PyObject *defs;
  PyObject *body;

  if (!PyArg_ParseTuple(args, "OO!", &defs, &HsObject_type, &body))
    return NULL;

  return pyon_mkLetrecE(defs, body);
}

static PyObject *
mkDictE(PyObject *self, PyObject *args)
{
  PyObject *cls;
  PyObject *type;
  PyObject *superclasses;
  PyObject *methods;

  if (!PyArg_ParseTuple(args, "O!O!OO",
			&HsObject_type, &cls, &HsObject_type, &type,
			&superclasses, &methods))
    return NULL;

  return pyon_mkDictE(cls,type, superclasses, methods);
}

static PyObject *
mkMethodSelectE(PyObject *self, PyObject *args)
{
  PyObject *cls;
  PyObject *type;
  int index;
  PyObject *arg;

  if (!PyArg_ParseTuple(args, "O!O!iO!",
			&HsObject_type, &cls, &HsObject_type, &type, &index,
			&HsObject_type, &arg))
    return NULL;

  return pyon_mkMethodSelectE(cls, type, index, arg);
}

static PyObject *
mkFun(PyObject *self, PyObject *args)
{
  PyObject *type_params;
  PyObject *params;
  PyObject *return_type;
  PyObject *stream_tag_callback;
  PyObject *body;

  if (!PyArg_ParseTuple(args, "OOO!OO!", &type_params, &params,
			&HsObject_type, &return_type,
			&stream_tag_callback,
			&HsObject_type, &body))
    return NULL;

  return pyon_mkFun(type_params, params, return_type, stream_tag_callback, body);
}

static PyObject *
mkDef(PyObject *self, PyObject *args)
{
  PyObject *var;
  PyObject *fun;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &var, &HsObject_type, &fun))
    return NULL;

  return pyon_mkDef(var, fun);
}

static PyObject *
makeAndEvaluateModule(PyObject *self, PyObject *args)
{
  PyObject *defs;

  if (!PyArg_ParseTuple(args, "O", &defs))
    return NULL;

  return pyon_makeAndEvaluateModule(defs);
}

static PyObject *
isExp(PyObject *self, PyObject *arg)
{
  if (!PyObject_IsInstance(arg, (PyObject *)&HsObject_type)) {
    PyErr_SetString(PyExc_TypeError, "Expecting a HsObject instance");
    return NULL;
  }

  int rc = pyon_isExp(arg);
  return PyBool_FromLong(rc);
}

/*****************************************************************************/

static PyMethodDef system_f_methods[] = {
  {"getTupleCon", getTupleCon, METH_VARARGS,
   "Get the type constructor for an N-tuple"},
  {"newExpPlaceholder", newExpPlaceholder, METH_NOARGS,
   "Create a new placeholder expression."},
  {"setExpPlaceholder", setExpPlaceholder, METH_VARARGS,
   "Assign the value of a placeholder expression."},
  {"newVar", newVar, METH_VARARGS,
   "Create a new variable."},
  {"mkIntL", mkIntL, METH_O,
   "Create a literal integer value."},
  {"mkFloatL", mkFloatL, METH_O,
   "Create a literal floating-point value."},
  {"mkBoolL", mkBoolL, METH_O,
   "Create a literal boolean value."},
  {"mkTyPat", mkTyPat, METH_VARARGS,
   "Create a type variable pattern."},
  {"mkWildP", mkWildP, METH_VARARGS,
   "Create a wildcard pattern."},
  {"mkVarP", mkVarP, METH_VARARGS,
   "Create a variable pattern."},
  {"mkTupleP", mkTupleP, METH_VARARGS,
   "Create a tuple pattern."},
  {"mkVarE", mkVarE, METH_VARARGS,
   "Create a variable expression."},
  {"mkConE", mkConE, METH_VARARGS,
   "Create a constructor expression."},
  {"mkLitE", mkLitE, METH_VARARGS,
   "Create a literal expression."},
  {"mkUndefinedE", mkUndefinedE, METH_VARARGS,
   "Create an undefined expression."},
  {"mkTupleE", mkTupleE, METH_VARARGS,
   "Create a tuple expression."},
  {"mkTyAppE", mkTyAppE, METH_VARARGS,
   "Create a type application expression."},
  {"mkCallE", mkCallE, METH_VARARGS,
   "Create a function call expression."},
  {"mkIfE", mkIfE, METH_VARARGS,
   "Create a conditional expression."},
  {"mkFunE", mkFunE, METH_VARARGS,
   "Create a lambda expression."},
  {"mkLetE", mkLetE, METH_VARARGS,
   "Create a let expression."},
  {"mkLetrecE", mkLetrecE, METH_VARARGS,
   "Create a letrec expression."},
  {"mkDictE", mkDictE, METH_VARARGS,
   "Create a dictionary expression."},
  {"mkMethodSelectE", mkMethodSelectE, METH_VARARGS,
   "Create a method select expression."},
  {"mkFun", mkFun, METH_VARARGS,
   "Create a function."},
  {"mkDef", mkDef, METH_VARARGS,
   "Create a function definition."},
  {"makeAndEvaluateModule", makeAndEvaluateModule, METH_VARARGS,
   "Create a module from a list of definitions.  This function also runs\n"
   "any delayed computation of the module's contents."},
  {"printModule", pyon_printModule, METH_O,
   "Print a module to standard output."},
  {"optimizeModule", pyon_optimizeModule, METH_O,
   "Run System F optimizations on a module."},
  {"typeCheckModule", pyon_typeCheckModule, METH_O,
   "Typecheck a module."},
  {"isExp", isExp, METH_O,
   "Determine whether the parameter is a System F expression."},
  {NULL, NULL, 0, NULL}
};

static int
addGlobalObject(PyObject *module, const char *name, void *(*factory)(void))
{
  PyObject *ptr = (PyObject *)factory();
  if (!ptr) return 0;

  PyModule_AddObject(module, (char *)name, ptr);
  return 1;
}

extern int
createSystemFModule(void)
{
  /* Load the builtin Gluon definitions, if not already loaded */
  if (!gluon_builtinsLoaded() && !gluon_loadBuiltins()) return 0;

  PyObject *module = Py_InitModule("system_f", system_f_methods);

#define ADD_OBJECT(name, factory) \
  if (!addGlobalObject(module, name, factory)) return;

  ADD_OBJECT("NoneL", pyon_mkNoneL);

  ADD_OBJECT("con_Action", pyon_con_Action);
  ADD_OBJECT("con_Stream", pyon_con_Stream);
  ADD_OBJECT("con_NoneType", pyon_con_NoneType);
  ADD_OBJECT("con_Any", pyon_con_Any);
  ADD_OBJECT("con_bool", pyon_con_bool);
  ADD_OBJECT("con_list", pyon_con_list);
  ADD_OBJECT("con_EqDict", pyon_con_EqDict);
  ADD_OBJECT("con_OrdDict", pyon_con_OrdDict);
  ADD_OBJECT("con_TraversableDict", pyon_con_TraversableDict);
  ADD_OBJECT("con_EQ_Int", pyon_con_EQ_Int);
  ADD_OBJECT("con_NE_Int", pyon_con_NE_Int);
  ADD_OBJECT("con_LT_Int", pyon_con_LT_Int);
  ADD_OBJECT("con_LE_Int", pyon_con_LE_Int);
  ADD_OBJECT("con_GT_Int", pyon_con_GT_Int);
  ADD_OBJECT("con_GE_Int", pyon_con_GE_Int);
  ADD_OBJECT("con_EQ_Float", pyon_con_EQ_Float);
  ADD_OBJECT("con_NE_Float", pyon_con_NE_Float);
  ADD_OBJECT("con_LT_Float", pyon_con_LT_Float);
  ADD_OBJECT("con_LE_Float", pyon_con_LE_Float);
  ADD_OBJECT("con_GT_Float", pyon_con_GT_Float);
  ADD_OBJECT("con_GE_Float", pyon_con_GE_Float);
  ADD_OBJECT("con_EQ_Tuple2", pyon_con_EQ_Tuple2);
  ADD_OBJECT("con_NE_Tuple2", pyon_con_NE_Tuple2);
  ADD_OBJECT("con_LT_Tuple2", pyon_con_LT_Tuple2);
  ADD_OBJECT("con_LE_Tuple2", pyon_con_LE_Tuple2);
  ADD_OBJECT("con_GT_Tuple2", pyon_con_GT_Tuple2);
  ADD_OBJECT("con_GE_Tuple2", pyon_con_GE_Tuple2);
  ADD_OBJECT("con_TRAVERSE_Stream", pyon_con_TRAVERSE_Stream);
  ADD_OBJECT("con_TRAVERSE_list", pyon_con_TRAVERSE_list);
  ADD_OBJECT("EqClass", pyon_EqClass);
  ADD_OBJECT("OrdClass", pyon_OrdClass);
  ADD_OBJECT("TraversableClass", pyon_TraversableClass);
  ADD_OBJECT("con_oper_ADD", pyon_con_oper_ADD);
  ADD_OBJECT("con_oper_SUB", pyon_con_oper_SUB);
  ADD_OBJECT("con_oper_MUL", pyon_con_oper_MUL);
  ADD_OBJECT("con_oper_DIV", pyon_con_oper_DIV);
  ADD_OBJECT("con_oper_MOD", pyon_con_oper_MOD);
  ADD_OBJECT("con_oper_POWER", pyon_con_oper_POWER);
  ADD_OBJECT("con_oper_FLOORDIV", pyon_con_oper_FLOORDIV);
  ADD_OBJECT("con_oper_BITWISEAND", pyon_con_oper_BITWISEAND);
  ADD_OBJECT("con_oper_BITWISEOR", pyon_con_oper_BITWISEOR);
  ADD_OBJECT("con_oper_BITWISEXOR", pyon_con_oper_BITWISEXOR);
  ADD_OBJECT("con_oper_NEGATE", pyon_con_oper_NEGATE);
  ADD_OBJECT("con_oper_CAT_MAP", pyon_con_oper_CAT_MAP);
  ADD_OBJECT("con_oper_GUARD", pyon_con_oper_GUARD);
  ADD_OBJECT("con_oper_DO", pyon_con_oper_DO);
  ADD_OBJECT("con_fun_makelist", pyon_con_fun_makelist);
  ADD_OBJECT("con_fun_map", pyon_con_fun_map);
  ADD_OBJECT("con_fun_reduce", pyon_con_fun_reduce);
  ADD_OBJECT("con_fun_reduce1", pyon_con_fun_reduce1);
  ADD_OBJECT("con_fun_zip", pyon_con_fun_zip);
  ADD_OBJECT("con_fun_iota", pyon_con_fun_iota);
  ADD_OBJECT("con_fun_undefined", pyon_con_fun_undefined);

  return 1;
}
