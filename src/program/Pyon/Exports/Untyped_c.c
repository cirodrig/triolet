
#include <HsFFI.h>

// Undefine this symbol, which is redefined in Python.h, to eliminate a warning
#ifdef _POSIX_C_SOURCE
#undef _POSIX_C_SOURCE
#endif

#include <Python.h>

#include "PythonInterface/HsObject.h"
#include "Pyon/Exports/Untyped_stub.h"

/*****************************************************************************/

static PyObject *
SourcePos(PyObject *self, PyObject *args)
{
  const char *filename;
  int line, column;

  if (!PyArg_ParseTuple(args, "sii", &filename, &line, &column))
    return NULL;

  return pyon_SourcePos(filename, line, column);
}

static PyObject *
RigidTyVar(PyObject *self, PyObject *args)
{
  PyObject *kind;
  PyObject *label;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &label, &HsObject_type, &kind))
    return NULL;

  return pyon_RigidTyVar(label, kind);
}

static PyObject *
Variable(PyObject *self, PyObject *args)
{
  PyObject *var;

  if (!PyArg_ParseTuple(args, "O", &var))
    return NULL;

  return pyon_Variable(var);
}

static PyObject *
WildP(PyObject *self, PyObject *args)
{
  if (!PyArg_ParseTuple(args, ""))
    return NULL;

  return pyon_WildP();
}

static PyObject *
VariableP(PyObject *self, PyObject *args)
{
  PyObject *var;
  PyObject *type = Py_None;

  if (!PyArg_ParseTuple(args, "O!|O",
			&HsObject_type, &var, &type))
    return NULL;

  return pyon_VariableP(var, type);
}

static PyObject *
TupleP(PyObject *self, PyObject *args)
{
  PyObject *fields;

  if (!PyArg_ParseTuple(args, "O", &fields))
    return NULL;

  return pyon_TupleP(fields);
}

static PyObject *
VariableE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *var;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &pos, &HsObject_type, &var))
    return NULL;

  return pyon_VariableE(pos, var);
}

static PyObject *
NoneLiteral(PyObject *self, PyObject *args)
{
  PyObject *pos;

  if (!PyArg_ParseTuple(args, "O!", &HsObject_type, &pos))
    return NULL;

  return pyon_NoneLiteral(pos);
}

static PyObject *
IntLiteral(PyObject *self, PyObject *args)
{
  PyObject *pos;
  long n;

  if (!PyArg_ParseTuple(args, "O!l", &HsObject_type, &pos, &n))
    return NULL;

  return pyon_IntLiteral(pos, n);
}

static PyObject *
FloatLiteral(PyObject *self, PyObject *args)
{
  PyObject *pos;
  double d;

  if (!PyArg_ParseTuple(args, "O!d", &HsObject_type, &pos, &d))
    return NULL;

  return pyon_FloatLiteral(pos, d);
}

static PyObject *
BoolLiteral(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *b;

  if (!PyArg_ParseTuple(args, "O!O", &HsObject_type, &pos, &b))
    return NULL;

  return pyon_BoolLiteral(pos, b);
}

static PyObject *
UndefinedE(PyObject *self, PyObject *args)
{
  PyObject *pos;

  if (!PyArg_ParseTuple(args, "O!", &HsObject_type, &pos))
    return NULL;

  return pyon_UndefinedE(pos);
}

static PyObject *
TupleE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *fields;

  if (!PyArg_ParseTuple(args, "O!O", &HsObject_type, &pos, &fields))
    return NULL;

  return pyon_TupleE(pos, fields);
}

static PyObject *
CallE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *oper;
  PyObject *arg_list;

  if (!PyArg_ParseTuple(args, "O!O!O",
			&HsObject_type, &pos, &HsObject_type, &oper,
			&arg_list))
    return NULL;

  return pyon_CallE(pos, oper, arg_list);
}

static PyObject *
FunE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *f;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &pos, &HsObject_type, &f))
    return NULL;

  return pyon_FunE(pos, f);
}

static PyObject *
IfE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *cond, *tr, *fa;

  if (!PyArg_ParseTuple(args, "O!O!O!O!",
			&HsObject_type, &pos,
			&HsObject_type, &cond, &HsObject_type, &tr,
			&HsObject_type, &fa))
    return NULL;

  return pyon_IfE(pos, cond, tr, fa);
}

static PyObject *
LetE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *lhs;
  PyObject *rhs;
  PyObject *body;

  if (!PyArg_ParseTuple(args, "O!O!O!O!",
			&HsObject_type, &pos,
			&HsObject_type, &lhs, &HsObject_type, &rhs,
			&HsObject_type, &body))
    return NULL;

  return pyon_LetE(pos, lhs, rhs, body);
}

static PyObject *
LetrecE(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *defs;
  PyObject *body;

  if (!PyArg_ParseTuple(args, "O!OO!",
			&HsObject_type, &pos, &defs, &HsObject_type, &body))
    return NULL;

  return pyon_LetrecE(pos, defs, body);
}

static PyObject *
Function(PyObject *self, PyObject *args)
{
  PyObject *pos;
  PyObject *qvars;
  PyObject *params;
  PyObject *rt;
  PyObject *body;

  if (!PyArg_ParseTuple(args, "O!OOOO!", &HsObject_type, &pos,
			&qvars, &params, &rt,
			&HsObject_type, &body))
    return NULL;

  return pyon_Function(pos, qvars, params, rt, body);
}

static PyObject *
Def(PyObject *self, PyObject *args)
{
  PyObject *var;
  PyObject *fun;

  if (!PyArg_ParseTuple(args, "O!O!",
			&HsObject_type, &var, &HsObject_type, &fun))
    return NULL;

  return pyon_Def(var, fun);
}

static PyObject *
Module(PyObject *self, PyObject *args)
{
  PyObject *defgroups;

  if (!PyArg_ParseTuple(args, "O", &defgroups))
    return NULL;

  return pyon_Module(defgroups);
}

static PyObject *
typeApplication(PyObject *self, PyObject *args)
{
  PyObject *op;
  PyObject *operands;

  if (!PyArg_ParseTuple(args, "O!O", &HsObject_type, &op, &operands))
    return NULL;

  return pyon_typeApplication(op, operands);
}

/*****************************************************************************/

static PyMethodDef untyped_methods[] = {
  {"SourcePos", SourcePos, METH_VARARGS,
   "Construct a source code position"},
  {"RigidTyVar", RigidTyVar, METH_VARARGS,
   "Construct a rigid type variable"},
  {"Variable", Variable, METH_VARARGS,
   "Construct an untyped variable"},
  {"WildP", WildP, METH_VARARGS,
   "Construct a wildcard parameter"},
  {"VariableP", VariableP, METH_VARARGS,
   "Construct an untyped variable parameter"},
  {"TupleP", TupleP, METH_VARARGS,
   "Construct an untyped tuple parameter"},
  {"VariableE", VariableE, METH_VARARGS,
   "Construct a variable expression"},
  {"NoneLiteral", NoneLiteral, METH_VARARGS,
   "Construct a None literal expression"},
  {"IntLiteral", IntLiteral, METH_VARARGS,
   "Construct an integer literal expression"},
  {"FloatLiteral", FloatLiteral, METH_VARARGS,
   "Construct a floating-point literal expression"},
  {"BoolLiteral", BoolLiteral, METH_VARARGS,
   "Construct a boolean literal expression"},
  {"UndefinedE", UndefinedE, METH_VARARGS,
   "Construct an undefined expression"},
  {"TupleE", TupleE, METH_VARARGS,
   "Construct a tuple expression"},
  {"CallE", CallE, METH_VARARGS,
   "Construct a call expression"},
  {"FunE", FunE, METH_VARARGS,
   "Construct a function expression"},
  {"IfE", IfE, METH_VARARGS,
   "Construct an if expression"},
  {"LetE", LetE, METH_VARARGS,
   "Construct a let expression"},
  {"LetrecE", LetrecE, METH_VARARGS,
   "Construct a letrec expression"},
  {"Function", Function, METH_VARARGS,
   "Consruct a function object"},
  {"Def", Def, METH_VARARGS,
   "Construct a function definition"},
  {"Module", Module, METH_VARARGS,
   "Construct a module object"},
  {"printModule", pyon_printModule, METH_O,
   "Print a module"},
  {"typeApplication", typeApplication, METH_VARARGS,
   "Apply a type constructor to a list of operands"},
  {"typeInferModule", pyon_typeInferModule, METH_O,
   "Perform type inference on an untyped module, generating a System F\n"
   " module."},
  {"typeCheckModule", pyon_typeCheckSystemFModule, METH_O,
   "Perform type checking on a System F module.  If checking fails, an\n"
   "exception will be raised."},
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

#define ADD_OBJECT(name, factory) \
  if (!addGlobalObject(module, name, factory)) return 0;

extern int
createUntypedModule(void)
{
  /* Load the builtin Gluon definitions, if not already loaded */
  if (!gluon_builtinsLoaded() && !gluon_loadBuiltins()) return 0;

  /* Initialize the builtins module */
  if (!pyon_initializeUntypedModule()) return 0;

  PyObject *module = Py_InitModule("untyped", untyped_methods);

  ADD_OBJECT("BUILTIN_TYPES", pyon_builtinTypes);
  ADD_OBJECT("GLOBAL_VARIABLES", pyon_globalVariables);
  ADD_OBJECT("fun_makelist", pyon_fun_makelist);
  ADD_OBJECT("fun_do", pyon_fun_do);
  ADD_OBJECT("fun_guard", pyon_fun_guard);
  ADD_OBJECT("fun_iter", pyon_fun_iter);
  ADD_OBJECT("fun_iterBind", pyon_fun_iterBind);
  ADD_OBJECT("oper_ADD", pyon_oper_ADD);
  ADD_OBJECT("oper_SUB", pyon_oper_SUB);
  ADD_OBJECT("oper_MUL", pyon_oper_MUL);
  ADD_OBJECT("oper_DIV", pyon_oper_DIV);
  ADD_OBJECT("oper_MOD", pyon_oper_MOD);
  ADD_OBJECT("oper_FLOORDIV", pyon_oper_FLOORDIV);
  ADD_OBJECT("oper_POWER", pyon_oper_POWER);
  ADD_OBJECT("oper_EQ", pyon_oper_EQ);
  ADD_OBJECT("oper_NE", pyon_oper_NE);
  ADD_OBJECT("oper_LT", pyon_oper_LT);
  ADD_OBJECT("oper_LE", pyon_oper_LE);
  ADD_OBJECT("oper_GT", pyon_oper_GT);
  ADD_OBJECT("oper_GE", pyon_oper_GE);
  ADD_OBJECT("oper_BITWISEAND", pyon_oper_BITWISEAND);
  ADD_OBJECT("oper_BITWISEOR", pyon_oper_BITWISEOR);
  ADD_OBJECT("oper_BITWISEXOR", pyon_oper_BITWISEXOR);
  ADD_OBJECT("oper_NEGATE", pyon_oper_NEGATE);
  ADD_OBJECT("Star", pyon_Star);

  return 1;
}
