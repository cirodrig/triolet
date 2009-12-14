
#include "operators.h"

/* Members of an operator that are accessible from Python */
static PyMemberDef Pyon_Operator_members[] = {
  {"name", T_STRING, offsetof(Pyon_Operator, name), READONLY,
   "Name of operator"},
  {"display", T_STRING, offsetof(Pyon_Operator, display), READONLY,
   "Source code appearance of operator"},
  {NULL}
};

static PyMemberDef Pyon_BinaryOp_members[] = {
  {"name", T_STRING, offsetof(Pyon_BinaryOp, name), READONLY,
   "Name of operator"},
  {"display", T_STRING, offsetof(Pyon_BinaryOp, display), READONLY,
   "Source code appearance of operator"},
  {"associativity", T_INT, offsetof(Pyon_BinaryOp, associativity), READONLY,
   "Associativity of operator (ASSOC_NONE, ASSOC_LEFT, or ASSOC_RIGHT)"},
  {"precedence", T_INT, offsetof(Pyon_BinaryOp, precedence), READONLY,
   "Operator precedence (higher precedence binds more tightly"},
  {NULL}
};

static PyMemberDef Pyon_UnaryOp_members[] = {
  {"name", T_STRING, offsetof(Pyon_UnaryOp, name), READONLY,
   "Name of operator"},
  {"display", T_STRING, offsetof(Pyon_UnaryOp, display), READONLY,
   "Source code appearance of operator"},
  {"precedence", T_INT, offsetof(Pyon_UnaryOp, precedence), READONLY,
   "Operator precedence (higher precedence binds more tightly"},
  {NULL}
};

static PyTypeObject Operator_type = {
  PyObject_HEAD_INIT(NULL)
  0,				/* ob_size */
  "Operator",			/* tp_name */
  sizeof(Pyon_Operator),	/* tp_basicsize */
  0,				/* tp_itemsize */
  0,				/* tp_dealloc */
  0,				/* tp_print */
  0,				/* tp_getattr */
  0,				/* tp_setattr */
  0,				/* tp_reserved */
  0,				/* tp_repr */
  0,				/* tp_as_number */
  0,				/* tp_as_sequence */
  0,				/* tp_as_mapping */
  0,				/* tp_hash  */
  0,				/* tp_call */
  0,				/* tp_str */
  0,				/* tp_getattro */
  0,				/* tp_setattro */
  0,				/* tp_as_buffer */
  Py_TPFLAGS_DEFAULT,		/* tp_flags */
  "Base type of Python operators", /* tp_doc */
  0,				/* tp_traverse */
  0,				/* tp_clear */
  0,				/* tp_richcompare */
  0,				/* tp_weaklistoffset */
  0,				/* tp_iter */
  0,				/* tp_iternext */
  0,				/* tp_methods */
  Pyon_Operator_members,	/* tp_members */
  0,				/* tp_getset */
  0,				/* tp_base */
  0,				/* tp_dict */
  0,				/* tp_descr_get */
  0,				/* tp_descr_set */
};

static PyTypeObject UnaryOp_type = {
  PyObject_HEAD_INIT(NULL)
  0,				/* ob_size */
  "UnaryOp",			/* tp_name */
  sizeof(Pyon_UnaryOp),		/* tp_basicsize */
  0,				/* tp_itemsize */
  0,				/* tp_dealloc */
  0,				/* tp_print */
  0,				/* tp_getattr */
  0,				/* tp_setattr */
  0,				/* tp_reserved */
  0,				/* tp_repr */
  0,				/* tp_as_number */
  0,				/* tp_as_sequence */
  0,				/* tp_as_mapping */
  0,				/* tp_hash  */
  0,				/* tp_call */
  0,				/* tp_str */
  0,				/* tp_getattro */
  0,				/* tp_setattro */
  0,				/* tp_as_buffer */
  Py_TPFLAGS_DEFAULT,		/* tp_flags */
  "Unary Python operators",	/* tp_doc */
  0,				/* tp_traverse */
  0,				/* tp_clear */
  0,				/* tp_richcompare */
  0,				/* tp_weaklistoffset */
  0,				/* tp_iter */
  0,				/* tp_iternext */
  0,				/* tp_methods */
  Pyon_UnaryOp_members,		/* tp_members */
  0,				/* tp_getset */
  &Operator_type,		/* tp_base */
  0,				/* tp_dict */
  0,				/* tp_descr_get */
  0,				/* tp_descr_set */
};

static PyTypeObject BinaryOp_type = {
  PyObject_HEAD_INIT(NULL)
  0,				/* ob_size */
  "BinaryOp",			/* tp_name */
  sizeof(Pyon_BinaryOp),	/* tp_basicsize */
  0,				/* tp_itemsize */
  0,				/* tp_dealloc */
  0,				/* tp_print */
  0,				/* tp_getattr */
  0,				/* tp_setattr */
  0,				/* tp_reserved */
  0,				/* tp_repr */
  0,				/* tp_as_number */
  0,				/* tp_as_sequence */
  0,				/* tp_as_mapping */
  0,				/* tp_hash  */
  0,				/* tp_call */
  0,				/* tp_str */
  0,				/* tp_getattro */
  0,				/* tp_setattro */
  0,				/* tp_as_buffer */
  Py_TPFLAGS_DEFAULT,		/* tp_flags */
  "Binary Python operators",	/* tp_doc */
  0,				/* tp_traverse */
  0,				/* tp_clear */
  0,				/* tp_richcompare */
  0,				/* tp_weaklistoffset */
  0,				/* tp_iter */
  0,				/* tp_iternext */
  0,				/* tp_methods */
  Pyon_BinaryOp_members,	/* tp_members */
  0,				/* tp_getset */
  &Operator_type,		/* tp_base */
  0,				/* tp_dict */
  0,				/* tp_descr_get */
  0,				/* tp_descr_set */
};

static PyTypeObject AugmentOp_type = {
  PyObject_HEAD_INIT(NULL)
  0,				/* ob_size */
  "AugmentOp",			/* tp_name */
  sizeof(Pyon_AugmentOp),	/* tp_basicsize */
  0,				/* tp_itemsize */
  0,				/* tp_dealloc */
  0,				/* tp_print */
  0,				/* tp_getattr */
  0,				/* tp_setattr */
  0,				/* tp_reserved */
  0,				/* tp_repr */
  0,				/* tp_as_number */
  0,				/* tp_as_sequence */
  0,				/* tp_as_mapping */
  0,				/* tp_hash  */
  0,				/* tp_call */
  0,				/* tp_str */
  0,				/* tp_getattro */
  0,				/* tp_setattro */
  0,				/* tp_as_buffer */
  Py_TPFLAGS_DEFAULT,		/* tp_flags */
  "Augmenting Python operators", /* tp_doc */
  0,				/* tp_traverse */
  0,				/* tp_clear */
  0,				/* tp_richcompare */
  0,				/* tp_weaklistoffset */
  0,				/* tp_iter */
  0,				/* tp_iternext */
  0,				/* tp_methods */
  Pyon_Operator_members,	/* tp_members */
  0,				/* tp_getset */
  &Operator_type,		/* tp_base */
  0,				/* tp_dict */
  0,				/* tp_descr_get */
  0,				/* tp_descr_set */
};

/*****************************************************************************/
/* Operator tables */

/* Each operator must be declared in three places:
 * * As a table field, to define its contents
 * * As a global variable, to initialize it
 * * As an extern global variable in the header file,
 *   to make it visible to external code.
 *
 * Keep the index declaration orders consistent. Operations are listed
 * in decreasing order of priority.
 */

#define BINARY_OP_DECL(name, display, prec, assoc)			\
  { PyObject_HEAD_INIT(&BinaryOp_type) name, display, prec, assoc }

#define BINARY_OP_NAME(name, index) \
  const Pyon_BinaryOpRef pyon_Op_ ## name = &ast_binary_operators[index]

static struct Pyon_BinaryOp ast_binary_operators[] = {
  BINARY_OP_DECL("POWER", "**", 13, ASSOC_NONE),
  BINARY_OP_DECL("MUL", "*", 11, ASSOC_LEFT),
  BINARY_OP_DECL("FLOORDIV", "//", 11, ASSOC_LEFT),
  BINARY_OP_DECL("DIV", "/", 11, ASSOC_LEFT),
  BINARY_OP_DECL("MOD", "%", 11, ASSOC_LEFT),
  BINARY_OP_DECL("ADD",  "+", 10, ASSOC_LEFT),
  BINARY_OP_DECL("SUB",  "-", 10, ASSOC_LEFT),
  BINARY_OP_DECL("LT", "<", 4, ASSOC_NONE),
  BINARY_OP_DECL("GT", ">", 4, ASSOC_NONE),
  BINARY_OP_DECL("EQ", "==", 4, ASSOC_NONE),
  BINARY_OP_DECL("LE", "<=", 4, ASSOC_NONE),
  BINARY_OP_DECL("GE", ">=", 4, ASSOC_NONE),
  BINARY_OP_DECL("NE", "!=", 4, ASSOC_NONE),
  BINARY_OP_DECL(NULL, NULL, 0, 0)	/* sentinel */
};

BINARY_OP_NAME(POWER,   0);
BINARY_OP_NAME(MUL,     1);
BINARY_OP_NAME(FLOORDIV, 2);
BINARY_OP_NAME(DIV,     3);
BINARY_OP_NAME(MOD,     4);
BINARY_OP_NAME(ADD,     5);
BINARY_OP_NAME(SUB,     6);
BINARY_OP_NAME(LT,      7);
BINARY_OP_NAME(GT,      8);
BINARY_OP_NAME(EQ,      9);
BINARY_OP_NAME(LE,      10);
BINARY_OP_NAME(GE,      11);
BINARY_OP_NAME(NE,      12);

#define UNARY_OP_DECL(name, display, prec)			\
  { PyObject_HEAD_INIT(&UnaryOp_type) name, display, prec }

#define UNARY_OP_NAME(name, index) \
  const Pyon_UnaryOpRef pyon_Op_ ## name = &ast_unary_operators[index]

static struct Pyon_UnaryOp ast_unary_operators[] = {
  UNARY_OP_DECL("NEGATE", "-", 12),
  UNARY_OP_DECL("COMPLEMENT", "~", 12),
  UNARY_OP_DECL("NOT", "not", 12),
  UNARY_OP_DECL(NULL, NULL, 0)	/* sentinel */
};

/*****************************************************************************/
/* Module initialization */

/* Initialize and add all operators to the module. */
static int
add_operators(PyObject *mod)
{
  {
    Pyon_BinaryOp *def;

    for (def = &ast_binary_operators[0]; def->name; def++) {
      /* Increment the reference count, so that the reference count will
       * never fall to zero. */
      Py_INCREF(def);
      PyModule_AddObject(mod, (char *)def->name, (PyObject *)def);
    }
  }
  {
    Pyon_UnaryOp *def;

    for (def = &ast_unary_operators[0]; def->name; def++) {
      /* Increment the reference count, so that the reference count will
       * never fall to zero. */
      Py_INCREF(def);
      PyModule_AddObject(mod, (char *)def->name, (PyObject *)def);
    }
  }

  return 1;
}

/* Initialize a type object and add it to the module */
static int
add_type(PyObject *mod, PyTypeObject *type)
{
  if (PyType_Ready(type) < 0) {
    PyErr_Format(PyExc_SystemError,
		 "Cannot initialize type '%s'",
		 type->tp_name);
    return 0;
  }

  PyModule_AddObject(mod, type->tp_name, (PyObject *)type);
  return 1;
}

static PyMethodDef
module_methods[] = {
  {NULL, NULL, 0, NULL}
};

PyMODINIT_FUNC
initoperators(void)
{
  PyObject *mod = Py_InitModule("operators", module_methods);

  /* Associativity */
  PyModule_AddIntConstant(mod, "ASSOC_NONE", ASSOC_NONE);
  PyModule_AddIntConstant(mod, "ASSOC_LEFT", ASSOC_LEFT);
  PyModule_AddIntConstant(mod, "ASSOC_RIGHT", ASSOC_RIGHT);

  if (!add_type(mod, &Operator_type)) return;
  if (!add_type(mod, &UnaryOp_type)) return;
  if (!add_type(mod, &BinaryOp_type)) return;
  if (!add_type(mod, &AugmentOp_type)) return;

  if (!add_operators(mod)) return;
}
