
#include <Python.h>
#include <structmember.h>

typedef struct Pyon_Operator Pyon_Operator;
typedef struct Pyon_UnaryOp Pyon_UnaryOp;
typedef struct Pyon_BinaryOp Pyon_BinaryOp;
typedef struct Pyon_AugmentOp Pyon_AugmentOp;

typedef struct Pyon_UnaryOp *Pyon_UnaryOpRef;
typedef struct Pyon_BinaryOp *Pyon_BinaryOpRef;
typedef struct Pyon_AugmentOp *Pyon_AugmentOpRef;

/* Fields shared by the base type and subtypes */
#define Pyon_Operator_FIELDS					\
  PyObject_HEAD							\
  const char *name;		/* Name of operator */		\
  const char *display;		/* The operator's appearance */

/* The abstract base type of Pyon operators */
struct Pyon_Operator {
  Pyon_Operator_FIELDS
};

/* A unary Pyon operator */
struct Pyon_UnaryOp {
  Pyon_Operator_FIELDS
};

/* A binary Pyon operator */
struct Pyon_BinaryOp {
  Pyon_Operator_FIELDS
};

/* An augmenting Pyon operator */
struct Pyon_AugmentOp {
  Pyon_Operator_FIELDS
};


/* There's a statically declared, const pointer to each operator so that we
 * can refer to them outside of Python. */

extern const Pyon_BinaryOpRef
  pyon_Op_POWER,
  pyon_Op_MUL,
  pyon_Op_FLOORDIV,
  pyon_Op_DIV,
  pyon_Op_MOD,
  pyon_Op_ADD,
  pyon_Op_SUB;
  
