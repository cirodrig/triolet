
#ifndef CXXINTERFACE_SIGNATURE_H
#define CXXINTERFACE_SIGNATURE_H

typedef struct PyonType PyonType;
typedef struct PyonTypes PyonTypes;
typedef struct PyonSignature PyonSignature;

typedef enum PyonTypeTag {
  PyonIntTag = 0,               /* Pyon type "int" */
  PyonFloatTag,                 /* Pyon type "float" */
  PyonBoolTag,                  /* Pyon type "bool" */
  PyonNoneTypeTag               /* Pyon type "NoneType" */
} PyonTypeTag;

/* A Pyon type */
struct PyonType {
  PyonTypeTag tag;
};

/* Functions to create 'PyonType' instances */
const PyonType *PyonType_Int(void);
const PyonType *PyonType_Float(void);
const PyonType *PyonType_Bool(void);
const PyonType *PyonType_NoneType(void);
const PyonType *PyonType_duplicate(const PyonType *);

/* Destroy a PyonType instance */
void PyonType_destroy(const PyonType *);

/*****************************************************************************/

/* An array of Pyon types */
struct PyonTypes {
  int count;                    /* Length of array */
  const PyonType **elems; /* Pointer to an array of owned 'PyonType *' */
};

/* Allocate a PyonTypes object of the given length.  The caller should
 * assign elems[0] through elems[size - 1]. */
const PyonTypes *PyonTypes_alloc(int size);
const PyonTypes *PyonTypes_duplicate(const PyonTypes *);

/* Destroy a PyonTypes object */
void PyonTypes_destroy(const PyonTypes *);

/*****************************************************************************/

/* The signature of an exported Pyon function */
struct PyonSignature {
  const PyonTypes *parameterTypes; /* Owned reference to parameter type list */
  const PyonType *returnType;	   /* Owned reference to return type */
};

/* Create a 'PyonSignature'.  This steals ownership of the arguments. */
const PyonSignature *PyonSignature_create (const PyonTypes *parameter_types,
                                           const PyonType *return_type);

void PyonSignature_destroy(const PyonSignature *);

#endif
