
#ifndef CXX_WRAPPER_GENERATOR_PRINT_H
#define CXX_WRAPPER_GENERATOR_PRINT_H

#include "CxxInterface/CxxWrapperGeneratorTypes.h"

// ===== Helper Structure Declarations =====

typedef struct Derivation Derivation;

// ===== Printing Function Declarations =====

void printNothing(FILE* fp, void* capture);
void printName (FILE* fp, Name* name);
void printTmplName (FILE* fp, TmplName* tmplName);
void printQName (FILE* fp, QName* qName);
void printPrimType (FILE* fp, PrimType primType);
void printType (FILE* fp, Type* type, Derivation* derivation);
void printBaseType (FILE* fp, Type* type);
void printDeclaration (FILE* fp, Declaration* declaration);
void printExpression(FILE* fp, Expression* expression);
void printStatement(FILE* fp, Statement* statement);
void printFunction(FILE* fp, Function* function);


// ===== Helper Function Declarations =====

Type* getBaseType(Type* type);
void printBaseType (FILE* fp, Type* type);

Derivation* Derivation_nothing_create();
Derivation* Derivation_name_create(Name* name);
Derivation* Derivation_call_create(Derivation* derivation, int parameterCount, Declaration** parameterList);
Derivation* getDerivedDeclaration(Type* type, Derivation* derivation);

void printDerivedDeclaration(FILE* fp, Derivation* derivation);

#define ERR(message)  \
  printf("Error: %s\n", message)

// ===== Helper Structure Definitions =====

typedef enum DerivationKind { NOTHING , NAME , CALL } DerivationKind;
struct Derivation {
  DerivationKind kind;
  union {
    Name* name;
    struct {
      Derivation* derivation;
      int parameterCount; 
      Declaration** parameterList;
    } call;
  };
};

#endif

