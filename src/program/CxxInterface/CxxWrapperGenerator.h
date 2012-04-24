
#include <stdio.h>
#include "CxxWrapperGeneratorTypes.h"
#include "CxxWrapperGeneratorPrint.h"
#include "Signature.h"

typedef enum TypeKindTag { ValTypeTag , BareTypeTag } TypeKindTag;

void printCxxFunction(FILE* fp, char* wrappedFunctionName, char* wrapperFunctionName, PyonSignature* pyonSignature);

Function* createWrappedFunctionDeclaration(Pool* p, char* wrappedFunctionName, PyonSignature* pyonSignature);
Function* createWrapperFunctionDefinition(Pool* p, char* wrapperFunctionName, PyonSignature* pyonSignature, Function* wrappedFunction);

Statement* createUnwrappingStatement(Pool* p, const PyonType* pyonType, Declaration* wrappedVariable, Declaration* wrapperVariable);

Type* pyonToWrappedValType(Pool* p, const PyonType* pyonType);
Type* pyonToWrappedParamType(Pool* p, const PyonType* pyonType);
Type* pyonToWrappedReturnType(Pool* p, const PyonType* pyonType);
Type* pyonToWrapperParamAndReturnType(Pool* p, const PyonType* pyonType);
Type* pyonToWrapperReturnDeclarationType(Pool* p, const PyonType* pyonType);
Type* pyonToWrapperType(Pool* p, const PyonType* pyonType);
TypeKindTag pyonTypeKind(const PyonType *pyonType);

int populateWrappedParameterList(Pool* p, Declaration** parameterList, const PyonTypes* pyonParameterTypes);
void populateArgumentList(Pool* p, Expression** argumentList, Declaration** wrappedParameterList, int parameterCount);

Name* newVariableName(Pool* p);
Type* createTmplNameInNamespace (Pool* p, TmplName* tmplName);
Expression* nameToObjectIDExpression(Pool* p, Name* name);

