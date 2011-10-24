
#include <stdio.h>
#include "CxxWrapperGeneratorTypes.h"
#include "CxxWrapperGeneratorPrint.h"
#include "Signature.h"

void printCxxFunction(FILE* fp, char* wrappedFunctionName, char* wrapperFunctionName, PyonSignature* pyonSignature);
Function* createWrappedFunctionDeclaration(Pool* p, char* wrappedFunctionName, PyonSignature* pyonSignature);
Function* createWrapperFunctionDefinition(Pool* p, char* wrapperFunctionName, PyonSignature* pyonSignature, Function* wrappedFunction);
void populateWrappedParameterList(Pool* p, Declaration** parameterList, const PyonTypes* pyonParameterTypes);
void populateArgumentList(Pool* p, Expression** argumentList, Declaration** wrappedParameterList, int parameterCount);
Type* pyonToWrappedType(Pool* p, const PyonType* pyonType);
Type* pyonToWrapperType(Pool* p, const PyonType* pyonType);
Statement* createUnwrappingStatement(Pool* p, const PyonType* pyonType, Declaration* wrappedVariable, Declaration* wrapperVariable);
Name* newVariableName(Pool* p);

