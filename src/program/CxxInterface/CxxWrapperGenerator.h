
#include <stdio.h>
#include "CxxWrapperGeneratorTypes.h"
#include "CxxWrapperGeneratorPrint.h"
#include "Signature.h"

void printCxxFunction(FILE* fp, char* wrappedFunctionName, char* wrapperFunctionName, PyonSignature* pyonSignature);
Type* pyonToCxxType(Pool* p, PyonTypeTag tag);
Type* pyonToWrapperType(Pool* p, PyonTypeTag tag);
Function* createWrappedFunctionDeclaration(Pool* p, char* wrappedFunctionName, PyonSignature* pyonSignature);
Function* createWrapperFunctionDefinition(Pool* p, char* wrapperFunctionName, PyonSignature* pyonSignature, Function* wrappedFunction);
Name* newVariableName(Pool* p);

