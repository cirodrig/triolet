
#include <stdio.h>
#include <stdlib.h> 
#include "CxxWrapperGeneratorTypes.h"
#include "CxxWrapperGeneratorPrint.h"
#include "Signature.h"
#include "CxxWrapperGenerator.h"

unsigned int variableNameCounter = 0;

void 
printCxxFunction(FILE* fp, char* wrappedFunctionName, char* wrapperFunctionName, PyonSignature* pyonSignature) {

  Pool *p = Pool_create();

  // Generate Functions
  Function* wrappedFunction = createWrappedFunctionDeclaration(p, wrappedFunctionName, pyonSignature);
  Function* wrapperFunction = createWrapperFunctionDefinition(p, wrapperFunctionName, pyonSignature, wrappedFunction);

  // Print ASTs
  fputs("\n\n", fp);
  printFunction(fp, wrappedFunction);
  fputs("\n", fp);
  printFunction(fp, wrapperFunction);
  fputs("\n\n", fp);

  Pool_destroy(p);

}

Type* 
pyonToCxxType(Pool* p, PyonTypeTag tag) {
  switch (tag) {
    case PyonIntTag:
      return Type_primType_create(p, INT32_T);
      break;
    case PyonFloatTag:
      return Type_primType_create(p, FLOAT);
      break;
    case PyonBoolTag:
      return Type_primType_create(p, BOOL_TYPE);
      break;
    case PyonNoneTypeTag:
      return Type_primType_create(p, NONE_TYPE);
      break;
    default: ERR("invalid PyonTypeTag in function pyonToCxxType(Pool*,PyonTypeTag)");
  }
}

Type* 
pyonToWrapperType(Pool* p, PyonTypeTag tag) {
  Name* name;
  switch (tag) {
    case PyonIntTag:
      name = Name_create(p, "Int");
      break;
    case PyonFloatTag:
      name = Name_create(p, "Float");
      break;
    case PyonBoolTag:
      name = Name_create(p, "Bool");
      break;
    case PyonNoneTypeTag:
      name = Name_create(p, "NoneType");
      break;
    default: ERR("invalid PyonTypeTag in function pyonToWrapperType(Pool*,PyonTypeTag)");
  }
  TmplName* tmplName = TmplName_create(p, name, 0, NULL);
  QName* qName = QName_tmplName_create(p, tmplName);
  return Type_qName_create(p, qName);
}

Function* 
createWrappedFunctionDeclaration(Pool* p, char* wrappedFunctionName, PyonSignature* pyonSignature) {

  // Set return type
  Type* returnType = pyonToCxxType(p, pyonSignature->returnType->tag);
  
  // Extract parameters
  PyonTypes *pyonParameterTypes = pyonSignature->parameterTypes;
  int parameterCount = pyonParameterTypes->count;
  Declaration** parameterList = malloc(parameterCount*sizeof(Declaration*));
  int parameterIndex;
  for (parameterIndex=0; parameterIndex<parameterCount; parameterIndex++){
    Type* parameterType = pyonToCxxType(p, pyonParameterTypes->elems[parameterIndex]->tag);
    parameterList[parameterIndex] = Declaration_local_create(p, parameterType, newVariableName(p));
  }

  // Create signature
  Type* signatureType = Type_function_create(p, returnType, parameterCount, parameterList);
  Declaration* signature = Declaration_extern_c_create(p, signatureType, Name_create(p, wrappedFunctionName));

  return Function_declaration_create(p, signature);

}

Function* 
createWrapperFunctionDefinition(Pool* p, char* wrapperFunctionName, PyonSignature* pyonSignature, Function* wrappedFunction) {
  
  // Set return type
  Type* returnType = pyonToWrapperType(p, pyonSignature->returnType->tag);
  
  // Extract parameters
  PyonTypes *pyonParameterTypes = pyonSignature->parameterTypes;
  int parameterCount = pyonParameterTypes->count;
  Declaration** wrappedParameterList = wrappedFunction->signature->type->function.parameterList;
  Declaration** wrapperParameterList = malloc(parameterCount*sizeof(Declaration*));
  int parameterIndex;
  for (parameterIndex=0; parameterIndex<parameterCount; parameterIndex++){
    Type* parameterType = pyonToWrapperType(p, pyonParameterTypes->elems[parameterIndex]->tag);
    wrapperParameterList[parameterIndex] = Declaration_local_create(p, parameterType, newVariableName(p));
  }
  
  // Create signature
  Type* signatureType = Type_function_create(p, returnType, parameterCount, wrapperParameterList);
  Declaration* signature = Declaration_local_create(p, signatureType, Name_create(p, wrapperFunctionName));

  // Create declaration list
  DeclarationList* declarationList = DeclarationList_create(p);
  for (parameterIndex=0; parameterIndex<parameterCount; parameterIndex++){
    DeclarationList_append(p, declarationList, wrappedParameterList[parameterIndex]);
  }
  Name* returnVariableName = newVariableName(p);
  DeclarationList_append(p, declarationList, Declaration_local_create(p, pyonToCxxType(p, pyonSignature->returnType->tag), returnVariableName));
  
  // Create statement list
  StatementList* statementList = StatementList_create(p);
  Statement* statement;
  // Step 1: unwrap parameters
  for (parameterIndex=0; parameterIndex<parameterCount; parameterIndex++){
    TmplName* lhsTmplName = TmplName_create(p, wrappedParameterList[parameterIndex]->name, 0, NULL);
    QName *lhsObjectID = QName_tmplName_create(p, lhsTmplName);
    Expression* lhsExpression = Expression_objectID_create(p, lhsObjectID);
    TmplName* rhsCastTmplName = TmplName_create(p, wrapperParameterList[parameterIndex]->name, 0, NULL);
    QName* rhsCastQName = QName_tmplName_create(p, rhsCastTmplName);
    Expression* rhsExpression = Expression_cast_create(p, wrappedParameterList[parameterIndex]->type, rhsCastQName);
    statement = Statement_assignment_create(p, lhsExpression, rhsExpression);
    StatementList_append(p, statementList, statement);
  }
  // Step 2: invoke wrapped function
  // Step 2.1: generate the return variable expression for the left hand side (note: also used in return expression of step 3)
  TmplName* returnVariableTmplName = TmplName_create(p, returnVariableName, 0, NULL);
  QName *returnVariableObjectID = QName_tmplName_create(p, returnVariableTmplName);
  Expression* returnVariableExpression = Expression_objectID_create(p, returnVariableObjectID);
  // Step 2.2: generate function invokation for the right hand side
  TmplName* functionTmplName = TmplName_create(p, wrappedFunction->signature->name, 0, NULL);
  QName *functionQName = QName_tmplName_create(p, functionTmplName);
  Expression** argumentList = malloc(parameterCount*sizeof(Expression*));
  for (parameterIndex=0; parameterIndex<parameterCount; parameterIndex++){
    TmplName* argumentTmplName = TmplName_create(p, wrappedParameterList[parameterIndex]->name, 0, NULL);
    QName* argumentObjectID = QName_tmplName_create(p, argumentTmplName);
    Expression* argument = Expression_objectID_create(p, argumentObjectID);
    argumentList[parameterIndex] = argument;
  }
  Expression* functionInvocationExpression = Expression_function_call_create(p, functionQName, parameterCount, argumentList);
  // Step 2.3: combine and append to list
  statement = Statement_assignment_create(p, returnVariableExpression, functionInvocationExpression);
  StatementList_append(p, statementList, statement);
  // Step 3: wrap final value and return
  QName* constructorQName = returnType->qName;
  int argumentCount = 1;
  Expression** constructorArgumentList = malloc(argumentCount*sizeof(Expression*));
  constructorArgumentList[0] = returnVariableExpression;
  Expression* returnExpression = Expression_constructor_create(p, constructorQName, argumentCount, constructorArgumentList);
  statement = Statement_return_create(p, returnExpression);
  StatementList_append(p, statementList, statement);

  return Function_definition_create(p, signature, declarationList, statementList);
  
}

Name*
newVariableName(Pool* p)
{
  unsigned int n = variableNameCounter++;
  unsigned int digits = 1;
  {
    unsigned int limit = 10;
    while (n >= limit) limit *= 10, digits++;
  }
  char *s = malloc(digits + 3);
  sprintf(s, "x_%u", n);
  return Name_create(p, s);
}



/********************************************************************************
 **                        Example Wrapper Function                            **
 ********************************************************************************

      // WRAPPED FUNCTION
      bool sampleFunction(int_32 i,float f);

      // WRAPPER FUNCTION
      Bool sampleFunction_wrapper(Int i_wrapper, Float f_wrapper) {

        // DECLARATIONS
        int_32 i; // Function argument
        float f; // Function argument
        bool b; // Function return value
      
        // STATEMENTS
      
        // Step 1: unwrap parameters
        i = (int_32) i_wrapper;
        f = (float) f_wrapper;

        // Step 2: invoke wrapped function
        b = sampleFunction(i,f);

        // Step 3: wrap final value and return
        return Bool(b);

      }
  
 ********************************************************************************/

