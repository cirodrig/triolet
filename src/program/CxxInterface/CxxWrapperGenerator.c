
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
  fputs("\n#include <PyonData.h>\n\n", fp); // TODO: make sure this is the right file
  printFunction(fp, wrappedFunction);
  fputs("\n", fp);
  printFunction(fp, wrapperFunction);
  fputs("\n\n", fp);

  Pool_destroy(p);

}

void 
populateWrappedParameterList(Pool* p, Declaration** parameterList, const PyonTypes* pyonParameterTypes) {

  int parameterCount = pyonParameterTypes->count;
  int parameterIndex;
  for (parameterIndex=0; parameterIndex<parameterCount; parameterIndex++){
    Type* parameterType = pyonToWrappedType(p, pyonParameterTypes->elems[parameterIndex]);
    parameterList[parameterIndex] = Declaration_local_create(p, parameterType, newVariableName(p));
  }

}

Function* 
createWrappedFunctionDeclaration(Pool* p, char* wrappedFunctionName, PyonSignature* pyonSignature) {

  // Extract return type
  Type* returnType = pyonToWrappedType(p, pyonSignature->returnType);

  // Declare parameter data
  const PyonTypes *pyonParameterTypes = pyonSignature->parameterTypes;
  int parameterCount = pyonParameterTypes->count;
  Declaration** parameterList;

  // Separate treatment of functions with val type and bare type return values (bare types have one extra parameter for returnung data and return type void)
  switch (pyonSignature->returnType->tag) {
    case PyonIntTag: case PyonFloatTag: case PyonBoolTag: case PyonNoneTypeTag: // Val Types
      // Create parameter list
      parameterList = malloc(parameterCount*sizeof(Declaration*));
      populateWrappedParameterList(p, parameterList, pyonParameterTypes);
      break;
    case PyonTupleTypeTag: // Bare Types
      // Create parameter list
      parameterCount++; // One extra parameter for the bare data returned
      parameterList = malloc(parameterCount*sizeof(Declaration*));
      populateWrappedParameterList(p, parameterList, pyonParameterTypes);
      // Manage returned data
      parameterList[parameterCount-1] = Declaration_local_create(p, returnType, newVariableName(p)); // Add last parameter for returned data
      returnType = Type_primType_create(p, VOID); // Change return type to void
      break;
    default: ERR("invalid PyonTypeTag in function createWrappedFunctionDeclaration(Pool*, char*, PyonSignature*)");
  }

  // Create function signature
  Type* signatureType = Type_function_create(p, returnType, parameterCount, parameterList);
  Declaration* signature = Declaration_extern_c_create(p, signatureType, Name_create(p, wrappedFunctionName));

  return Function_declaration_create(p, signature);

}

void 
populateArgumentList(Pool* p, Expression** argumentList, Declaration** wrappedParameterList, int parameterCount) {
  int parameterIndex;
  for (parameterIndex=0; parameterIndex<parameterCount; parameterIndex++){
    TmplName* argumentTmplName = TmplName_create(p, wrappedParameterList[parameterIndex]->name, 0, NULL);
    QName* argumentObjectID = QName_tmplName_create(p, argumentTmplName);
    Expression* argument = Expression_objectID_create(p, argumentObjectID);
    argumentList[parameterIndex] = argument;
  }
}


Function* 
createWrapperFunctionDefinition(Pool* p, char* wrapperFunctionName, PyonSignature* pyonSignature, Function* wrappedFunction) {
  
  // Extract return type
  Type* returnType = pyonToWrapperType(p, pyonSignature->returnType);
  
  // Extract parameters
  const PyonTypes *pyonParameterTypes = pyonSignature->parameterTypes;
  int parameterCount = pyonParameterTypes->count;
  Declaration** wrappedParameterList = wrappedFunction->signature->type->function.parameterList;
  Declaration** wrapperParameterList = malloc(parameterCount*sizeof(Declaration*));
  int parameterIndex;
  for (parameterIndex=0; parameterIndex<parameterCount; parameterIndex++){
    Type* parameterType = pyonToWrapperType(p, pyonParameterTypes->elems[parameterIndex]);
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
  // Separate return varibale treatment of functions with val type and bare type return values
  Name* returnVariableName = newVariableName(p);
  Type* returnVariableType;
  switch (pyonSignature->returnType->tag) {
    case PyonIntTag: case PyonFloatTag: case PyonBoolTag: case PyonNoneTypeTag: // Val Types
      returnVariableType = pyonToWrappedType(p, pyonSignature->returnType);
      break;
    case PyonTupleTypeTag: { // Bare Types (surround wrapper type with Incomplete<>)
      Type** typeList = malloc(1*sizeof(Type*));
      typeList[0] = pyonToWrapperType(p, pyonSignature->returnType);
      TmplName* tmplName = TmplName_create(p, Name_create(p, "Incomplete"), 1, typeList);
      QName* qName = QName_tmplName_create(p, tmplName);
      qName = QName_namespace_qName_create(p, Name_create(p, "Pyon"), qName);
      returnVariableType = Type_qName_create(p, qName);
      break;
    }
    default: ERR("invalid PyonTypeTag in function createWrapperFunctionDefinition(Pool*, char*, PyonSignature*, Function*)");
  }
  DeclarationList_append(p, declarationList, Declaration_local_create(p, returnVariableType, returnVariableName));
  
  // Create statement list
  StatementList* statementList = StatementList_create(p);
  // Step 1: unwrap parameters
  for (parameterIndex=0; parameterIndex<parameterCount; parameterIndex++){
    Statement* unwrappingStatement = 
      createUnwrappingStatement(p, pyonParameterTypes->elems[parameterIndex], wrappedParameterList[parameterIndex], wrapperParameterList[parameterIndex]);
    StatementList_append(p, statementList, unwrappingStatement);
  }
  // Separate function invocation treatment of functions with val type and bare type return values
  switch (pyonSignature->returnType->tag) {
    case PyonIntTag: case PyonFloatTag: case PyonBoolTag: case PyonNoneTypeTag: { // Val Types
      // Step 2: invoke wrapped function
      // Step 2.1: generate the return variable expression for the left hand side (note: also used in return expression of step 3)
      TmplName* returnVariableTmplName = TmplName_create(p, returnVariableName, 0, NULL);
      QName *returnVariableObjectID = QName_tmplName_create(p, returnVariableTmplName);
      Expression* returnVariableExpression = Expression_objectID_create(p, returnVariableObjectID);
      // Step 2.2: generate function invokation for the right hand side
      TmplName* functionTmplName = TmplName_create(p, wrappedFunction->signature->name, 0, NULL);
      QName *functionQName = QName_tmplName_create(p, functionTmplName);
      Expression** argumentList = malloc(parameterCount*sizeof(Expression*));
      populateArgumentList(p, argumentList, wrappedParameterList, parameterCount);
      Expression* functionQNameExpression = Expression_objectID_create(p, functionQName);
      Expression* functionInvocationExpression = Expression_function_call_create(p, functionQNameExpression, parameterCount, argumentList);
      // Step 2.3: combine in assignment and append to list
      Statement* statement = Statement_assignment_create(p, returnVariableExpression, functionInvocationExpression);
      StatementList_append(p, statementList, statement);
      // Step 3: wrap final value and return
      QName* constructorQName = returnType->qName;
      int argumentCount = 1;
      Expression** constructorArgumentList = malloc(argumentCount*sizeof(Expression*));
      constructorArgumentList[0] = returnVariableExpression;
      Expression* returnExpression = Expression_constructor_create(p, constructorQName, argumentCount, constructorArgumentList);
      statement = Statement_return_create(p, returnExpression);
      StatementList_append(p, statementList, statement);
      break;
    }
    case PyonTupleTypeTag: { // Bare Types
      // Step 2: invoke wrapped function
      // Step 2.0: before invoking the function, return variable must be allocated
      TmplName* returnVariableTmplName = TmplName_create(p, returnVariableName, 0, NULL);
      QName *returnVariableObjectID = QName_tmplName_create(p, returnVariableTmplName);
      Expression* returnVariableExpression = Expression_objectID_create(p, returnVariableObjectID);
      Expression* memberAccessExpression = Expression_member_access_create(p, returnVariableExpression, Name_create(p, "allocate"));
      Expression* allocateExpression = Expression_function_call_create(p, memberAccessExpression, 0, NULL);
      Statement* statement = Statement_expression_create(p, allocateExpression);
      StatementList_append(p, statementList, statement);
      // Step 2.1: no left hand side
      // Step 2.2: generate function invokation for the right hand side
      TmplName* functionTmplName = TmplName_create(p, wrappedFunction->signature->name, 0, NULL);
      QName *functionQName = QName_tmplName_create(p, functionTmplName);
      Expression** argumentList = malloc( (parameterCount+1) * sizeof(Expression*) ); // One extra parameter for returned bare data
      populateArgumentList(p, argumentList, wrappedParameterList, parameterCount);
      memberAccessExpression = Expression_member_access_create(p, returnVariableExpression, Name_create(p, "getObject")); // Final parameter is returnVariable.getBareData()
      argumentList[parameterCount] = Expression_function_call_create(p, memberAccessExpression, 0, NULL); // Add final parameter to list
      Expression* functionQNameExpression = Expression_objectID_create(p, functionQName);
      Expression* functionInvocationExpression = Expression_function_call_create(p, functionQNameExpression, parameterCount + 1, argumentList); // One extra parameter
      // Step 2.3: append to list (no assignment)
      statement = Statement_expression_create(p, functionInvocationExpression);
      StatementList_append(p, statementList, statement);
      // Step 3: invoke freeze() and return
      memberAccessExpression = Expression_member_access_create(p, returnVariableExpression, Name_create(p, "freeze"));
      Expression* returnExpression = Expression_function_call_create(p, memberAccessExpression, 0, NULL);
      statement = Statement_return_create(p, returnExpression);
      StatementList_append(p, statementList, statement);
      break;
    }
    default: ERR("invalid PyonTypeTag in function createWrapperFunctionDefinition(Pool*, char*, PyonSignature*, Function*)");
  }

  return Function_definition_create(p, signature, declarationList, statementList);
  
}

Type* 
pyonToWrappedType(Pool* p, const PyonType* pyonType) {
  switch (pyonType->tag) {
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
    case PyonTupleTypeTag: 
    { 
      TmplName* tmplName = TmplName_create(p, Name_create(p, "PyonBarePtr"), 0, NULL);
      QName* qName = QName_tmplName_create(p, tmplName);
      qName = QName_namespace_qName_create(p, Name_create(p, "Pyon"), qName);
      return Type_qName_create(p, qName);
      break;
    }
    default: ERR("invalid PyonTypeTag in function pyonToWrappedType(Pool*,PyonType*)");
  }
}

Type* 
pyonToWrapperType(Pool* p, const PyonType* pyonType) {
  Name* name;
  int tupleDimension;
  Type** typeList;
  switch (pyonType->tag) { // TODO: include namespace "Pyon::"
    case PyonIntTag:
      name = Name_create(p, "Int");
      tupleDimension = 0;
      typeList = NULL;
      break;
    case PyonFloatTag:
      name = Name_create(p, "Float");
      tupleDimension = 0;
      typeList = NULL;
      break;
    case PyonBoolTag:
      name = Name_create(p, "Bool");
      tupleDimension = 0;
      typeList = NULL;
      break;
    case PyonNoneTypeTag:
      name = Name_create(p, "NoneType");
      tupleDimension = 0;
      typeList = NULL;
      break;
    case PyonTupleTypeTag:
      name = Name_create(p, "Tuple");
      tupleDimension = pyonType->tuple.count;
      typeList = malloc(tupleDimension*sizeof(Type*));
      int typeIndex;
      for (typeIndex=0; typeIndex<tupleDimension; typeIndex++) {
        typeList[typeIndex] = pyonToWrapperType(p, pyonType->tuple.elems[typeIndex]);
      }
      break;
    default: ERR("invalid PyonTypeTag in function pyonToWrapperType(Pool*,PyonType*)");
  }
  TmplName* tmplName = TmplName_create(p, name, tupleDimension, typeList);
  QName* qName = QName_tmplName_create(p, tmplName);
  qName = QName_namespace_qName_create(p, Name_create(p, "Pyon"), qName);
  return Type_qName_create(p, qName);
}

Statement*
createUnwrappingStatement(Pool* p, const PyonType* pyonType, Declaration* wrappedVariable, Declaration* wrapperVariable) {

  // Left hand side (lhs)
  TmplName* lhsTmplName = TmplName_create(p, wrappedVariable->name, 0, NULL);
  QName *lhsObjectID = QName_tmplName_create(p, lhsTmplName);
  Expression* lhsExpression = Expression_objectID_create(p, lhsObjectID);

  // Right hand side (rhs)
  TmplName* rhsVariableTmplName = TmplName_create(p, wrapperVariable->name, 0, NULL);
  QName* rhsVariableQName = QName_tmplName_create(p, rhsVariableTmplName);
  Expression* rhsExpression;
  switch (pyonType->tag) {
    case PyonIntTag: case PyonFloatTag: case PyonBoolTag: case PyonNoneTypeTag:
      rhsExpression = Expression_cast_create(p, wrappedVariable->type, rhsVariableQName);
      break;
    case PyonTupleTypeTag: {
      Expression* objectID = Expression_objectID_create(p, rhsVariableQName);
      Expression* memberAccessExpression = Expression_member_access_create(p, objectID, Name_create(p, "getBareData"));
      rhsExpression = Expression_function_call_create(p, memberAccessExpression, 0, NULL);
      break;
    }
    default: ERR("invalid PyonTypeTag in function createUnwrappingStatement(Pool*,PyonType*,Declaration*,Declaration*)");
  }

  // lhs = rhs
  return Statement_assignment_create(p, lhsExpression, rhsExpression);

}

Name*
newVariableName(Pool* p) {
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
      bool sampleFunction(int_32 i,float f, PyonBarePtr tuple);

      // WRAPPER FUNCTION
      Bool sampleFunction_wrapper(Int i_wrapper, Float f_wrapper, Tuple<T1,T2> t) {

        // DECLARATIONS
        int_32 i; // Function argument
        float f; // Function argument
        PyonBarePtr t; // Function argument
        bool b; // Function return value
      
        // STATEMENTS
      
        // Step 1: unwrap parameters
        i = (int_32) i_wrapper;
        f = (float) f_wrapper;
        t = t.getBareData();

        // Step 2: invoke wrapped function
        b = sampleFunction(i,f,t);

        // Step 3: wrap final value and return
        return Bool(b);

      }
  
 ********************************************************************************/

