
#include <stdio.h>
#include <stdlib.h> 
#include <string.h>
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
  fputs("\n#include <PyonData.h>\n\n", fp);
  printFunction(fp, wrappedFunction);
  fputs("\n", fp);
  printFunction(fp, wrapperFunction);
  fputs("\n\n", fp);

  Pool_destroy(p);

}

Function* 
createWrappedFunctionDeclaration(Pool* p, char* wrappedFunctionName, PyonSignature* pyonSignature) {

  // Declare parameter data
  int parameterCount = pyonSignature->parameterTypes->count;
  Declaration** parameterList;

  // Separate treatment of functions with val type and bare type return values (bare types have one extra parameter for returnung data and return type void)
  switch (pyonTypeKind(pyonSignature->returnType)) {
    case ValTypeTag: // Val Types
      parameterList = malloc(parameterCount*sizeof(Declaration*));
      populateWrappedParameterList(p, parameterList, pyonSignature->parameterTypes);
      break;
    case BareTypeTag: // Bare Types
      parameterCount++; // One extra parameter for the bare data returned
      parameterList = malloc(parameterCount*sizeof(Declaration*));
      populateWrappedParameterList(p, parameterList, pyonSignature->parameterTypes);
      Type* returnParameterType = pyonToWrappedParamType(p, pyonSignature->returnType); // Get final parameter type
      parameterList[parameterCount-1] = Declaration_local_create(p, returnParameterType, newVariableName(p)); // Add final parameter to list
      break;
    default: ERR("invalid PyonTypeTag in function createWrappedFunctionDeclaration(Pool*, char*, PyonSignature*)");
  }

  // Create function signature
  Type* returnType = pyonToWrappedReturnType(p, pyonSignature->returnType);
  Type* signatureType = Type_function_create(p, returnType, parameterCount, parameterList);
  Declaration* signature = Declaration_extern_c_create(p, signatureType, Name_create_dynamic(p, strdup(wrappedFunctionName)));

  return Function_declaration_create(p, signature);

}

Function* 
createWrapperFunctionDefinition(Pool* p, char* wrapperFunctionName, PyonSignature* pyonSignature, Function* wrappedFunction) {
  
  // Extract return type
  Type* returnType = pyonToWrapperParamAndReturnType(p, pyonSignature->returnType);
  
  // Extract parameters
  const PyonTypes *pyonParameterTypes = pyonSignature->parameterTypes;
  int parameterCount = pyonParameterTypes->count;
  Declaration** wrappedParameterList = wrappedFunction->signature->type->function.parameterList;
  Declaration** wrapperParameterList = malloc(parameterCount*sizeof(Declaration*));
  int parameterIndex;
  for (parameterIndex=0; parameterIndex<parameterCount; parameterIndex++){
    Type* parameterType = pyonToWrapperParamAndReturnType(p, pyonParameterTypes->elems[parameterIndex]);
    wrapperParameterList[parameterIndex] = Declaration_local_create(p, parameterType, newVariableName(p));
  }
  
  // Create signature
  Type* signatureType = Type_function_create(p, returnType, parameterCount, wrapperParameterList);
  Declaration* signature = Declaration_local_create(p, signatureType, Name_create_dynamic(p, strdup(wrapperFunctionName)));

  // Create declaration list
  DeclarationList* declarationList = DeclarationList_create(p);
  for (parameterIndex=0; parameterIndex<parameterCount; parameterIndex++){
    DeclarationList_append(p, declarationList, wrappedParameterList[parameterIndex]); // Reuse wrapped parameter list since the types will be the same
  }
  Name* returnVariableName = newVariableName(p);
  Type* returnVariableType = pyonToWrapperReturnDeclarationType(p, pyonSignature->returnType);
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
  switch (pyonTypeKind(pyonSignature->returnType)) {
    case ValTypeTag: { // Val Types
      // Step 2: invoke wrapped function
      // Step 2.1: generate the return variable expression for the left hand side (note: also used in return expression of step 3)
      Expression* returnVariableExpression = nameToObjectIDExpression(p, returnVariableName);
      // Step 2.2: generate function invokation for the right hand side
      TmplName* functionTmplName = TmplName_create_zero_types(p, wrappedFunction->signature->name);
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
    case BareTypeTag: { // Bare Types
      // Step 2: invoke wrapped function
      // Step 2.0: before invoking the function, return variable must be allocated
      Expression* returnVariableExpression = nameToObjectIDExpression(p, returnVariableName);
      Expression* memberAccessExpression = Expression_member_access_create(p, returnVariableExpression, Name_create_static(p, "allocate"));
      Expression* allocateExpression = Expression_function_call_create(p, memberAccessExpression, 0, NULL);
      Statement* statement = Statement_expression_create(p, allocateExpression);
      StatementList_append(p, statementList, statement);
      // Step 2.1: no left hand side
      // Step 2.2: generate function invokation for the right hand side
      TmplName* functionTmplName = TmplName_create_zero_types(p, wrappedFunction->signature->name);
      QName *functionQName = QName_tmplName_create(p, functionTmplName);
      Expression** argumentList = malloc( (parameterCount+1) * sizeof(Expression*) ); // One extra parameter for returned bare data
      populateArgumentList(p, argumentList, wrappedParameterList, parameterCount);
      memberAccessExpression = Expression_member_access_create(p, returnVariableExpression, Name_create_static(p, "getObject")); // Final parameter is returnVariable.getBareData()
      argumentList[parameterCount] = Expression_function_call_create(p, memberAccessExpression, 0, NULL); // Add final parameter to list
      Expression* functionQNameExpression = Expression_objectID_create(p, functionQName);
      Expression* functionInvocationExpression = Expression_function_call_create(p, functionQNameExpression, parameterCount + 1, argumentList); // One extra parameter
      // Step 2.3: append to list (no assignment)
      statement = Statement_expression_create(p, functionInvocationExpression);
      StatementList_append(p, statementList, statement);
      // Step 3: invoke freeze() and return
      memberAccessExpression = Expression_member_access_create(p, returnVariableExpression, Name_create_static(p, "freeze"));
      Expression* returnExpression = Expression_function_call_create(p, memberAccessExpression, 0, NULL);
      statement = Statement_return_create(p, returnExpression);
      StatementList_append(p, statementList, statement);
      break;
    }
    default: ERR("invalid PyonTypeTag in function createWrapperFunctionDefinition(Pool*, char*, PyonSignature*, Function*)");
  }

  return Function_definition_create(p, signature, declarationList, statementList);
  
}

Statement*
createUnwrappingStatement(Pool* p, const PyonType* pyonType, Declaration* wrappedVariable, Declaration* wrapperVariable) {

  // Left hand side (lhs)
  Expression* lhsExpression = nameToObjectIDExpression(p, wrappedVariable->name);

  // Right hand side (rhs)
  TmplName* rhsVariableTmplName = TmplName_create_zero_types(p, wrapperVariable->name);
  QName* rhsVariableQName = QName_tmplName_create(p, rhsVariableTmplName);
  Expression* rhsExpression;
  switch (pyonTypeKind(pyonType)) {
    case ValTypeTag:
      rhsExpression = Expression_cast_create(p, wrappedVariable->type, rhsVariableQName);
      break;
    case BareTypeTag: {
      Expression* objectID = Expression_objectID_create(p, rhsVariableQName);
      Expression* memberAccessExpression = Expression_member_access_create(p, objectID, Name_create_static(p, "getBareData"));
      rhsExpression = Expression_function_call_create(p, memberAccessExpression, 0, NULL);
      break;
    }
    default: ERR("invalid PyonTypeTag in function createUnwrappingStatement(Pool*,PyonType*,Declaration*,Declaration*)");
  }

  // lhs = rhs
  return Statement_assignment_create(p, lhsExpression, rhsExpression);

}

Type* 
pyonToWrappedValType(Pool* p, const PyonType* pyonType) {
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
    default: ERR("invalid PyonTypeTag in function pyonToWrappedValType(Pool*,PyonType*)");
  }
}

Type* pyonToWrappedParamType(Pool* p, const PyonType* pyonType) {
  switch(pyonTypeKind(pyonType)) {
    case ValTypeTag:
      return pyonToWrappedValType(p, pyonType);
      break;
    case BareTypeTag:
      return createTmplNameInNamespace (p, TmplName_create_zero_types(p, Name_create_static(p, "PyonBarePtr")));
      break;
    default: ERR("invalid TypeKindTag in function pyonToWrappedParamType(Pool*, PyonType*)");
  }
}

Type* pyonToWrappedReturnType(Pool* p, const PyonType* pyonType) {
  switch(pyonTypeKind(pyonType)) {
    case ValTypeTag:
      return pyonToWrappedValType(p, pyonType);
      break;
    case BareTypeTag:
      return Type_primType_create(p, VOID);
      break;
    default: ERR("invalid TypeKindTag in function pyonToWrappedReturnType(Pool*, PyonType*)");
  }
}

Type* pyonToWrapperParamAndReturnType(Pool* p, const PyonType* pyonType) {
  return pyonToWrapperType(p, pyonType);
}

Type* pyonToWrapperReturnDeclarationType(Pool* p, const PyonType* pyonType) {
  switch (pyonTypeKind(pyonType)) {
    case ValTypeTag:
      return pyonToWrappedValType(p, pyonType);
      break;
    case BareTypeTag: {
      Type** typeList = malloc(sizeof(Type*));
      typeList[0] = pyonToWrapperType(p, pyonType);
      TmplName* tmplName = TmplName_create(p, Name_create_static(p, "Incomplete"), 1, typeList);
      return createTmplNameInNamespace (p, tmplName);
      break;
    }
    default: ERR("invalid TypeKindTag in function pyonToWrapperReturnType(Pool*, PyonType*)");
  }
}

Type* 
pyonToWrapperType(Pool* p, const PyonType* pyonType) {
  switch (pyonType->tag) {
    case PyonIntTag:
      return createTmplNameInNamespace (p, TmplName_create_zero_types(p, Name_create_static(p, "Int")));
      break;
    case PyonFloatTag:
      return createTmplNameInNamespace (p, TmplName_create_zero_types(p, Name_create_static(p, "Float")));
      break;
    case PyonBoolTag:
      return createTmplNameInNamespace (p, TmplName_create_zero_types(p, Name_create_static(p, "Bool")));
      break;
    case PyonNoneTypeTag:
      return createTmplNameInNamespace (p, TmplName_create_zero_types(p, Name_create_static(p, "NoneType")));
      break;
    case PyonTupleTypeTag: {
      int templateCount = pyonType->tuple.count;
      Type** typeList = malloc(templateCount*sizeof(Type*));
      int typeIndex;
      for (typeIndex=0; typeIndex<templateCount; typeIndex++) {
        typeList[typeIndex] = pyonToWrapperType(p, pyonType->tuple.elems[typeIndex]);
      }
      TmplName* tmplName = TmplName_create(p, Name_create_static(p, "Tuple"), templateCount, typeList);
      return createTmplNameInNamespace (p, tmplName);
      break;
    }
    case PyonListTypeTag: {
      // Create either a "List" or "BList" type
      const char *list_name = pyonType->list.boxed ? "BList" : "List";
      Type** typeList = malloc(sizeof(Type*));
      typeList[0] = pyonToWrapperType(p, pyonType->list.elem);
      TmplName* tmplName =
        TmplName_create(p, Name_create_static(p, list_name), 1, typeList);
      return createTmplNameInNamespace (p, tmplName);
      break;
    }
    case PyonArrayTypeTag: {
      Type** typeList = malloc(sizeof(Type*));
      typeList[0] = pyonToWrapperType(p, pyonType->array.elem);
      // Allocate string
      // 6 ("BArray") + 1 (dimension digit) + 1 (null terminator) = 8
      char *nameString = malloc(8*sizeof(char));
      if (pyonType->array.boxed) {
        sprintf(nameString, "BArray%d", pyonType->array.dimensionality);
      }
      else {
        sprintf(nameString, "Array%d", pyonType->array.dimensionality);
      }
      TmplName* tmplName = TmplName_create(p, Name_create_dynamic(p, nameString), 1, typeList);
      return createTmplNameInNamespace (p, tmplName);
      break;
    }
    default: ERR("invalid PyonTypeTag in function pyonToWrapperType(Pool*,PyonType*)");
  }
}

TypeKindTag pyonTypeKind(const PyonType *pyonType) {
  switch (pyonType->tag) {
    case PyonIntTag: case PyonFloatTag: case PyonBoolTag: case PyonNoneTypeTag:
      return ValTypeTag;
      break;
    case PyonTupleTypeTag: case PyonListTypeTag: case PyonArrayTypeTag:
      return BareTypeTag;
      break;
    default: ERR("invalid PyonTypeTag in function pyonTypeKind(PyonType*)");
  }
}

void 
populateWrappedParameterList(Pool* p, Declaration** parameterList, const PyonTypes* pyonParameterTypes) {
  int parameterCount = pyonParameterTypes->count;
  int parameterIndex;
  for (parameterIndex=0; parameterIndex<parameterCount; parameterIndex++){
    Type* parameterType = pyonToWrappedParamType(p, pyonParameterTypes->elems[parameterIndex]);
    parameterList[parameterIndex] = Declaration_local_create(p, parameterType, newVariableName(p));
  }
}

void 
populateArgumentList(Pool* p, Expression** argumentList, Declaration** wrappedParameterList, int parameterCount) {
  int parameterIndex;
  for (parameterIndex=0; parameterIndex<parameterCount; parameterIndex++){
    argumentList[parameterIndex] = nameToObjectIDExpression(p, wrappedParameterList[parameterIndex]->name);;
  }
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
  return Name_create_dynamic(p, s);
}

Type*
createTmplNameInNamespace (Pool* p, TmplName* tmplName) {
      QName* qName = QName_tmplName_create(p, tmplName);
      qName = QName_namespace_qName_create(p, Name_create_static(p, "Pyon"), qName);
      return Type_qName_create(p, qName);
}

Expression* 
nameToObjectIDExpression(Pool* p, Name* name) {
    TmplName* tmplName = TmplName_create_zero_types(p, name);
    QName* objectID = QName_tmplName_create(p, tmplName);
    Expression* expression = Expression_objectID_create(p, objectID);
    return expression;
}




/*******************************************************************************
 **                       Example Wrapper Function                            **
 *******************************************************************************

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
  
 ******************************************************************************/

