
#include <stdio.h>
#include <stdlib.h>
#include "CxxInterface/CxxWrapperGeneratorPrint.h"

// ===== Printing Function Definitions =====

void 
printName(FILE* fp, Name* name) {
  fputs(name->nameString, fp);
}

void 
printTmplName (FILE* fp, TmplName* tmplName) { // name < typeList[0], typeList[1], .. >
  printName(fp, (void*) tmplName->name);
  int index;
  for (index=0; index<tmplName->typeCount; index++) {
    if (index==0) {fputs("<", fp);}
    printType(fp, tmplName->typeList[index], Derivation_nothing_create());
    if (index < tmplName->typeCount - 1){
      fputs(", ", fp);
    } else {
      fputs(">", fp);
    }
  }
}

void 
printQName(FILE* fp, QName* qName) {
  switch (qName->kind) {
    case NAMESPACE_QNAME: // namespaceName::qName
      printName(fp, (void*) qName->namespace_qName.namespaceName);
      fputs("::", fp);
      printQName(fp, qName->namespace_qName.qName);
      break;
    case TMPLNAME_QNAME: // tmplName::qName
      printTmplName(fp, qName->tmplName_qName.tmplName);
      fputs("::", fp);
      printQName(fp, qName->tmplName_qName.qName);
      break;
    case TMPLNAME: // tmplName
      printTmplName(fp, qName->tmplName);
      break;
    default: ERR("invalid QName kind");
  }
}

void 
printPrimType(FILE* fp, PrimType primType) {
  switch (primType) {
    case INT32_T:
      fputs("int32_t", fp);
      break;
    case FLOAT:
      fputs("float", fp);
      break;
    case BOOL_TYPE:
      fputs("int", fp);
      break;
    case NONE_TYPE:
      fputs("int", fp);
      break;
    case VOID:
      fputs("void", fp);
      break;
    default: ERR("invalid PrimType");
  }
}

void 
printType (FILE* fp, Type* type, Derivation* derivation) {
  printBaseType(fp, getBaseType(type));
  fputs(" ", fp);
  printDerivedDeclaration(fp, getDerivedDeclaration(type, derivation));
}

void 
printDeclaration (FILE* fp, Declaration* declaration) {
  switch (declaration->kind) {
    case EXTERN_C:
      fputs("extern \"C\" ", fp);
      break;
    case STATIC:
      fputs("static ", fp);
      break;
    case LOCAL:
      break;
    default: ERR("invalid Declaration kind");
  }
  printType(fp, declaration->type, Derivation_name_create(declaration->name));
}

void 
printExpression(FILE* fp, Expression* expression) {
  switch (expression->kind) {
    case OBJECTID: // id
      printQName(fp, expression->objectID);
      break;
    case CAST: // (type) qName
      fputs("(", fp);
      printType(fp, expression->cast.type, Derivation_nothing_create());
      fputs(") ", fp);
      printQName(fp, expression->cast.qName);
      break;
    case CONSTRUCTOR: // new qName (expressionList[0], expressionList[1], ...)
      printQName(fp, expression->constructorInvocation.qName);
      fputs("(", fp);
      { int index;
        for (index=0; index<expression->constructorInvocation.argumentCount; index++) {
          printExpression(fp, expression->constructorInvocation.argumentList[index]);
          if (index < expression->constructorInvocation.argumentCount-1) {fputs(", ", fp);}
        }
      }
      fputs(")", fp);
      break;
    case FUNCTION_CALL: // exprerssion (expressionList[0], expressionList[1], ...)
      printExpression(fp, expression->functionCall.expression);
      fputs("(", fp);
      { int index;
        for (index=0; index<expression->functionCall.argumentCount; index++) {
          printExpression(fp, expression->functionCall.argumentList[index]);
          if (index < expression->functionCall.argumentCount-1) {fputs(", ", fp);}
        }
       }
      fputs(")", fp);
      break;
    case MEMBER_ACCESS: // (exprerssion).name
      fputs("(", fp);
      printExpression(fp, expression->memberAccess.expression);
      fputs(").", fp);
      printName(fp, expression->memberAccess.name);
      break;
    default: ERR("invalid Expression kind");
  }
}

void 
printStatement(FILE* fp, Statement* statement){
  switch (statement->kind) {
    case ASSIGNMENT: // expression1 = expression2
      printExpression(fp, statement->assignment.lhsExpression);
      fputs(" = ", fp);
      printExpression(fp, statement->assignment.rhsExpression);
      break;
    case EXPRESSION: // expression
      printExpression(fp, statement->expression);
      break;
    case RETURN: // return expression
      fputs("return ", fp);
      printExpression(fp, statement->returnStatement);
      break;
    default: ERR("invalid Statement kind");
  }
  fputs(";\n", fp);
}

void 
printFunction(FILE* fp, Function* function){
  printDeclaration(fp, function->signature);
  switch (function->kind) {
    case DECLARATION:
      fputs(";\n", fp);
      break;
    case DEFINITION:
      fputs(" {\n", fp);
      BEGIN_FOR_DECLARATION(currentDNode,function->declarationList) {
        fputs("\t", fp);
        printDeclaration(fp, currentDNode->declaration);
        fputs(";\n", fp);
      }
      BEGIN_FOR_STATEMENT(currentSNode,function->statementList) {
        fputs("\t", fp);
        printStatement(fp, currentSNode->statement);
      }
      fputs("}\n", fp);
      break;
    default: ERR("invalid Function kind");
  }
}

// ===== Helper Structure and Function Definitions =====

Derivation* 
Derivation_nothing_create(){
  Derivation* derivation = malloc(sizeof(Derivation));
  derivation->kind = NOTHING;
  return derivation;
}

Derivation* 
Derivation_name_create(Name* name){
  Derivation* derivation = malloc(sizeof(Derivation));
  derivation->kind = NAME;
  derivation->name = name;
  return derivation;
}

Derivation* 
Derivation_call_create(Derivation* derivation, int parameterCount, Declaration** parameterList){
  Derivation* derivation_ret = malloc(sizeof(Derivation));
  derivation_ret->kind = CALL;
  derivation_ret->call.derivation = derivation;
  derivation_ret->call.parameterCount = parameterCount;
  derivation_ret->call.parameterList = parameterList;
  return derivation_ret;
}

Derivation* 
getDerivedDeclaration(Type* type, Derivation* derivation) {
  switch (type->kind) {
    case QNAME:
      return derivation;
    case PRIMTYPE:
      return derivation;
    case FUNCTION:
      return getDerivedDeclaration(type->function.returnType, 
          Derivation_call_create(derivation, type->function.parameterCount, type->function.parameterList));
    default: ERR("invalid Type kind in function getDerivedDeclaration()");
  }
}

void 
printDerivedDeclaration(FILE* fp, Derivation* derivation) {
  switch (derivation->kind) {
    case NOTHING:
      break;
    case NAME:  
      printName(fp, derivation->name);
      break;
    case CALL:
      printDerivedDeclaration(fp, derivation->call.derivation);
      fputs("(", fp);
      int index;
      for(index=0; index<derivation->call.parameterCount; index++) {
        printDeclaration(fp, derivation->call.parameterList[index]);
        if (index < derivation->call.parameterCount-1) {
          fputs(", ", fp);
        } else {
          fputs(")", fp);
        }
      }
      break;
    default: ERR("invalid Derivation kind");
  }
}

Type* 
getBaseType(Type* type) {
  switch (type->kind) {
    case QNAME:
      return type;
    case PRIMTYPE:
      return type;
    case FUNCTION:
      return getBaseType(type->function.returnType);
    default: ERR("invalid Type kind in function getBaseType(Type*)");
  }
}

void 
printBaseType (FILE* fp, Type* type) {
  switch (type->kind) {
    case QNAME:
      printQName(fp, type->qName);
      break;
    case PRIMTYPE:
      printPrimType(fp, type->primType);
      break;
    default: ERR("invalid Type kind");
  }
}

