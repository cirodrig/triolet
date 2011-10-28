
#include <stddef.h>
#include <stdlib.h>
#include "cutils/Pool.h"
#include "CxxInterface/CxxWrapperGeneratorTypes.h"

// Name

void 
finalize_Name (Name *name) {
  if(name->isDynamic) { free(name->nameString); }
}

DEFINE_POOL_DESCRIPTOR(Name);

Name* 
Name_create_static(Pool* p, char* nameString){
  Name *name = Pool_malloc(p, &Name_alloc);
  name->nameString = nameString;
  name->isDynamic = 0;
  return name;
}

Name* 
Name_create_dynamic(Pool* p, char* nameString){
  Name *name = Pool_malloc(p, &Name_alloc);
  name->nameString = nameString;
  name->isDynamic = 1;
  return name;
}

// Template names

void 
finalize_TmplName (TmplName *tmplName) {
  if(tmplName->typeList != NULL) {
    free (tmplName->typeList);
  }
}

DEFINE_POOL_DESCRIPTOR(TmplName);

TmplName* 
TmplName_create_zero_types(Pool* p, Name* name){
  return TmplName_create(p, name, 0, NULL);
}

TmplName* 
TmplName_create(Pool* p, Name* name, int typeCount, Type** typeList){
  TmplName* tmplName = Pool_malloc(p, &TmplName_alloc);
  tmplName->name = name;
  tmplName->typeCount = typeCount;
  tmplName->typeList = typeList;
  return tmplName;
}

// Qualified Names

void 
finalize_QName(QName *qName) {
}

DEFINE_POOL_DESCRIPTOR(QName);

QName* 
QName_namespace_qName_create(Pool* p, Name* namespaceName, QName* qName){
  QName* qName_ret = Pool_malloc(p, &QName_alloc);
  qName_ret->kind = NAMESPACE_QNAME;
  qName_ret->namespace_qName.namespaceName = namespaceName;
  qName_ret->namespace_qName.qName = qName;
  return qName_ret;
}

QName* 
QName_tmplName_qName_create(Pool* p, TmplName* tmplName, QName* qName){
  QName* qName_ret = Pool_malloc(p, &QName_alloc);
  qName_ret->kind = TMPLNAME_QNAME;
  qName_ret->tmplName_qName.tmplName = tmplName;
  qName_ret->tmplName_qName.qName = qName;
  return qName_ret;
}

QName* 
QName_tmplName_create(Pool* p, TmplName* tmplName){
  QName* qName_ret = Pool_malloc(p, &QName_alloc);
  qName_ret->kind = TMPLNAME;
  qName_ret->tmplName = tmplName;
  return qName_ret;
}

// Types

void 
finalize_Type(Type* type) {
  if (type->function.parameterList != NULL) {
    free(type->function.parameterList);
  }
}

DEFINE_POOL_DESCRIPTOR(Type);

Type* 
Type_qName_create(Pool* p, QName* qName){
  Type* type = Pool_malloc(p, &Type_alloc);
  type->kind = QNAME;
  type->qName = qName;
  return type;
}

Type* 
Type_primType_create(Pool* p, PrimType primType){
  Type* type = Pool_malloc(p, &Type_alloc);
  type->kind = PRIMTYPE;
  type->primType = primType;
  return type;
}

Type* 
Type_function_create(Pool* p, Type* returnType, int parameterCount, Declaration** parameterList){
  Type* type = Pool_malloc(p, &Type_alloc);
  type->kind = FUNCTION;
  type->function.returnType = returnType;
  type->function.parameterCount = parameterCount;
  type->function.parameterList = parameterList;
  return type;
}

// Declarations

void 
finalize_Declaration(Declaration* declaration) {
}

DEFINE_POOL_DESCRIPTOR(Declaration);

Declaration* 
Declaration_local_create(Pool* p, Type* type, Name* name){
  Declaration* declaration = Pool_malloc(p, &Declaration_alloc);
  declaration->kind = LOCAL;
  declaration->type = type;
  declaration->name = name;
  return declaration;
}

Declaration* 
Declaration_extern_c_create(Pool* p, Type* type, Name* name){
  Declaration* declaration = Pool_malloc(p, &Declaration_alloc);
  declaration->kind = EXTERN_C;
  declaration->type = type;
  declaration->name = name;
  return declaration;
}

Declaration* 
Declaration_static_create(Pool* p, Type* type, Name* name){
  Declaration* declaration = Pool_malloc(p, &Declaration_alloc);
  declaration->kind = STATIC;
  declaration->type = type;
  declaration->name = name;
  return declaration;
}

void 
finalize_DeclarationListNode(DeclarationListNode* declarationListNode) {
}

DEFINE_POOL_DESCRIPTOR(DeclarationListNode);

DeclarationListNode* 
DeclarationListNode_create(Pool* p, Declaration* declaration, DeclarationListNode* next){
  DeclarationListNode* node = Pool_malloc(p, &DeclarationListNode_alloc);
  node->declaration = declaration;
  node->next = next;
  return node;
}

void 
finalize_DeclarationList(DeclarationList* declarationList) {
}

DEFINE_POOL_DESCRIPTOR(DeclarationList);

DeclarationList* 
DeclarationList_create(Pool* p){
  DeclarationList* list = Pool_malloc(p, &DeclarationList_alloc);
  list->head = list->tail = NULL;
  return list;
}

void 
DeclarationList_append(Pool* p, DeclarationList* list, Declaration* declaration){
  if (list->head == NULL) { // Originally empty
    list->head = list->tail = DeclarationListNode_create(p, declaration, NULL);
  } else {
    list->tail->next =  DeclarationListNode_create(p, declaration, NULL);
    list->tail = list->tail->next;
  }
}

// Expressions

void 
finalize_Expression(Expression* expression){
  if(expression->kind == CONSTRUCTOR) {
    if(expression->constructorInvocation.argumentList != NULL){
      free(expression->constructorInvocation.argumentList);
    }
  } else if(expression->kind == FUNCTION_CALL) {
    if(expression->functionCall.argumentList != NULL){
      free(expression->functionCall.argumentList);
    }
  }
}

DEFINE_POOL_DESCRIPTOR(Expression);

Expression* 
Expression_objectID_create(Pool* p, QName *objectID){
  Expression* expression = Pool_malloc(p, &Expression_alloc);
  expression->kind = OBJECTID;
  expression->objectID = objectID;
  return expression;
}

Expression* 
Expression_cast_create(Pool* p, Type* type, QName* qName){
  Expression* expression = Pool_malloc(p, &Expression_alloc);
  expression->kind = CAST;
  expression->cast.type = type;
  expression->cast.qName = qName;
  return expression;
}

Expression* 
Expression_constructor_create(Pool* p, QName* qName, int argumentCount, Expression** argumentList){
  Expression* expression = Pool_malloc(p, &Expression_alloc);
  expression->kind = CONSTRUCTOR;
  expression->constructorInvocation.qName = qName;
  expression->constructorInvocation.argumentCount = argumentCount;
  expression->constructorInvocation.argumentList = argumentList;
  return expression;
}

Expression* 
Expression_function_call_create(Pool* p, Expression* expression, int argumentCount, Expression** argumentList){
  Expression* expression_ret = Pool_malloc(p, &Expression_alloc);
  expression_ret->kind = FUNCTION_CALL;
  expression_ret->functionCall.expression = expression;
  expression_ret->functionCall.argumentCount = argumentCount;
  expression_ret->functionCall.argumentList = argumentList;
  return expression_ret;
}

Expression* 
Expression_member_access_create(Pool* p, Expression* expression, Name* name){
  Expression* expression_ret = Pool_malloc(p, &Expression_alloc);
  expression_ret->kind = MEMBER_ACCESS;
  expression_ret->memberAccess.expression = expression;
  expression_ret->memberAccess.name = name;
  return expression_ret;
}

// Statements

void 
finalize_Statement(Statement* statement){
}

DEFINE_POOL_DESCRIPTOR(Statement);

Statement* 
Statement_assignment_create(Pool* p, Expression* lhsExpression, Expression* rhsExpression){
  Statement* statement = Pool_malloc(p, &Statement_alloc);
  statement->kind = ASSIGNMENT;
  statement->assignment.lhsExpression = lhsExpression;
  statement->assignment.rhsExpression = rhsExpression;
  return statement;
}

Statement* 
Statement_expression_create(Pool* p, Expression* expression){
  Statement* statement = Pool_malloc(p, &Statement_alloc);
  statement->kind = EXPRESSION;
  statement->expression = expression;
  return statement;
}

Statement* 
Statement_return_create(Pool* p, Expression* returnStatement){
  Statement* statement = Pool_malloc(p, &Statement_alloc);
  statement->kind = RETURN;
  statement->returnStatement = returnStatement;
  return statement;
}

void 
finalize_StatementListNode(StatementListNode* statementListNode) {
}

DEFINE_POOL_DESCRIPTOR(StatementListNode);

StatementListNode* 
StatementListNode_create(Pool* p, Statement* statement, StatementListNode* next){
  StatementListNode* node = Pool_malloc(p, &Statement_alloc);
  node->statement = statement;
  node->next = next;
  return node;
}

void 
finalize_StatementList(StatementList* statementList) {
}

DEFINE_POOL_DESCRIPTOR(StatementList);

StatementList* 
StatementList_create(Pool* p){
  StatementList* list = Pool_malloc(p, &StatementList_alloc);
  list->head = list->tail = NULL;
  return list;
}

void 
StatementList_append(Pool* p, StatementList* list, Statement* statement){
  if (list->head == NULL) { // Originally empty
    list->head = list->tail = StatementListNode_create(p, statement, NULL);
  } else {
    list->tail->next =  StatementListNode_create(p, statement, NULL);
    list->tail = list->tail->next;
  }
}

// Functions

void 
finalize_Function(Function* function){
}

DEFINE_POOL_DESCRIPTOR(Function);

Function* 
Function_declaration_create(Pool* p, Declaration* signature){
  Function* function = Pool_malloc(p, &Function_alloc);
  function->kind = DECLARATION;
  function->signature = signature;
  return function;
}

Function* 
Function_definition_create(Pool* p, Declaration* signature, DeclarationList* declarationList, StatementList* statementList){
  Function* function = Pool_malloc(p, &Function_alloc);
  function->kind = DEFINITION;
  function->signature = signature;
  function->declarationList = declarationList;
  function->statementList = statementList;
  return function;
}

