
#ifndef CXX_WRAPPER_GENERATOR_TYPES_H
#define CXX_WRAPPER_GENERATOR_TYPES_H

#include "cutils/Pool.h"

/********************************************************************************/
/*                                 AST Grammar                                  */
/*                                                                              */
/* TopLevel  = List(Declaration) List(Function)                                 */
/*                                                                              */
/* Name    = char*                                                              */
/*                                                                              */
/* TmplName   = Name * (1 + List(Type))                                         */
/*                                                                              */
/* QName   = Name * QName                                                       */
/*    + TmplName * QName                                                        */
/*    + TmplName                                                                */
/*                                                                              */
/* PrimType   = { int32_t, float, bool, ... }                                   */
/*                                                                              */
/* Type   = QName                                                               */
/*    + PrimType                                                                */
/*    + Type * List(Declaration)                                                */
/*                                                                              */
/* Declaration   = Type * Name                                                  */
/*                                                                              */
/* Statement  = (1 + Expression) * Expression                                   */
/*    + Expression                                                              */
/*                                                                              */
/* Expression   = QName                                                         */
/*    + Type * QName                                                            */
/*    + Expression * List(Expression)                                           */
/*    + Expression * Name                                                       */
/*                                                                              */
/* Function   = Declaration * ( 1 + List(Declaration) * List(Statement) )       */
/*                                                                              */
/********************************************************************************/

// ===== Structure Declarations =====

typedef struct Name Name;
typedef struct TmplName TmplName;
typedef struct QName QName;
typedef enum PrimType PrimType;
typedef struct Type Type;
typedef struct Declaration Declaration;
typedef struct DeclarationListNode DeclarationListNode;
typedef struct DeclarationList DeclarationList;
typedef struct Expression Expression;
typedef struct Statement Statement;
typedef struct StatementListNode StatementListNode;
typedef struct StatementList StatementList;
typedef struct Function Function;

// ===== Function Declarations =====

void finalize_Name (Name *name);
void finalize_TmplName (TmplName *tmplName);
void finalize_QName(QName *qName);
void finalize_Type(Type* type);
void finalize_Declaration(Declaration* declaration);
void finalize_DeclarationListNode(DeclarationListNode* declarationListNode);
void finalize_DeclarationList(DeclarationList* declarationList);
void finalize_Expression(Expression* expression);
void finalize_Statement(Statement* statement);
void finalize_StatementListNode(StatementListNode* statementListNode);
void finalize_StatementList(StatementList* statementList);
void finalize_Function(Function* function);

Name* Name_create_static(Pool* p, char* nameString);
Name* Name_create_dynamic(Pool* p, char* nameString);

TmplName* TmplName_create_zero_types(Pool* p, Name* name);
TmplName* TmplName_create(Pool* p, Name* name, int typeCount, Type** typeList);

QName* QName_namespace_qName_create(Pool* p, Name* namespaceName, QName* qName);
QName* QName_tmplName_qName_create(Pool* p, TmplName* tmplName, QName* qName);
QName* QName_tmplName_create(Pool* p, TmplName* tmplName);

Type* Type_qName_create(Pool* p, QName* qName);
Type* Type_primType_create(Pool* p, PrimType primType);
Type* Type_function_create(Pool* p, Type* returnType, int parameterCount, Declaration** parameterList);

Declaration* Declaration_local_create(Pool* p, Type* type, Name* name);
Declaration* Declaration_extern_c_create(Pool* p, Type* type, Name* name);
Declaration* Declaration_static_create(Pool* p, Type* type, Name* name);
DeclarationListNode* DeclarationListNode_create(Pool* p, Declaration* declaration, DeclarationListNode* next);
DeclarationList* DeclarationList_create(Pool* p);
void DeclarationList_append(Pool* p, DeclarationList* list, Declaration* declaration);

Expression* Expression_objectID_create(Pool* p, QName *objectID);
Expression* Expression_cast_create(Pool* p, Type* type, QName* qName);
Expression* Expression_constructor_create(Pool* p, QName* qName, int argumentCount, Expression** argumentList);
Expression* Expression_function_call_create(Pool* p, Expression* expression, int argumentCount, Expression** argumentList);

Statement* Statement_assignment_create(Pool* p, Expression* lhsExpression, Expression* rhsExpression);
Statement* Statement_expression_create(Pool* p, Expression* expression);
Statement* Statement_return_create(Pool* p, Expression* returnStatement);
StatementListNode* StatementListNode_create(Pool* p, Statement* statement, StatementListNode* next);
StatementList* StatementList_create(Pool* p);
void StatementList_append(Pool* p, StatementList* list, Statement* statement);

Function* Function_declaration_create(Pool* p, Declaration* signature);
Function* Function_definition_create(Pool* p, Declaration* signature, DeclarationList* declarationList, StatementList* statementList);

// ===== Structure Definitions =====

// Name

struct Name {
  int isDynamic;
  char* nameString;
  PoolMembership pool;
};

// Template names

struct TmplName {
  Name* name;
  int typeCount;
  Type** typeList;
  PoolMembership pool;
};

// Qualified Names

typedef enum QNameKind { NAMESPACE_QNAME , TMPLNAME_QNAME , TMPLNAME } QNameKind;
struct QName {
  QNameKind kind;
  union {
    struct {
      Name* namespaceName; 
      QName* qName;
    } namespace_qName;
    struct {
      TmplName* tmplName; 
      QName* qName;
    } tmplName_qName;
    TmplName* tmplName;
  };
  PoolMembership pool;
};

// Primitive Types

enum PrimType {NONE_TYPE, INT32_T, FLOAT, BOOL_TYPE, VOID};

// Types

typedef enum TypeKind { QNAME , PRIMTYPE , FUNCTION } TypeKind;
struct Type {
  TypeKind kind;
  union {
    QName* qName;
    PrimType primType;
    struct {
      Type* returnType; 
      int parameterCount; 
      Declaration** parameterList;
    } function;
  };  
  PoolMembership pool;
};

// Declarations

typedef enum DeclarationKind { LOCAL , EXTERN_C , STATIC } DeclarationKind;
struct Declaration {
  DeclarationKind kind;
  Type* type;
  Name* name;
  PoolMembership pool;
};

struct DeclarationListNode {
  Declaration* declaration;
  DeclarationListNode* next;
  PoolMembership pool;
};

struct DeclarationList {
  DeclarationListNode* head;
  DeclarationListNode* tail;
  PoolMembership pool;
};

#define BEGIN_FOR_DECLARATION(nodeName,listName)            \
    DeclarationListNode* nodeName;              \
    for(nodeName = listName->head; nodeName != NULL; nodeName = nodeName->next)

// Expressions

typedef enum ExpressionKind { OBJECTID , CAST , CONSTRUCTOR , FUNCTION_CALL , MEMBER_ACCESS } ExpressionKind;
struct Expression {
  ExpressionKind kind;
  union {
    QName* objectID;
    struct {
      Type* type; 
      QName* qName;
    } cast;
    struct {
      QName* qName; 
      int argumentCount; 
      Expression** argumentList; 
    } constructorInvocation;
    struct {
      Expression* expression; 
      int argumentCount; 
      Expression** argumentList; 
    } functionCall;
    struct {
      Expression* expression; 
      Name* name;
    } memberAccess;
  };
  PoolMembership pool;
};

// Statements

typedef enum StatementKind { ASSIGNMENT , EXPRESSION , RETURN } StatementKind;
struct Statement {
  StatementKind kind;
  union {
    struct {
      Expression* lhsExpression; 
      Expression* rhsExpression;
    }  assignment;
    Expression* expression;
    Expression* returnStatement;
  };
  PoolMembership pool;
};

struct StatementListNode {
  Statement* statement;
  StatementListNode* next;
  PoolMembership pool;
};

struct StatementList {
  StatementListNode* head;
  StatementListNode* tail;
  PoolMembership pool;
};

#define BEGIN_FOR_STATEMENT(nodeName,listName)        \
    StatementListNode* nodeName;              \
    for(nodeName = listName->head; nodeName != NULL; nodeName = nodeName->next)

// Functions

typedef enum FunctionKind { DECLARATION , DEFINITION } FunctionKind;
struct Function {
  FunctionKind kind;
  Declaration* signature;
  DeclarationList* declarationList;
  StatementList* statementList;
  PoolMembership pool;
};

#endif

