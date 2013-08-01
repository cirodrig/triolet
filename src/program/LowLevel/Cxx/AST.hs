{-| Simplified C++ abstract syntax trees. 

These ASTs are built when generating C++ header files containing wrappers 
around Triolet code.
-}

module LowLevel.Cxx.AST where

type Name = String

-- | A name or a template instantiation.  Primitive C types like \"int\"
--   are also names.
--
-- > NAME
-- > NAME<t1, t2>
data TmplName = PlainName Name | TmplName Name [Type]

-- | A qualified name
--
-- > TMPLNAME
-- > TMPLNAME::QNAME
data QName = Qualified TmplName QName | Unqualified TmplName

-- | C variables are QNames 
type Var = QName

plainQName :: Name -> QName
plainQName nm = Unqualified (PlainName nm)

tmplQName :: Name -> [Type] -> QName
tmplQName nm tys = Unqualified (TmplName nm tys)

-- | A C++ type
data Type = NameType QName
          | FunType [Type] Type

-- | Primitive and standard C types
int32_tT, int64_tT, floatT, boolT, voidT :: Type
int32_tT = NameType $ plainQName "int32_t"
int64_tT = NameType $ plainQName "int64_t"
floatT = NameType $ plainQName "float"
boolT = NameType $ plainQName "bool"
voidT = NameType $ plainQName "void"

-- | A qualifier
data Qualifier =
  ExternCQual

-- | A declaration consists of a name and a type
data Decl = Decl [Qualifier] Name Type

data Expression =
    IdentExpr QName                  -- ^ An identifier
  | CallExpr Expression [Expression] -- ^ A function call
  | DotExpr Expression Name          -- ^ Member access
  | CastExpr Type Expression         -- ^ Type cast

callVarExpr :: Var -> [Expression] -> Expression
callVarExpr fun args = CallExpr (IdentExpr fun) args

callMemberExpr :: Expression -> Name -> [Expression] -> Expression
callMemberExpr op field args = CallExpr (DotExpr op field) args

data Statement =
    -- | Declare and optionally initialize a variable
    DeclStmt Decl (Maybe Expression)
    -- | Execute an expression
  | ExprStmt Expression
    -- | Return a value
  | ReturnStmt Expression

type Suite = [Statement]

-- | A function definition
data FunDef =
  FunDef 
  { funQualifiers :: [Qualifier]
  , funReturnType :: Type 
  , funName :: Name 
  , funParameters :: [Decl] 
  , funBody :: Suite
  }

data HeaderFile = HeaderFile [Decl] [FunDef]

