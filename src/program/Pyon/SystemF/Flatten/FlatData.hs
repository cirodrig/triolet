
module Pyon.SystemF.Flatten.FlatData where

import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Label
import Gluon.Common.Error
import Gluon.Common.SourcePos
import Gluon.Core(Level(..), HasLevel(..),
                  Whnf, fromWhnf,
                  Con(..),
                  Var, varID, varName,
                  VarID,
                  Binder(..), Binder'(..), RBinder, RBinder')
import Gluon.Core.Rename
import qualified Gluon.Core.Builtins.Effect
import qualified Gluon.Core as Gluon

import Pyon.SystemF.Syntax
import Pyon.SystemF.Print
import qualified Pyon.Anf.Syntax as Anf
import qualified Pyon.Anf.Builtins as Anf

-- | The unit type
unitType :: RType
unitType = Gluon.TupTyE (Gluon.mkSynInfo noSourcePos TypeLevel) Gluon.Unit

-- | The type of an address
addressType :: RType
addressType = Gluon.mkInternalConE $ Gluon.builtin Gluon.the_Addr

-- | The type of a pointer-to-address
pointerType :: RType -> RType 
pointerType referent =
  Gluon.mkInternalConAppE (Anf.anfBuiltin Anf.the_Ptr) [referent]

-- | A parameter-passing mode.  Modes control how a System F value is
-- elaborated into an ANF value.
data TypeMode = PassByVal | PassByClo | PassByRef
              deriving(Eq)

-- | A parameter-passing mode for a binder.  This mode distinguishes
-- pass-by-reference and return-by-reference binders.
data DataMode = IOVal | IOClo | InRef | OutRef
              deriving(Eq)

-- | How to pass a parameter for a given mode
parameterInMode :: TypeMode -> DataMode
parameterInMode PassByVal = IOVal
parameterInMode PassByClo = IOClo
parameterInMode PassByRef = InRef

-- | How to pass a parameter for a return value of a given mode.
-- A 'Nothing' value means that no parameter is necessary.
-- For by-reference values, the data is written into storage that is passed in
-- by parameter.
parameterOutMode :: TypeMode -> Maybe DataMode
parameterOutMode PassByVal = Nothing
parameterOutMode PassByClo = Nothing
parameterOutMode PassByRef = Just OutRef

-- | We keep track of the set of variables that an expression or function 
-- reads.  This set is used to compute the side effect.
newtype Effect = Effect {effectMap :: Map.Map VarID AtomicEffect}
type AtomicEffect = ()

isNoEffect, isSomeEffect :: Effect -> Bool
isNoEffect (Effect m) = Map.null m
isSomeEffect (Effect m) = not (Map.null m)

-- | The empty effect 
noEffect :: Effect
noEffect = Effect Map.empty

-- | A side effect on a single variable
varEffect :: Var -> Effect
varEffect v = Effect $ Map.singleton (varID v) ()

-- | Remove a variable from an effect (if it is present)
maskEffect :: Var -> Effect -> Effect
maskEffect v (Effect m) = Effect $ Map.delete (varID v) m

-- | Determine whether a variable is part of a side effect
affects :: Effect -> Var -> Bool
Effect m `affects` v = varID v `Map.member` m

-- | Take the union of two effects
effectUnion :: Effect -> Effect -> Effect
effectUnion (Effect m1) (Effect m2) = Effect (Map.union m1 m2)

-- | Take the union of a list of effects
effectUnions :: [Effect] -> Effect
effectUnions xs = Effect $ Map.unions $ map effectMap xs

-- | Take the difference of two effects
effectDiff :: Effect -> Effect -> Effect
Effect m1 `effectDiff` Effect m2 = Effect (m1 Map.\\ m2)

-- | Rename the variables in a side effect
renameEffect :: (VarID -> VarID) -> Effect -> Effect
renameEffect f (Effect m) = Effect $ Map.mapKeys f m

-- | Get a list of variable IDs affected by a side effect
effectVars :: Effect -> [VarID]
effectVars (Effect m) = Map.keys m

-- | An argument to be passed to a flattened operator.
data FlatArgument =
    -- | Pass a value, by value
    ValueArgument !Value
    -- | Pass a closure.  The side effect of calling the closure is also 
    -- passed.
  | ClosureArgument !Value FunctionEffect
    -- | Pass data by reference.  The argument is the variable that holds
    -- the parameter data.
  | VariableArgument !Var

argumentMode :: FlatArgument -> DataMode
argumentMode (ValueArgument {}) = IOVal
argumentMode (ClosureArgument {}) = IOClo
argumentMode (VariableArgument {}) = InRef

-- | Side effect information for a function call.  The effect is computed
-- from the function's arguments.
type FunctionEffect = [FlatArgument] -> Effect

-- | Data are either returned as values or by writing to a variable.
-- We keep track of an expression's return to compute its input and output
-- state.
data FlatReturn =
    -- | Return by value
    ValueReturn !RType
    -- | Return a closure
  | ClosureReturn !RType FunctionEffect
    -- | Return by writing into a variable
  | VariableReturn !RType !Var

returnMode :: FlatReturn -> DataMode
returnMode (ValueReturn {}) = IOVal
returnMode (ClosureReturn {}) = IOClo
returnMode (VariableReturn {}) = OutRef

returnType :: FlatReturn -> RType
returnType (ValueReturn ty) = ty
returnType (ClosureReturn ty _) = ty
returnType (VariableReturn ty _) = ty

isValueReturn (ValueReturn _) = True
isValueReturn _ = False

data Value =
    VarV Var !DataMode
  | ConV Con !DataMode
    -- | Literals are passed as values.
  | LitV Lit
    -- | Types are passed as values.
  | TypeV RType
    -- | Functions are always pass-by-closure values.
  | FunV FlatFun
    -- | Applications are always values.
  | AppV Value [Value]

data FlatInfo =
  FlatInfo
  { fexpInfoInfo :: ExpInfo
  , fexpInfoReturn :: FlatReturn
  , fexpInfoEffect :: Effect
  }

mkFlatInfo :: SourcePos -> FlatReturn -> Effect -> FlatInfo
mkFlatInfo pos ret eff =
  FlatInfo (Gluon.mkSynInfo pos Gluon.ObjectLevel) ret eff

mkValueReturnInfo :: SourcePos -> RType -> FlatInfo
mkValueReturnInfo pos ty = mkFlatInfo pos (ValueReturn ty) noEffect

mkClosureReturnInfo :: SourcePos -> RType -> FunctionEffect -> FlatInfo
mkClosureReturnInfo pos ty eff = mkFlatInfo pos (ClosureReturn ty eff) noEffect

mkVariableReturnInfo :: SourcePos -> Var -> RType -> FlatInfo
mkVariableReturnInfo pos v ty =
  mkFlatInfo pos (VariableReturn ty v) noEffect

fexpEffect :: Stmt -> Effect
fexpEffect e = fexpInfoEffect (fexpInfo e)

fexpReturn :: Stmt -> FlatReturn
fexpReturn e = fexpInfoReturn (fexpInfo e)

fexpSourcePos :: Stmt -> SourcePos
fexpSourcePos e = getSourcePos (fexpInfoInfo $ fexpInfo e)

-- | Alter the given information by setting the source position and
-- altering the side effect.
extendFlatInfo :: SourcePos -> (Effect -> Effect) -> FlatInfo -> FlatInfo
extendFlatInfo pos modify_effect (FlatInfo inf ret eff) =
  FlatInfo (setSourcePos inf pos) ret (modify_effect eff)

extendStmtInfo :: SourcePos -> (Effect -> Effect) -> Stmt -> FlatInfo
extendStmtInfo pos modify_effect stmt =
  extendFlatInfo pos modify_effect (fexpInfo stmt)

data Stmt =
    ValueS
    { fexpInfo :: {-# UNPACK #-} !FlatInfo
    , fexpValue :: Value
    }
    -- | Store a value into a variable.
  | CopyValueS
    { fexpInfo :: {-# UNPACK #-} !FlatInfo
    , fexpValue :: Value
    }
    -- | Call a function.  The function either returns a value or
    -- writes into a variable as a side effect.
  | CallS
    { fexpInfo :: {-# UNPACK #-} !FlatInfo
    , fexpOper :: Value
    , fexpArgs :: [Value]
    }
    -- | Perform an action that returns a result value, bind the result
    -- to a local variable, and perform another action.
  | LetS
    { fexpInfo :: {-# UNPACK #-} !FlatInfo
    , fexpBinder :: RBinder DataMode
    , fexpRhs :: Stmt
    , fexpBody :: Stmt
    }
    -- | Perform an action for its side effect, then perform another action.
  | EvalS
    { fexpInfo :: {-# UNPACK #-} !FlatInfo
    , fexpRhs :: Stmt
    , fexpBody :: Stmt
    }
  | LetrecS
    { fexpInfo :: {-# UNPACK #-} !FlatInfo
    , fexpDefs :: [FlatDef]
    , fexpBody :: Stmt
    }
    -- | Case-of-value
  | CaseValS
    { fexpInfo :: {-# UNPACK #-} !FlatInfo
    , fexpScrutinee :: Value
    , fexpValAlts :: [FlatValAlt]
    }
    -- | Case-of-reference
  | CaseRefS
    { fexpInfo :: {-# UNPACK #-} !FlatInfo
    , fexpScrutineeVar :: Var
    , fexpScrutineeType :: RType
    , fexpRefAlts :: [FlatRefAlt]
    }
    -- | Put a writable object into readable mode.  This is inserted during
    -- flattening.
  | ReadingS
    { fexpInfo :: {-# UNPACK #-} !FlatInfo
    , fexpScrutineeVar :: Var
    , fexpScrutineeType :: RType
    , fexpBody :: Stmt
    }
    -- | Allocate some memory that is alive only during the body of this
    -- expression.  This is inserted during flattening.
  | LocalS
    { fexpInfo :: {-# UNPACK #-} !FlatInfo
    , fexpVar :: Var
    , fexpType :: RType
    , fexpBody :: Stmt
    }
    -- | Copy a variable (to a destination variable).  This is inserted during
    -- flattening.
  | CopyS
    { fexpInfo :: {-# UNPACK #-} !FlatInfo
    , fexpSrc :: Var
    }

data FlatValAlt =
  FlatValAlt Con [Value] [RBinder DataMode] Stmt

valAltBody (FlatValAlt _ _ _ body) = body

-- | A pass-by-reference alternative.
-- The case alternative matches a constructor instantiated at type arguments,
-- binds parameters, and then executes a body.  The body's effect and return
-- type are recorded.
data FlatRefAlt =
  FlatRefAlt Con [Value] [RBinder DataMode] Effect FlatReturn RType Stmt

refAltBody (FlatRefAlt _ _ _ _ _ _ body) = body

refAltReturnType (FlatRefAlt _ _ _ _ _ rt _) = rt

data FlatFun =
  FlatFun
  { ffunInfo :: ExpInfo
  , ffunParams :: [RBinder DataMode]
  , ffunReturn :: FlatReturn
  , ffunReturnType :: RType
  , ffunEffect :: Effect
  , ffunBody :: Stmt
  }

data FlatDef = FlatDef Var FlatFun

-------------------------------------------------------------------------------
-- Pretty-printing of temporary flattening data structures

pprComponent :: DataMode -> Doc
pprComponent component =
  let name = case component
             of IOVal -> "val"
                IOClo -> "fun"
                InRef -> "read"
                OutRef -> "write"
  in text name

pprDotted :: Doc -> DataMode -> Doc
doc `pprDotted` c = doc <> text "." <> pprComponent c

pprBlock :: [Doc] -> Doc
pprBlock []     = text "{}"
pprBlock [d]    = d
pprBlock (d:ds) = vcat ((text "{" <+> d) : map (semi <+>) ds) $$ text "}"

pprValue :: Value -> Doc
pprValue value = 
  case value
  of VarV v component ->
       pprVar v `pprDotted` component
     ConV c component ->
       text (showLabel $ Gluon.conName c) `pprDotted` component
     LitV l -> pprLit l
     TypeV ty -> Gluon.pprExp ty
     FunV f -> parens $ pprFlatFun f
     AppV v vs -> parens $ sep (pprValue v : map pprValue vs)

pprStmt :: Stmt -> Doc
pprStmt statement =
  case fexpInfo statement
  of FlatInfo _ ret eff ->
       let eff_doc = text "<" <>
                     cat (punctuate (text ",") (map (text . show) $ effectVars eff)) <>
                     text ">"
           stmt_doc = pprStmt' statement
           lhs_doc rhs = case ret
                         of ValueReturn _ -> rhs
                            ClosureReturn _ _ -> rhs
                            VariableReturn t v -> hang (pprVar v <+> text ":=") 4 rhs
       in eff_doc $$ lhs_doc stmt_doc

pprStmt' statement =
  case statement
  of ValueS {fexpValue = val} ->
       pprValue val
     CopyValueS {fexpValue = val} ->
       pprValue val
     CallS {fexpOper = op, fexpArgs = args} ->
       pprValue op <+> sep (map pprValue args)
     LetS {} -> pprStmts statement
     EvalS {} -> pprStmts statement
     LetrecS {} -> pprStmts statement
     ReadingS {} -> pprStmts statement
     LocalS {} -> pprStmts statement
     CaseValS {fexpScrutinee = v, fexpValAlts = alts} ->
       text "case" <+> pprValue v $$
       text "of" <+> pprBlock (map pprAlt alts)
     CaseRefS {fexpScrutineeVar = v, fexpRefAlts = alts} ->
       text "case" <+> pprVar v $$
       text "of" <+> pprBlock (map pprRefAlt alts)
     CopyS {fexpSrc = src} ->
       text "copy" <+> pprVar src

pprAlt :: FlatValAlt -> Doc
pprAlt (FlatValAlt c ty_args params body) =
  let con_doc = text (showLabel $ Gluon.conName c)
      ty_docs = map pprValue ty_args
      param_docs = map pprParam params
      body_doc = pprStmt body
  in hang (con_doc <+> sep (ty_docs ++ param_docs) <> text ".") 4 body_doc

pprRefAlt :: FlatRefAlt -> Doc
pprRefAlt (FlatRefAlt c ty_args params eff _ _  body) =
  let con_doc = text (showLabel $ Gluon.conName c)
      ty_docs = map pprValue ty_args
      param_docs = map pprParam params
      body_doc = pprStmt body
  in hang (con_doc <+> sep (ty_docs ++ param_docs) <> text ".") 4 body_doc

-- | Print a sequence of statements as a block
pprStmts :: Stmt -> Doc
pprStmts s = pprBlock $ statement_sequence s
  where
    statement_sequence statement =
      case statement
      of LetS { fexpBinder = Binder v ty comp
              , fexpRhs = rhs
              , fexpBody = body} ->
           let lhs_doc = pprVar v `pprDotted` comp <+>
                         colon <+> Gluon.pprExp ty <+> text "="
               rhs_doc = pprStmt rhs
               body_doc = statement_sequence body
           in hang lhs_doc 4 rhs_doc : body_doc
         EvalS { fexpRhs = rhs
               , fexpBody = body} ->
           pprStmt rhs : statement_sequence body
         LetrecS { fexpDefs = defs
                 , fexpBody = body} ->
           let defs_doc = map pprFlatDef defs
               body_doc = statement_sequence body
           in (text "letrec" $$ nest 2 (pprBlock defs_doc)) : body_doc
         ReadingS {fexpScrutineeVar = v, fexpBody = body} ->
           (text "reading" <+> pprVar v) : statement_sequence body
         LocalS {fexpVar = v, fexpBody = body} ->
           (text "local" <+> pprVar v) : statement_sequence body
         _ -> [pprStmt statement]

pprFlatDef :: FlatDef -> Doc
pprFlatDef (FlatDef v f) = hang (pprVar v <+> text "=") 4 (pprFlatFun f)

pprFlatFun :: FlatFun -> Doc
pprFlatFun function =
  let params = map pprParam $ ffunParams function
      rv = case ffunReturn function
           of ValueReturn ty ->
                parens $ Gluon.pprExp ty
              ClosureReturn ty _ ->
                parens $ Gluon.pprExp ty
              VariableReturn _ v ->
                parens $ pprVar v `pprDotted` OutRef <+> text ":" <+> Gluon.pprExp (ffunReturnType function)
      header = text "lambda" <+> cat (params ++ [nest (-3) $ text "->" <+> rv])
  in header <> text "." $$ nest 2 (pprStmt (ffunBody function))
    
pprParam (Binder v ty component) =
  parens $ pprVar v `pprDotted` component <+> text ":" <+> Gluon.pprExp ty

