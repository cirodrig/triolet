
module Pyon.SystemF.Flatten.FlatData where

import Prelude hiding(reads)

import qualified Data.IntSet as IntSet
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Identifier
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
import qualified Pyon.SystemF.Builtins as SF
import qualified Pyon.Anf.Syntax as Anf
import qualified Pyon.Anf.Builtins as Anf

withMany :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c
withMany f xs k = go xs k
  where
    go (x:xs) k = f x $ \y -> go xs $ \ys -> k (y:ys)
    go []     k = k []

-- | The unit type
unitType :: RType
unitType = Gluon.mkTupTyE noSourcePos Gluon.Unit

-- | The type of an address
addressType :: RType
addressType = Gluon.mkInternalConE $ Gluon.builtin Gluon.the_Addr

-- | The type of a pointer-to-address
pointerType :: RType -> RType 
pointerType referent =
  Gluon.mkInternalConAppE (Anf.anfBuiltin Anf.the_Ptr) [referent]

-- | The type of an object at an address
stateType :: RType -> RType -> RType
stateType obj_type addr_type =
  let at = Gluon.builtin Gluon.the_AtS
  in Gluon.mkInternalConAppE at [obj_type, addr_type]

-- | The type of an undefined object at an address
undefStateType :: RType -> RType -> RType
undefStateType obj_type addr_type =
  let at = Gluon.builtin Gluon.the_AtS
      undef = Anf.anfBuiltin Anf.the_Undef
  in Gluon.mkInternalConAppE at [ Gluon.mkInternalConAppE undef [obj_type]
                                , addr_type]

effectType :: RType -> RType -> RType
effectType obj_type addr_type =
  let at = Gluon.builtin Gluon.the_AtE
  in Gluon.mkInternalConAppE at [obj_type, addr_type]

-- | A parameter-passing mode.  Modes control how a System F value is
-- elaborated into an ANF value.
data TypeMode = PassByVal | PassByClo | PassByRef
              deriving(Eq)

-- | A parameter-passing mode for a binder.  Modes are used to compute
-- side effects and translate parameters to the form used by ANF.
-- We distinguish pass-by-value, pass-by-reference, and return-by-reference
-- binders.  We also distinguish parameters that are the result of HM type 
-- inference.
--
-- Dictionary parameters are only labeled as such when they are passed
-- to ordinary functions.  Functions that construct dictionaries, for example,
-- don't take dictionary parameters.
data DataMode = InHM            -- ^ A type or dictionary parameter
              | IOVal           -- ^ A pass-by-value parameter or return
              | IOClo           -- ^ A closure parameter or return
              | InRef           -- ^ A pass-by-reference parameter
              | OutRef          -- ^ A pass-by-reference return
              deriving(Eq)

-- | Return True if the given System F type is passed as Hindley-Milner type
-- or dictionary value.  Dictionary types can always be identified by looking 
-- at their head.
typeOfHMType :: RType -> Bool
typeOfHMType ty
  | getLevel ty == KindLevel = True
  | getLevel ty /= TypeLevel = internalError "typeOfHMType"
  | otherwise =
      case ty
      of Gluon.AppE {Gluon.expOper = Gluon.ConE {Gluon.expCon = c}} ->
           isDictionaryTypeConstructor c
         Gluon.ConE {Gluon.expCon = c} ->
           isDictionaryTypeConstructor c
         _ -> False

-- | True if this is a type constructor for a constraint type.
-- Data of these types are always passed by value. 
isDictionaryTypeConstructor con =
  any (con `SF.isPyonBuiltin`) [SF.the_PassConv, SF.the_EqDict, SF.the_OrdDict,
                                SF.the_TraversableDict, SF.the_AdditiveDict,
                                SF.the_VectorDict]

{-
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
parameterOutMode PassByRef = Just OutRef -}

-- | We keep track of the set of variables that an expression or function 
-- reads and writes.  This is the statement's side effect.
--
-- A variable is in at most one of the read and write sets.
data Effect =
  Effect
  { -- | Read variable IDs
    readEffect :: IntSet.IntSet
    -- | Written variable IDs
  , writeEffect :: IntSet.IntSet
  }

isNoEffect, isSomeEffect :: Effect -> Bool
isNoEffect (Effect r w) = IntSet.null r && IntSet.null w
isSomeEffect e = not $ isNoEffect e

-- | The empty effect 
noEffect :: Effect
noEffect = Effect IntSet.empty IntSet.empty

-- | A side effect that reads a single variable
readVar :: Var -> Effect
readVar v = Effect (IntSet.singleton (fromIdent $ varID v)) IntSet.empty

-- | A side effect that reads a single variable
writeVar :: Var -> Effect
writeVar v = Effect IntSet.empty (IntSet.singleton (fromIdent $ varID v))

-- | Remove a variable from an effect (if it is present)
maskEffect :: Var -> Effect -> Effect
maskEffect v (Effect r w) = Effect (mask r) (mask w)
  where
    mask s = IntSet.delete (fromIdent $ varID v) s

-- | Determine whether a variable is read
reads, writes, affects :: Effect -> Var -> Bool
Effect r _ `reads` v = fromIdent (varID v) `IntSet.member` r
Effect _ w `writes` v = fromIdent (varID v) `IntSet.member` w
e `affects` v = e `reads` v || e `writes` v

-- | Take the union of two effects
effectUnion :: Effect -> Effect -> Effect
effectUnion (Effect r1 w1) (Effect r2 w2) =
  let w = IntSet.union w1 w2
  in Effect (IntSet.union r1 r2 IntSet.\\ w) (IntSet.union w1 w2)

-- | Take the union of a list of effects
effectUnions :: [Effect] -> Effect
effectUnions xs = foldr effectUnion noEffect xs

-- | Take the difference of two effects.
--
-- The difference is undefined when the read and write effects overlap.
effectDiff :: Effect -> Effect -> Effect
Effect r1 w1 `effectDiff` Effect r2 w2
  | not $ IntSet.null (IntSet.intersection w1 r2) &&
    IntSet.null (IntSet.intersection w2 r1) =
      internalError "effectDiff"
  | otherwise = Effect (r1 IntSet.\\ r2) (w1 IntSet.\\ w2)

-- | Rename the variables in a side effect
renameEffect :: (VarID -> VarID) -> Effect -> Effect
renameEffect f (Effect r w) =
  let f' x = fromIdent (f (toIdent x))
  in Effect (IntSet.map f' r) (IntSet.map f' w)

-- | Get a list of variable IDs affected by a side effect
effectReadVars, effectWriteVars, effectVars :: Effect -> [VarID]
effectReadVars (Effect r _) = map toIdent $ IntSet.elems r
effectWriteVars (Effect _ w) = map toIdent $ IntSet.elems w
effectVars (Effect r w) = map toIdent $ IntSet.elems $ IntSet.union r w

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

{-
argumentMode :: FlatArgument -> DataMode
argumentMode (ValueArgument {}) = undefined
argumentMode (ClosureArgument {}) = IOClo
argumentMode (VariableArgument {}) = InRef -}

-- | Side effect information for a function call.  The effect is computed
-- from the function's arguments.  The function's return is not included
-- in the side effect.
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
returnMode (ValueReturn ty) 
  | typeOfHMType ty = InHM
  | otherwise       = IOVal
returnMode (ClosureReturn {}) = IOClo
returnMode (VariableReturn {}) = OutRef

returnType :: FlatReturn -> RType
returnType (ValueReturn ty) = ty
returnType (ClosureReturn ty _) = ty
returnType (VariableReturn ty _) = ty

returnEffect :: FlatReturn -> Effect
returnEffect (ValueReturn _) = noEffect
returnEffect (ClosureReturn _ _) = noEffect
returnEffect (VariableReturn _ v) = writeVar v

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
  mkFlatInfo pos (VariableReturn ty v) (writeVar v)

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

-- | Get a string describing the statement constructor
stmtString :: Stmt -> String
stmtString (ValueS {}) = "ValueS"
stmtString (CopyValueS {}) = "CopyValueS"
stmtString (CallS {}) = "CallS"
stmtString (LetS {}) = "LetS"
stmtString (EvalS {}) = "EvalS"
stmtString (LetrecS {}) = "LetrecS"
stmtString (CaseValS {}) = "CaseValS"
stmtString (CaseRefS {}) = "CaseRefS"
stmtString (ReadingS {}) = "ReadingS"
stmtString (LocalS {}) = "LocalS"
stmtString (CopyS {}) = "CopyS"

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
             of InHM  -> "typeish"
                IOVal -> "val"
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
                     cat (punctuate (text ",") (map (text . show) (effectReadVars eff) ++ map ((text "!" <>) . text . show) (effectWriteVars eff))) <>
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

