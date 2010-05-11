
{-# LANGUAGE ViewPatterns, FlexibleContexts, FlexibleInstances,
             RelaxedPolyRec, GeneralizedNewtypeDeriving, Rank2Types #-}
module Pyon.SystemF.Flatten(flatten)
where

import Control.Monad
import Control.Monad.RWS
import Control.Monad.Trans
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace 
import Text.PrettyPrint.HughesPJ hiding(Mode)

import Gluon.Common.Label
import Gluon.Common.Identifier
import Gluon.Common.MonadLogic
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Gluon.Common.Error
import Gluon.Core(Level(..), HasLevel(..),
                  Whnf, fromWhnf,
                  Con(..),
                  Var, varID, varName,
                  VarID,
                  Binder(..), Binder'(..), RBinder, RBinder')
import Gluon.Core.Rename
import qualified Gluon.Core.Builtins.Effect
import qualified Gluon.Core as Gluon
import Gluon.Eval.Environment
import Gluon.Eval.Eval
import Gluon.Eval.Equality
import Gluon.Eval.Typecheck
import Pyon.Globals
import Pyon.SystemF.Builtins
import Pyon.SystemF.Syntax
import Pyon.SystemF.Typecheck
import Pyon.SystemF.Print
import qualified Pyon.Anf.Syntax as Anf
import qualified Pyon.Anf.Builtins as Anf

duplicateVar :: (Monad m, Supplies m VarID) => Var -> m Var
duplicateVar v = do
  id <- fresh
  return $ Gluon.mkVar id (varName v) (getLevel v)

withMany :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c
withMany f xs k = go xs k
  where
    go (x:xs) k = f x $ \y -> go xs $ \ys -> k (y:ys)
    go []     k = k []

type TExp = SFRecExp (Typed Rec)
type TType = RecType (Typed Rec)

-- | The type of an address
addressType :: RType
addressType = Gluon.mkInternalConE $ Gluon.builtin Gluon.the_Addr

-- | The type of a pointer-to-address
pointerType :: RType -> RType 
pointerType referent =
  Gluon.mkInternalConAppE (Anf.anfBuiltin Anf.the_Ptr) [referent]

data Mode = ByVal | ByRef | ByClo
data Component = Value | FunRef | Address | Pointer | State

-- | We keep track of the set of variables that an expression or function 
-- reads.  This set is used to compute the side effect.
type Effect = Map.Map VarID AtomicEffect
type AtomicEffect = ()

noEffect = Map.empty
varEffect v = Map.singleton (varID v) ()

data FlatArgument =
    ValueArgument !Value 
  | ClosureArgument !Value FunctionEffect
  | VariableArgument !Var

-- | Data are either returned as values or by writing to a variable.
-- We keep track of an expression's return to compute its input and output
-- state.
data FlatReturn =
    ValueReturn !RType
  | ClosureReturn !RType FunctionEffect
  | VariableReturn !RType !Var

returnComponent :: FlatReturn -> Component
returnComponent (ValueReturn _) = Value
returnComponent (ClosureReturn _ _) = FunRef
returnComponent (VariableReturn _ _) = internalError "returnComponent"

returnType :: FlatReturn -> RType
returnType (ValueReturn ty) = ty
returnType (ClosureReturn ty _) = ty
returnType (VariableReturn ty _) = ty

isValueReturn (ValueReturn _) = True
isValueReturn _ = False

data Value =
    VarV Var !Component
  | ConV Con !Component
  | LitV Lit
  | TypeV RType
  | FunV FlatFun
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
    , fexpBinder :: RBinder Component
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
  FlatValAlt Con [Value] [RBinder Component] Stmt

valAltBody (FlatValAlt _ _ _ body) = body

-- | A pass-by-reference alternative.
-- The case alternative matches a constructor instantiated at type arguments,
-- binds parameters, and then executes a body.  The body's effect and return
-- type are recorded.
data FlatRefAlt =
  FlatRefAlt Con [Value] [RBinder Component] Effect FlatReturn RType Stmt

refAltBody (FlatRefAlt _ _ _ _ _ _ body) = body

refAltReturnType (FlatRefAlt _ _ _ _ _ rt _) = rt

data FlatFun =
  FlatFun
  { ffunInfo :: ExpInfo
  , ffunParams :: [RBinder Component]
  , ffunReturn :: FlatReturn
  , ffunReturnType :: RType
  , ffunEffect :: Effect
  , ffunBody :: Stmt
  }

data FlatDef = FlatDef Var FlatFun

isDictionaryTypeConstructor con =
  any (con `isPyonBuiltin`) [the_PassConv, the_EqDict, the_OrdDict,
                             the_TraversableDict, the_AdditiveDict,
                             the_VectorDict]

discardExpType :: TExp -> SFExpOf Rec (Typed Rec)
discardExpType (TypedSFExp (TypeAnn _ e)) = e

fromTypedExp :: TExp -> RExp
fromTypedExp e = mapSFExp fromTypedExp fromTypedFun fromTypedType $
                 discardExpType e

fromTypedPat :: Pat (Typed Rec) -> RPat
fromTypedPat (VarP v ty) = VarP v (fromTypedType ty)
fromTypedPat _ = internalError "fromTypedPat: Expecting a variable parameter"

fromTypedFun :: Fun (Typed Rec) -> RFun
fromTypedFun (TypedSFFun (TypeAnn _ (Fun info ty_params params return_type body))) =
  Fun info (map from_ty_param ty_params) (map from_param params) (fromTypedType return_type) (fromTypedExp body)
  where
    from_ty_param (TyPat v ty) = TyPat v (fromTypedType ty)
    from_param (VarP v ty) = VarP v (fromTypedType ty)
    from_param _ = internalError "fromTypedFun: Expecting a variable parameter"

fromTypedType :: TType -> RType
fromTypedType (TypedSFType t) = t

expectClosureArgument :: FlatArgument -> (Value, FunctionEffect)
expectClosureArgument (ClosureArgument v e) = (v, e)
expectClosureArgument _ = internalError "Expecting closure argument"

-------------------------------------------------------------------------------
-- Pretty-printing routines

pprComponent :: Component -> Doc
pprComponent component =
  let name = case component
             of Value -> "val"
                FunRef -> "fun"
                Address -> "addr"
                Pointer -> "ptr"
                State -> "st"
  in text name

pprDotted :: Doc -> Component -> Doc
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
                     cat (punctuate (text ",") (map (text . show) $ Map.keys eff)) <>
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
                parens $ pprVar v `pprDotted` State <+> text ":" <+> Gluon.pprExp (ffunReturnType function)
      header = text "lambda" <+> cat (params ++ [nest (-3) $ text "->" <+> rv])
  in header <> text "." $$ nest 2 (pprStmt (ffunBody function))
    
pprParam (Binder v ty component) =
  parens $ pprVar v `pprDotted` component <+> text ":" <+> Gluon.pprExp ty

-------------------------------------------------------------------------------

type StmtContext = Stmt -> Stmt

-- | Objects that can have statements put around them.
-- There is an instance for 'Stmt', which simply applies the context to
-- the statement, and an instance for 'StmtContext', which composes the
-- two contexts. 
class StmtExtensible a where
  -- | @addContext ctx x@ builds some statements @ctx@ around some object @x@,
  -- returning a new object.
  addContext :: StmtContext -> a -> a

instance StmtExtensible Stmt where
  addContext = id

instance StmtExtensible (Stmt -> Stmt) where
  addContext = (.)

instance StmtExtensible a => StmtExtensible (a, b) where
  addContext ctx (x, y) = (addContext ctx x, y)

idContext :: StmtContext
idContext = id

-- | Allocate local storage for some statement
allocateLocalMemory :: SourcePos -> Var -> RType -> StmtContext
allocateLocalMemory pos v ty stmt =
  if varID v `Map.member` fexpEffect stmt
  then internalError "Side effect to local variable escapes"
  else LocalS (extendStmtInfo pos id stmt) v ty stmt

-- | Perform two actions in sequence.  If the first action writes a variable
-- that's read by the second action, put a 'ReadingS' statment around the
-- second action and mask out the effect.
eval :: SourcePos -> Stmt -> StmtContext
eval pos s1 s2 =
  let s2' =
        -- If s1 writes a variable, and this variable is part of s2's effect,
        -- then we need to insert a read operation around s2
        case fexpReturn s1 
        of VariableReturn write_ty write_var
             | varID write_var `Map.member` fexpEffect s2 ->
                 locallyRead pos write_var write_ty s2
           _ -> s2
      effect1 = fexpEffect s1
      effect2 = fexpEffect s2'
      info = mkFlatInfo pos (fexpReturn s2') (Map.union effect1 effect2)
  in EvalS info s1 s2'

-- | Change a writeable variable to a readable one over the scope of a
-- statement
locallyRead :: SourcePos -> Var -> RType -> StmtContext
locallyRead pos var ty stmt =
  let -- Do not propagate effects on this variable
      info = extendStmtInfo pos (Map.delete (varID var)) stmt
  in ReadingS info var ty stmt

-- | Assign a value to a local variable over the scope of a statement
assignTemporaryValue :: SourcePos -> Var -> RType -> Component -> Stmt
                     -> StmtContext
assignTemporaryValue pos v ty mode stmt body =
  let effect1 = fexpEffect stmt
      info = extendStmtInfo pos (Map.union effect1) body
  in LetS info (Binder v ty mode) stmt body

-------------------------------------------------------------------------------
-- A monad that keeps track of types and function side effects

type FunctionEffect = [FlatArgument] -> Effect

newtype F a = F (Map.Map Var FunctionEffect -> PureTC a)

instance Monad F where
  return x = F $ \_ -> return x
  F m >>= k = F $ \env -> do x <- m env
                             case k x of F m' -> m' env

instance Supplies F (Ident Var) where
  fresh = F $ \_ -> fresh
  supplyToST f = F $ \_ -> supplyToST f

instance EvalMonad F where
  liftEvaluation m = F $ \_ -> liftEvaluation m

instance PureTypeMonad F where
  assumePure v t (F m) = F $ \env -> assumePure v t (m env)
  getType v = F $ \_ -> getType v
  peekType v = F $ \_ -> peekType v
  getType' pos v = F $ \_ -> getType' pos v
  peekType' pos v = F $ \_ -> peekType' pos v
  getPureTypes = F $ \_ -> getPureTypes
  liftPure m = F $ \_ -> m
  formatEnvironment f = F $ \env ->
    formatEnvironment (\doc -> case f doc of F m -> m env)

instance TypeErrorMonad F where
  logError e = F $ \_ -> logError e
  throwError e = F $ \_ -> throwError e
  recover (F m) = F $ \env -> recover (m env)

instance PureTypeErrorMonad F

runF :: Supply (Ident Var) -> F a -> IO (Either [TypeCheckError] a)
runF var_id_supply (F m) = runPureTCIO var_id_supply (m Map.empty)

-- | Add side effect information to the local environment
assumeEffect :: Var -> FunctionEffect -> F a -> F a
assumeEffect v eff m = F $ \env ->
  let env' = Map.insert v eff env
  in case m of F f -> f env'

-- | Look up a function's effect
lookupEffect :: Var -> F FunctionEffect
lookupEffect v = F $ \env ->
  case Map.lookup v env
  of Nothing -> internalError $ "lookupEffect " ++ show v
     Just e -> return e

-------------------------------------------------------------------------------

-- | Find a parameter-passing convention dictionary for this type variable
-- in the environment.  Throw an error if it can't be found. 
findVarPassConv :: Var -> F Value
findVarPassConv v = do
  result <- findM matchType =<< getPureTypes
  case result of
    Just (dict_var, _) -> return $ VarV dict_var Value
    Nothing -> internalError "findVarPassConv: Can't find dictionary"
  where
    -- Return True if ty == PassConv v, False otherwise
    matchType (_, ty) = do
      ty' <- evalHead' ty
      case unpackRenamedWhnfAppE ty' of
        Just (con, [arg]) | con `isPyonBuiltin` the_PassConv -> do
          arg' <- evalHead arg
          case fromWhnf arg' of
            Gluon.VarE {Gluon.expVar = v'} -> return (v == v')
            _ -> return False
        _ -> return False

-- | Get an expression that computes this value's parameter-passing convention
getPassConv :: RType -> F Value
getPassConv ty = getPassConv' =<< evalHead' ty

getPassConv' :: TypeOf (Whnf Rec) (Whnf (Subst Rec)) -> F Value
getPassConv' ty =
  case Gluon.unpackRenamedWhnfAppE ty of
    Just (con, [])
      | con `Gluon.isBuiltin` Gluon.the_Int -> primitive the_passConv_Int
      | con `Gluon.isBuiltin` Gluon.the_Float -> primitive the_passConv_Float
      | con `isPyonBuiltin` the_bool -> primitive the_passConv_bool
      | con `isPyonBuiltin` the_Any -> primitive the_passConv_Any
    Just (con, [t1, t2])
      | con == getPyonTupleType' 2 -> do
          pc1 <- getPassConv' =<< evalHead t1
          pc2 <- getPassConv' =<< evalHead t2
          return $ AppV (ConV (getPyonTuplePassConv' 2) Value)
            [TypeV (substFully t1), TypeV (substFully t2), pc1, pc2]
    Nothing ->
      case fromWhnf ty of
        Gluon.VarE {Gluon.expVar = v} ->
          findVarPassConv v
    _ -> internalError "lookupPassConv"
  where
    primitive pc =
      let con = pyonBuiltin pc
      in return $ ConV con Value

newAnonymousVariable :: F Var
newAnonymousVariable = do
  v_id <- fresh
  return $ Gluon.mkAnonymousVariable v_id ObjectLevel

-- | Choose a parameter-passing mode for a data type.
-- Dictionary types inserted by type inference are passed by value.
-- Functions are passed as closures.
-- Other types are passed by reference.
chooseMode :: RType -> F Mode
chooseMode t
  | getLevel t == ObjectLevel = internalError "chooseMode"
  | getLevel t /= TypeLevel = return ByVal
  | otherwise = do
      t' <- evalHead' t
      return $! case Gluon.unpackRenamedWhnfAppE t'
                of Just (con, _)
                     | isDictionaryTypeConstructor con -> ByVal
                     | otherwise -> ByRef
                   Nothing -> case substFullyUnder $ fromWhnf t'
                              of Gluon.FunE {} -> ByClo
                                 _ -> ByRef

-- | Build the argument list for a function call
buildCallArguments :: [FlatArgument] -> FlatReturn -> [Value]
buildCallArguments args ret =
  mapMaybe addr_parameter args ++
  maybeToList return_addr_parameter ++
  mapMaybe value_parameter args ++
  maybeToList return_ptr_parameter ++
  maybeToList return_state_parameter
  where
    addr_parameter (ValueArgument _) = Nothing
    addr_parameter (ClosureArgument _ _) = Nothing
    addr_parameter (VariableArgument v) = Just (VarV v Address)
    
    value_parameter (ValueArgument fv) = Just fv
    value_parameter (ClosureArgument v _) = Just v
    value_parameter (VariableArgument v) = Just (VarV v Pointer)
    
    (return_addr_parameter, return_ptr_parameter, return_state_parameter) =
      case ret
      of ValueReturn _ -> (Nothing, Nothing, Nothing)
         ClosureReturn _ _ -> (Nothing, Nothing, Nothing)
         VariableReturn _ v ->
           (Just (VarV v Address),
            Just (VarV v Pointer),
            Just (VarV v State))

addressParameter, valueParameter, valueOnlyParameter, stateParameter
  :: RPat -> Mode -> Maybe (RBinder Component)

addressParameter (VarP v ty) mode =
  case mode
  of ByVal -> Nothing
     ByClo -> Nothing
     ByRef -> Just $ Binder v ty Address

addressParameter _ _ = internalError "Expecting a variable parameter"

valueParameter (VarP v ty) mode =
  case mode
  of ByVal -> Just $ Binder v ty Value
     ByClo -> Just $ Binder v ty FunRef
     ByRef -> Just $ Binder v ty Pointer

valueParameter _ _ = internalError "Expecting a variable parameter"

valueOnlyParameter (VarP v ty) mode =
  case mode
  of ByVal -> Just $ Binder v ty Value
     ByClo -> Just $ Binder v ty FunRef
     ByRef -> internalError "Unexpected pass-by-reference parameter"

valueOnlyParameter _ _ = internalError "Expecting a variable parameter"

stateParameter (VarP v ty) mode =
  case mode
  of ByVal -> Nothing
     ByClo -> Nothing
     ByRef -> Just $ Binder v ty State

stateParameter _ _ = internalError "Expecting a variable parameter"

patternEffects :: [(RPat, Mode)] -> Effect
patternEffects patterns = Map.fromList $ mapMaybe effect patterns
  where
    effect (VarP v _, ByRef) = Just (varID v, ())
    effect (VarP v _, ByVal) = Nothing
    effect (VarP v _, ByClo) = Nothing
    effect _ = internalError "patternEffects"

functionTypeEffect :: RType -> F FunctionEffect
functionTypeEffect ty = do
  p_effects <- parameter_effects ty
  return $ \arguments -> compute_effect p_effects arguments
  where
    -- To compute the side effect, combine the side effects of all parameters
    -- that are actually used.
    --
    -- Since we restrict how partial application can occur, either this will 
    -- have no side effect, or all parameters will be used.
    compute_effect effs args =
      let effect = foldr ($) noEffect $ zipWith ($) effs args
      in if length args < length effs && not (Map.null effect)
         then internalError "functionTypeEffect: partial application with effect"
         else effect

    -- For each parameter, compute its contribution to the overall
    -- function effect
    parameter_effects ty =
      case ty
      of Gluon.FunE { Gluon.expMParam = Binder' mv ty ()
                    , Gluon.expRange = rng}
           | getLevel ty == KindLevel -> ignore_continue rng 
           | getLevel ty == TypeLevel && isNothing mv -> do
               mode <- chooseMode ty
               case mode of ByVal -> ignore_continue rng
                            ByRef -> add_effect_continue rng
                            ByClo -> ignore_continue rng
           | otherwise -> internalError "functionTypeEffect"
         _ -> end
      where
        -- ignore this parameter
        ignore_continue rng = liftM (ignore :) $ parameter_effects rng

        -- This parameter's effect should be added
        add_effect_continue rng = liftM (add_effect :) $ parameter_effects rng
        
        end = return []
        
        ignore _ effect = effect
        
        add_effect (VariableArgument v) effect = Map.insert (varID v) () effect
        add_effect _ effect = internalError "functionTypeEffect"
        
-- | Build the parameter list for a function
buildFunctionParameters :: [TyPat (Typed Rec)]
                        -> [Pat (Typed Rec)]
                        -> RType
                        -> F ([RBinder Component], Effect, Mode, FlatReturn)
buildFunctionParameters ty_params params return_type = do
  -- Determine parameter passing modes
  param_modes <- mapM choose_param_mode params
  return_mode <- chooseMode return_type
  
  -- Create a new variable for the return value
  (return_var, return_address, return_pointer, return_state) <-
    case return_mode
    of ByVal -> return (ValueReturn return_type, Nothing, Nothing, Nothing)
       ByRef -> do rv <- newAnonymousVariable
                   return (VariableReturn return_type rv,
                           Just (Binder rv return_type Address),
                           Just (Binder rv return_type Pointer),
                           Just (Binder rv return_type State))
       ByClo -> do return_effect <- functionTypeEffect return_type
                   return (ClosureReturn return_type return_effect,
                           Nothing, Nothing, Nothing)

  -- Construct parameter list and side effects
  let params' = zip (map fromTypedPat params) param_modes
      flat_params =
        map convert_ty_param ty_params ++
        mapMaybe (uncurry addressParameter) params' ++
        maybeToList return_address ++
        mapMaybe (uncurry valueParameter) params' ++
        maybeToList return_pointer ++
        maybeToList return_state
      effect = patternEffects params'

  return (flat_params, effect, return_mode, return_var)
  where
    convert_ty_param (TyPat v ty) = Binder v (fromTypedType ty) Value
    
    choose_param_mode (VarP v ty) = chooseMode (fromTypedType ty)
    choose_param_mode _ = internalError "not a variable parameter"

-- | Get the parameter and result types of a case alternative
getAltParameterTypes :: Alt (Typed Rec) -> F ([Gluon.WRExp], Gluon.WRExp)
getAltParameterTypes (Alt { altConstructor = con
                          , altTyArgs = ty_args
                          , altParams = param_vars
                          }) = do
  con_type <- liftPure $ getConstructorType con
  compute_fotype con_type ty_args
  where
    -- Compute the first-order type of a data constructor, instantiated with 
    -- type arguments 'args'  Assume the application is well-typed.
    compute_fotype :: Gluon.SRExp -> [TType] -> F ([Gluon.WRExp], Gluon.WRExp)
    compute_fotype ty (arg:args) = do
      ty' <- evalHead ty
      case fromWhnf ty' of
        Gluon.FunE {Gluon.expMParam = binder, Gluon.expRange = rng} -> do
          -- Assign the bound variable in the range
          ev_binder <- Gluon.traverseBinder' return (return . fromWhnf <=< evalFully) binder
          let rng' = assignBinder' ev_binder (fromTypedType arg) rng
          compute_fotype rng' args
        _ ->
          internalError "Too many arguments to constructor"

    compute_fotype ty [] = get_param_return_types ty
    
    -- Decompose a function type into a list of parameter and
    -- return types
    get_param_return_types ty = do
      ty' <- evalHead ty
      case fromWhnf ty' of
        Gluon.FunE { Gluon.expMParam = Binder' Nothing param_ty ()
                   , Gluon.expRange = rng} -> do
          real_param_ty <- evalFully param_ty
          (param_types, return_type) <- get_param_return_types rng
          return (real_param_ty : param_types, return_type)
        Gluon.FunE { Gluon.expMParam = Binder' (Just _) _ _} ->
          internalError "Dependently typed constructor"
        _ -> -- This is the return type 
          return ([], substFullyUnderWhnf ty')

-- | Build the parameter list for a case alternative
buildValueCaseParameters :: RType    -- ^ Scrutinee type
                         -> Alt (Typed Rec)
                         -> F (Con, [Value], [RBinder Component])
buildValueCaseParameters scrutinee_type alt = do
  -- Get types of the value parameters and scrutinee
  (param_types, inferred_scrutinee_type) <- getAltParameterTypes alt
  
  -- Scrutinee type should match.
  -- We assume the expression is well-typed, so skip the test.
  when False $ tcAssertEqual noSourcePos (verbatim scrutinee_type)
                                         (verbatim $ fromWhnf inferred_scrutinee_type)

  -- Determine parameter-passing modes
  param_modes <- mapM (chooseMode . fromWhnf) param_types
  
  -- Construct parameter binders
  let param_patterns = map fromBinder $ altParams alt
        where fromBinder (Binder v ty ()) = VarP v (fromTypedType ty)
      parameters =
        catMaybes $ zipWith valueOnlyParameter param_patterns param_modes
      ty_args = map (TypeV . fromTypedType) $ altTyArgs alt
  return (altConstructor alt, ty_args, parameters)

-- | Build the parameter list for a case alternative
buildRefCaseParameters :: RType    -- ^ Scrutinee type
                       -> Alt (Typed Rec)
                       -> F (Con, [Value], [RBinder Component], Effect)
buildRefCaseParameters scrutinee_type alt = do
  -- Get types of the value parameters and scrutinee
  (param_types, inferred_scrutinee_type) <- getAltParameterTypes alt
    
  -- Scrutinee type should match.
  -- We assume the expression is well-typed, so skip the test.
  when False $ tcAssertEqual noSourcePos (verbatim scrutinee_type)
                                         (verbatim $ fromWhnf inferred_scrutinee_type)

  -- Determine parameter-passing modes
  param_modes <- mapM (chooseMode . fromWhnf) param_types
  
  -- Construct parameter binders
  let param_patterns = zip (map fromBinder $ altParams alt) param_modes
        where fromBinder (Binder v ty ()) = VarP v (fromTypedType ty)
      addr_parameters = mapMaybe (uncurry addressParameter) param_patterns
      value_parameters = mapMaybe (uncurry valueParameter) param_patterns
      parameters = addr_parameters ++ value_parameters
      
  -- Compute side effect
  let effect = patternEffects param_patterns
  
  -- Create type parameters to the pattern 
  let ty_args = map (TypeV . fromTypedType) $ altTyArgs alt
  return (altConstructor alt, ty_args, parameters, effect)

-- | Calculate the effect of a function based on its type
-- and record the effect information in the environment.
assumeFunctionEffect :: Def (Typed Rec) -> F a -> F a
assumeFunctionEffect (Def fun_name fun) m = do
  parameterized_effect <- functionEffect fun
  assumeEffect fun_name parameterized_effect m

-- | Calculate the effect of a set of functions based on their types
-- and record the effect information in the environment.
assumeFunctionEffects :: DefGroup (Typed Rec) -> F a -> F a
assumeFunctionEffects dg m = do
  parameterized_effects <- sequence [functionEffect fun | Def _ fun <- dg]
  foldr assume_def_effect m $ zip dg parameterized_effects
  where
    assume_def_effect (Def fun_name _, eff) = assumeEffect fun_name eff

-------------------------------------------------------------------------------

flattenValueToStmt :: ExpInfo -> RType -> F (StmtContext, Value) -> F Stmt
flattenValueToStmt inf ty m = do
  (context, value) <- m
  let info = mkFlatInfo (getSourcePos inf) (ValueReturn ty) noEffect
  return (context $ ValueS info value)

-- | Make the value of an expression available over some local scope
withFlattenedExp :: StmtExtensible a =>
                    TExp -> (FlatArgument -> F a) -> F a
withFlattenedExp typed_expression@(TypedSFExp (TypeAnn (fromWhnf -> ty) _)) k = do
  mode <- chooseMode ty
  case mode of
    ByVal -> do
      (ctx, val) <- flattenExpValue (ValueReturn ty) typed_expression
      result <- k $ ValueArgument val
      return $ addContext ctx result
    ByClo -> do
      parameterized_eff <- functionTypeEffect ty
      (ctx, val) <- flattenExpValue (ClosureReturn ty parameterized_eff) typed_expression
      result <- k $ ClosureArgument val parameterized_eff
      return $ addContext ctx result
    ByRef -> do 
      (ctx, var) <- flattenExpReference typed_expression
      result <- k $ VariableArgument var
      return $ addContext ctx result

-- | Make the value of many expressions available over some local scope
withFlattenedExps :: StmtExtensible a =>
                     [TExp] -> ([FlatArgument] -> F a) -> F a
withFlattenedExps = withMany withFlattenedExp

-- | Flatten a function call expression.
flattenCall :: ExpInfo -> FlatReturn -> TExp -> Maybe [TExp] -> F Stmt
flattenCall inf ret mono_op margs =
  -- Generate code for the function call parameters
  withFlattenedExp poly_op $ \real_op_argument ->
  withFlattenedExps (fromMaybe [] margs) $ \object_args -> do
    -- Get the function call parameters
    let arguments = map (ValueArgument . TypeV . fromTypedType) ty_args ++
                    object_args
        params = buildCallArguments arguments ret
        (op, parameterized_effect) = expectClosureArgument real_op_argument
    
    -- Compute the function's effect
    let effect = parameterized_effect arguments

    -- Create the function call statement
    return $ CallS (mkFlatInfo pos ret effect) op params
  where
    pos = getSourcePos inf

    -- Get the real operator and its type arguments 
    (poly_op, ty_args) = extract_type_parameters mono_op
    
    extract_type_parameters :: TExp -> (TExp, [TType])
    extract_type_parameters e = unpack [] e
      where
        unpack types (discardExpType -> TyAppE {expOper = op, expTyArg = ty}) =
          unpack (ty : types) op
        unpack types e = (e, types)

-- | Flatten a \'let\' expression, making its bound variable available locally
flattenLet :: StmtExtensible a =>
              ExpInfo -> Pat (Typed Rec) -> TExp -> a -> F a
flattenLet inf (VarP v (fromTypedType -> ty)) rhs body = do
  -- Decide the variable's parameter passing mode
  mode <- chooseMode ty

  -- Assign the variable in the body's context
  assignment <-
    case mode
    of ByVal -> flattenExpWriteValue inf (ValueReturn ty) v rhs
       ByClo -> do eff <- functionTypeEffect ty
                   flattenExpWriteValue inf (ClosureReturn ty eff) v rhs
       ByRef -> do stmt <- flattenExpWriteReference v rhs
                   return $
                     allocateLocalMemory (getSourcePos inf) v ty .
                     eval (getSourcePos inf) stmt
                
  
  return $ addContext assignment body

-- | Flatten a \'letrec\' expression
flattenLetrec :: StmtExtensible a =>
                 SourcePos -> [Def (Typed Rec)] -> a -> F a
flattenLetrec pos defs body = do
  defs' <- mapM flattenDef defs
  let context body = 
        let finf = extendStmtInfo pos id body
        in LetrecS finf defs' body
  return $ addContext context body

-- | Flatten a \'case\' expression to a statement
flattenCase :: (TExp -> F Stmt) -> ExpInfo -> FlatReturn -> RType -> TExp
            -> [Alt (Typed Rec)]
            -> F Stmt 
flattenCase flattenBranch inf return_mode return_type scrutinee alts =
  withFlattenedExp scrutinee flatten
  where
    scrutinee_type = case scrutinee of TypedSFExp (TypeAnn ty _) -> fromWhnf ty

    -- Create a flattened case statement with the given scrutinee
    flatten (ValueArgument scrutinee_val) = do
      -- Flatten all case alternatives
      flat_alts <- mapM (flattenValAlt flattenBranch scrutinee_type) alts
      
      -- Get the return value of one of the alternatives (should be the same
      -- for all alternatives)
      let ret = fexpReturn $ valAltBody $ head flat_alts

      -- Take the union of all alternatives' side effects
      let effect = Map.unions $ map (fexpEffect . valAltBody) flat_alts
      
      let new_info = mkFlatInfo (getSourcePos inf) ret effect
      return $ CaseValS new_info scrutinee_val flat_alts

    flatten (VariableArgument scrutinee_var) = do
      -- Flatten all case alternatives
      flat_alts <- mapM (flattenRefAlt flattenBranch scrutinee_type) alts
      
      -- Get the return value of one of the alternatives (should be the same
      -- for all alternatives)
      let ret = fexpReturn $ refAltBody $ head flat_alts

      -- Take the union of all alternatives' side effects, after masking
      -- off the effect provided by the pattern match.
      -- Read the scrutinee as part of the effect.
      let alternatives_effect =
            Map.unions [ fexpEffect stmt Map.\\ local_eff
                       | FlatRefAlt _ _ _ local_eff _ _ stmt <- flat_alts]
          effect = alternatives_effect `Map.union` varEffect scrutinee_var
      
      let new_info = mkFlatInfo (getSourcePos inf) ret effect
      return $ CaseRefS new_info scrutinee_var scrutinee_type flat_alts

    flatten (ClosureArgument _ _) =
      internalError "flattenCase: scrutinee is a function"
      
    -- Flatten a value-case alternative
    flattenValAlt flattenBranch scrutinee_type alt = do
      -- Get the parameters to the pattern match  
      (con, ty_args, params) <- buildValueCaseParameters scrutinee_type alt

      -- Flatten the body
      body <- flattenBranch (altBody alt)
      return $ FlatValAlt con ty_args params body

    -- Flatten a reference-case alternative
    flattenRefAlt flattenBranch scrutinee_type alt = do
      -- Get the parameters to the pattern match  
      (con, ty_args, params, eff) <- buildRefCaseParameters scrutinee_type alt

      -- Flatten the body
      body <- flattenBranch (altBody alt)
      return $ FlatRefAlt con ty_args params eff return_mode return_type body

-- Expression flattening functions

-- | Flatten an expression whose result is a value.  Assign the value to
-- the given return variable.
flattenExpWriteValue :: ExpInfo -> FlatReturn -> Var -> TExp -> F StmtContext
flattenExpWriteValue _ (VariableReturn _ _) _ _ =
  internalError "flattenExpWriteValue"
flattenExpWriteValue inf return_mode dest
                     texp@(TypedSFExp (TypeAnn (fromWhnf -> ty) expression)) =
  case expression
  of VarE {expVar = v} -> returnValue $ VarV v return_component
     ConE {expCon = c} -> returnValue $ ConV c return_component
     LitE {expLit = l} -> returnValue $ LitV l
     TyAppE {expInfo = inf, expOper = op} -> do 
       stmt <- flattenCall inf return_mode texp Nothing
       return $ assignTemporaryValue pos dest ty return_component stmt
     CallE {expInfo = inf, expOper = op, expArgs = args} -> do
       stmt <- flattenCall inf return_mode op (Just args)
       return $ assignTemporaryValue pos dest ty return_component stmt
     FunE {expInfo = inf, expFun = f} -> do
       f' <- flattenFun f
       returnValue $ FunV f'
     LetE { expInfo = inf
          , expBinder = binder
          , expValue = rhs
          , expBody = body} ->
       -- Assign the bound variable, then write the destination value in the
       -- body expression
       flattenLet inf binder rhs =<< recursive body
     LetrecE {expInfo = inf, expDefs = defs, expBody = body} ->
       flattenLetrec pos defs =<< recursive body
     CaseE { expInfo = inf
           , expScrutinee = scrutinee
           , expAlternatives = alts} -> do
       let flatten_alt_body stmt =
             flattenValueToStmt inf ty $ flattenExpValue return_mode stmt
       stmt <- flattenCase flatten_alt_body inf return_mode ty scrutinee alts
       return $ assignTemporaryValue pos dest ty return_component stmt
  where
    pos = getSourcePos inf
    
    recursive = flattenExpWriteValue inf return_mode dest
    
    returnValue val =
      case return_mode
      of ValueReturn ty ->
           let value = ValueS (mkValueReturnInfo pos ty) val
           in return $ assignTemporaryValue pos dest ty Value value
         ClosureReturn ty eff ->
           let value = ValueS (mkClosureReturnInfo pos ty eff) val
           in return $ assignTemporaryValue pos dest ty FunRef value
         _ -> internalError "flattenExpWriteValue"

    return_component =
      case return_mode
      of ValueReturn _ -> Value
         ClosureReturn _ _ -> FunRef
         VariableReturn _ _ -> internalError "flattenExpWriteValue"

flattenExpValue :: FlatReturn -> TExp -> F (StmtContext, Value)
flattenExpValue (VariableReturn _ _) _ = internalError "flattenExpValue"

flattenExpValue return_mode
                typed_expression@(TypedSFExp (TypeAnn (fromWhnf -> ty) expression)) =
  case expression
  of VarE {expVar = v} -> returnValue $ VarV v return_component
     ConE {expCon = c} -> returnValue $ ConV c return_component
     LitE {expLit = l} -> returnValue $ LitV l
     TyAppE {expInfo = inf} -> do
       -- Create a temporary variable to hold the result
       tmp_var <- newAnonymousVariable
       
       stmt <- flattenCall inf return_mode typed_expression Nothing
       
       -- Bind the call's result to a variable
       let context = assignTemporaryValue pos tmp_var ty return_component stmt
           
       return (context, VarV tmp_var return_component)
     CallE {expInfo = inf, expOper = op, expArgs = args} -> do
       -- Create a temporary variable to hold the result
       tmp_var <- newAnonymousVariable
       
       -- Create the function call
       stmt <- flattenCall inf return_mode op (Just args)
       
       -- Bind the call's result to a variable
       let context = assignTemporaryValue pos tmp_var ty return_component stmt
           
       return (context, VarV tmp_var return_component)
     FunE {expInfo = inf, expFun = f} -> do
       f' <- flattenFun f
       returnValue $ FunV f'
     LetE { expInfo = inf
          , expBinder = binder
          , expValue = rhs
          , expBody = body} ->
       flattenLet inf binder rhs =<< flattenExpValue return_mode body
     LetrecE {expInfo = inf, expDefs = defs, expBody = body} ->
       flattenLetrec pos defs =<< flattenExpValue return_mode body
     CaseE {} | isValueReturn return_mode ->
       internalError "flattenExpValue: scrutinee is a function"
     CaseE { expInfo = inf
           , expScrutinee = scrutinee
           , expAlternatives = alts} -> do
       let flatten_alt_body stmt =
             flattenValueToStmt inf ty $ flattenExpValue return_mode stmt
       stmt <- flattenCase flatten_alt_body inf return_mode ty scrutinee alts
       
       -- Assign the value to a temporary variable
       tmp_var <- newAnonymousVariable
       let context = assignTemporaryValue pos tmp_var ty return_component stmt
       return (context, VarV tmp_var return_component)
  where
    pos = getSourcePos expression

    return_component =
      case return_mode
      of ValueReturn _ -> Value
         ClosureReturn _ _ -> FunRef
         VariableReturn _ _ -> internalError "flattenExpValue"
    
    returnValue v = return (idContext, v)

-- | Flatten an expression whose value will be read by reference.
-- The variable representing the expression's storage will be returned. 
flattenExpReference :: TExp -> F (StmtContext, Var)
flattenExpReference texp@(TypedSFExp (TypeAnn (fromWhnf -> ty) expression)) =
  case expression
  of VarE {expVar = v} -> return (idContext, v)
     ConE {expCon = c} -> do
       -- Allocate the constructor value in a local memory area
       tmp_var <- newAnonymousVariable
       let context = allocateLocalMemory pos tmp_var ty
       return (context, tmp_var)
     LitE {expLit = l} -> do
       -- Allocate the variable value in a local memory area
       tmp_var <- newAnonymousVariable
       let context body =
             let copy_value_info =
                   mkVariableReturnInfo (fexpSourcePos body) tmp_var ty
             in allocateLocalMemory pos tmp_var ty $
                eval pos (CopyValueS copy_value_info (LitV l)) $
                body
       return (context, tmp_var)
     TyAppE {expInfo = inf} -> do
       -- Create a temporary variable to hold the result
       tmp_var <- newAnonymousVariable
            
       -- Create a function call
       stmt <- flattenCall inf (VariableReturn ty tmp_var) texp Nothing

       -- Bind the call's result to a locally allocated variable
       let context body =
             allocateLocalMemory pos tmp_var ty $
             eval pos stmt body
       return (context, tmp_var)       
     CallE {expInfo = inf, expOper = op, expArgs = args} -> do
       -- Create a temporary variable to hold the result
       tmp_var <- newAnonymousVariable
            
       -- Create a function call
       stmt <- flattenCall inf (VariableReturn ty tmp_var) op (Just args)

       -- Bind the call's result to a locally allocated variable
       let context body =
             allocateLocalMemory pos tmp_var ty $ 
             eval pos stmt body
       return (context, tmp_var)
  where
    pos = getSourcePos expression

-- | Flatten an expression whose value will be written to the specified
-- variable.
flattenExpWriteReference :: Var -> TExp -> F Stmt
flattenExpWriteReference return_var texp@(TypedSFExp (TypeAnn (fromWhnf -> ty) expression)) =
  case expression
  of VarE {expInfo = inf, expVar = v} -> do
       -- Copy this variable to the destination
       pc <- getPassConv ty
       let new_info = mkFlatInfo pos return_mode (varEffect v)
       return $ CopyS new_info v
     ConE {expCon = c} ->
       returnValue $ ConV c Value
     LitE {expLit = l} ->
       returnValue $ LitV l
     FunE {} -> internalError "flattenExpWriteReference: unexpected function"
     TyAppE {expInfo = inf} ->
       flattenCall inf return_mode texp Nothing
     CallE {expInfo = inf, expOper = op, expArgs = args} ->
       flattenCall inf return_mode op (Just args)
     LetE { expInfo = inf
          , expBinder = binder
          , expValue = rhs
          , expBody = body} -> do
       flattenLet inf binder rhs =<< flattenExpWriteReference return_var body
     LetrecE {expInfo = inf, expDefs = defs, expBody = body} ->
       flattenLetrec pos defs =<< flattenExpWriteReference return_var body
     CaseE { expInfo = inf
           , expScrutinee = scrutinee
           , expAlternatives = alts} ->
       flattenCase (flattenExpWriteReference return_var) inf return_mode ty scrutinee alts
  where
    pos = getSourcePos $ expInfo expression
    
    return_mode = VariableReturn ty return_var
    
    returnValue val =
      return $ CopyValueS (mkVariableReturnInfo pos return_var ty) val

-- | Compute a function's side effect.  Return the side effect as a function
-- of the arguments.
functionEffect :: Fun (Typed Rec) -> F ([FlatArgument] -> Effect)
functionEffect (TypedSFFun (TypeAnn _ function)) =
  functionEffect' (funTyParams function) (funParams function) (fromTypedType $ funReturnType function)

functionEffect' :: [TyPat (Typed Rec)] -> [Pat (Typed Rec)] -> RType
                -> F ([FlatArgument] -> Effect)
functionEffect' ty_params params return_type = do
  (_, eff, _, _) <- buildFunctionParameters ty_params params return_type
  return $ makeEffect params eff
  where
    makeEffect fun_params eff args =
      -- For each variable argument, rename the corresponding parameter to
      -- that argument
      let param_map = Map.fromList $ catMaybes $
                      zipWith associate_param fun_params args
          rename_effect k =
            case Map.lookup k param_map
            of Just k' -> k'
               Nothing -> internalError "functionEffect"
      in Map.mapKeys rename_effect eff
    
    -- Map the function's parameter variable to the callsite's actual variable
    associate_param (VarP parameter_v _) (VariableArgument argument_v) =
      Just (varID parameter_v, varID argument_v)

    associate_param (VarP _ _) (ValueArgument _) =
      Nothing

    associate_param (VarP _ _) (ClosureArgument _ _) =
      Nothing

    associate_param _ _ = internalError "functionEffect"
         
flattenFun :: Fun (Typed Rec) -> F FlatFun
flattenFun (TypedSFFun (TypeAnn _ function)) = do
  let return_type = fromTypedType $ funReturnType function
  (params, eff, mode, ret) <-
    buildFunctionParameters (funTyParams function) (funParams function) return_type
  
  -- Convert function body
  body <-
    assumeValueParameters params $
    case mode
    of ByVal -> do
         -- Flatten the expression and return its result value
         (ctx, val) <- flattenExpValue (ValueReturn return_type) (funBody function)
         let return_value =
               ValueS (mkValueReturnInfo body_pos return_type) val
         return $ ctx return_value
       ByRef ->
         case ret
         of VariableReturn _ v ->
              -- Flatten the expression,
              -- which writes the result as a side effect
              flattenExpWriteReference v (funBody function)
            _ -> internalError "flattenFun"
       ByClo -> do
         -- Flatten the expression and return its result value
         parameterized_effect <- functionTypeEffect return_type
         (ctx, val) <- flattenExpValue (ClosureReturn return_type parameterized_effect) (funBody function)
         let return_value =
               ValueS (mkClosureReturnInfo body_pos return_type parameterized_effect) val
         return $ ctx return_value

  return $ FlatFun { ffunInfo = funInfo function
                   , ffunParams = params
                   , ffunReturn = ret
                   , ffunReturnType = fromTypedType $ funReturnType function
                   , ffunEffect = eff
                   , ffunBody = body
                   }
  where
    body_pos = getSourcePos $ expInfo $ discardExpType (funBody function)

    -- Assume variables bound by one of the binders
    assumeValueParameters params m = foldr assumeValueParameter m params

    assumeValueParameter (Binder v ty Value) m = assumePure v ty m
    assumeValueParameter (Binder _ _ _)      m = m

flattenDef :: Def (Typed Rec) -> F FlatDef
flattenDef (Def v f) = do
  f' <- flattenFun f
  return $ FlatDef v f'

flattenDefGroup :: DefGroup (Typed Rec) -> F a -> F ([FlatDef], a)
flattenDefGroup dg m =
  -- Add the functions' side effects to the local environment
  assumeFunctionEffects dg $ do
    dg' <- mapM flattenDef dg
    x <- m
    return (dg', x)

flattenTopLevelDefGroups (dg:dgs) =
  liftM (uncurry (:)) $ flattenDefGroup dg $ flattenTopLevelDefGroups dgs 

flattenTopLevelDefGroups [] = return []

flattenModule :: Module (Typed Rec) -> F [[FlatDef]]
flattenModule (Module defss exports) = do
  defss' <- flattenTopLevelDefGroups defss
  return defss'

flatten :: RModule -> IO (Anf.Module Rec)
flatten mod = do
  -- Get type information
  result1 <- typeCheckModule annotateTypes mod

  case result1 of
    Left errs -> fail "Type checking failed"
    Right tc_mod ->
      withTheVarIdentSupply $ \var_supply -> do
        result2 <- runF var_supply $ flattenModule tc_mod
        case result2 of
          Left errs -> fail "Flattening failed"
          Right defss -> do print $ vcat $ map (vcat . map pprFlatDef) defss 
                            runToAnf var_supply $ anfModule defss

-------------------------------------------------------------------------------

-- | Pure variable information.
data VarElaboration =
    ValueVar { valueType :: !RType
             }
  | ReferenceVar { addressVar :: !Var
                 , pointerVar :: !Var
                 , objectType :: !RType
                 }

-- | State variable information.
data VarStateElaboration =
  VarStateElaboration { isDefinedVar :: {-# UNPACK #-} !Bool
                        -- | The type of the object associated with this
                        -- state variable.  If the type is @a@, then the
                        -- state variable's type is @a \@ foo@ or
                        -- @Undef a \@ foo@ for some address @foo@.
                      , stateVar :: !Var
                      }
  deriving(Eq)

data ToAnfEnv =
  ToAnfEnv
  { anfVariableMap :: Map.Map (Ident Var) VarElaboration
  }

data ToAnfState =
  ToAnfState
  { anfStateMap :: Map.Map (Ident Var) VarStateElaboration
  }

-- | Find the common parts of two state maps.
-- The state maps must have the same key set.
anfStateMapIntersection :: Map.Map (Ident Var) VarStateElaboration
                        -> Map.Map (Ident Var) VarStateElaboration
                        -> Map.Map (Ident Var) VarStateElaboration
anfStateMapIntersection m1 m2
  | Map.keysSet m1 /= Map.keysSet m2 =
      internalError "anfStateMapIntersection: Different states"
  | otherwise =
      Map.mapMaybe id $ Map.intersectionWith compare_values m1 m2
  where
    compare_values e1 e2
      | e1 == e2 = Just e1
      | otherwise = Nothing

-- | Find the intersection of all maps in the list and the
-- unique parts of each input map.
anfStateMapDifference :: [Map.Map (Ident Var) VarStateElaboration]
                      -> ( Map.Map (Ident Var) VarStateElaboration
                         , [Map.Map (Ident Var) VarStateElaboration]
                         )
anfStateMapDifference [] = (Map.empty, [])
anfStateMapDifference ms =
  let isxn = foldr1 anfStateMapIntersection ms
      uniques = map (Map.\\ isxn) ms
  in (isxn, uniques)

-- | When converting to ANF, we keep track of the variables that are in scope:
-- For each variable, keep track of its corresponding address, pointer, value,
-- and/or state variables.
-- Maintain a type environment of intuitionistic variables, but not linear
-- variables.
-- Keep track of all parameter-passing conventions for use in code generation.

newtype ToAnf a = ToAnf (RWST ToAnfEnv () ToAnfState PureTC a) deriving(Monad)

instance EvalMonad ToAnf where
  liftEvaluation m = ToAnf $ RWST $ \r s -> do
    x <- liftEvaluation m
    return (x, s, mempty)

instance PureTypeMonad ToAnf where
  assumePure v t = liftPureToAnfT (assumePure v t)
  formatEnvironment f =
    ToAnf $ RWST $ \r s ->
    formatEnvironment $ \doc ->
    case f doc of ToAnf m -> runRWST m r s

-- | Run several computations and combine their results.  All computations 
-- start with the same initial state.  The final states must be reconciled 
-- to produce a consistent final state.
anfParallel :: (ToAnfState -> [ToAnfState] -> (ToAnfState, b))
            -> [ToAnf a]
            -> ToAnf ([a], b)
anfParallel reconcile ms = ToAnf $ RWST $ \r s -> do
  -- Run all steps with the same starting state
  results <- forM ms $ \(ToAnf m) -> runRWST m r s
  let (final_values, final_states, final_outputs) = unzip3 results

  -- Reconcile results
  let (s', log) = reconcile s final_states
  return ((final_values, log), s', mconcat final_outputs)

-- | Do not permit access to state variables in this computation
hideState :: ToAnf a -> ToAnf a
hideState (ToAnf m) = ToAnf $ RWST $ \r s -> do
  let local_s = ToAnfState Map.empty
  (x, s', w) <- runRWST m r local_s
  unless (Map.null $ anfStateMap s') $
    internalError "hideState: State escapes"
  return (x, s, w)

runToAnf :: Supply (Ident Var) -> ToAnf a -> IO a
runToAnf var_supply (ToAnf m) = do
  let env = ToAnfEnv Map.empty
      st  = ToAnfState Map.empty
  result <- runPureTCIO var_supply (runRWST m env st)
  case result of
    Left errs -> do fail "flattening failed"
                    return undefined
    Right (x, _, _) -> return x

instance Supplies ToAnf (Ident Var) where
  fresh = liftPureToAnf fresh
  supplyToST f = liftPureToAnf (supplyToST f)

liftPureToAnf :: PureTC a -> ToAnf a
liftPureToAnf m = ToAnf $ lift m

liftPureToAnfT :: (forall b. PureTC b -> PureTC b) -> ToAnf a -> ToAnf a
liftPureToAnfT t (ToAnf m) = ToAnf $ RWST $ \r s -> t (runRWST m r s)

-- | Strict variant of 'asks'.
asksStrict f = RWST $ \r s ->
  let value = f r
  in value `seq` return (value, s, mempty)
  
-- | Strict variant of 'gets'.
getsStrict f = RWST $ \r s ->
  let value = f s
  in value `seq` return (value, s, mempty)

getAddrVariable, getPointerVariable, getValueVariable, getStateVariable
  :: Var -> ToAnf Var

getAddrVariable v = getAddrVariable' (varID v)

getAddrVariable' v =
  ToAnf $ asksStrict (lookup_addr_variable . anfVariableMap)
  where
    lookup_addr_variable env =
      case Map.lookup v env
      of Just (ReferenceVar {addressVar = v'}) -> v'
         Just (ValueVar {}) -> internalError "getAddrVariable: Not a reference"
         Nothing -> internalError "getAddrVariable: No information"

getPointerVariable v =
  ToAnf $ asksStrict (lookup_pointer_variable . anfVariableMap)
  where
    lookup_pointer_variable env =
      case Map.lookup (varID v) env
      of Just (ReferenceVar {pointerVar = v'}) -> v'
         Just (ValueVar {}) -> internalError "getPointerVariable: Not a pointer"
         Nothing -> internalError "getPointerVariable: No information"

getValueVariable v =
  ToAnf $ asksStrict (lookup_value_variable . anfVariableMap)
  where
    lookup_value_variable env =
      case Map.lookup (varID v) env
      of Just (ValueVar {}) -> v
         Just (ReferenceVar {}) -> internalError "getValueVariable: Not a value"
         Nothing -> internalError $ "getValueVariable: No information"

getStateVariable v = ToAnf $ getsStrict (lookup_state_variable . anfStateMap)
  where
    lookup_state_variable env =
      case Map.lookup (varID v) env
      of Just (VarStateElaboration {stateVar = v'}) -> v'
         Nothing -> internalError $
                    "getStateVariable: No information for " ++ show v

-- | For debugging; calls 'getStateVariable'
getStateVariableX s v = getStateVariable v 
  -- trace s $ getStateVariable v

-- | Get the address, pointer, and state variables for a reference variable
getWriteReferenceVariables v = do
  a <- getAddrVariable v
  p <- getPointerVariable v
  s <- getStateVariableX "getWriteReferenceVariables" v
  return (a, p, s)

getReadReferenceVariables v = do
  a <- getAddrVariable v
  p <- getPointerVariable v
  return (a, p)

getPointerType :: Var -> ToAnf RType
getPointerType v = do
  addr <- getAddrVariable v
  return $ Gluon.mkInternalConAppE (Anf.anfBuiltin Anf.the_Ptr)
           [Gluon.mkInternalVarE addr]

getEffectType :: Var -> ToAnf RType
getEffectType v = getEffectType' (varID v)

getEffectType' :: VarID -> ToAnf RType
getEffectType' v = do
  addr <- getAddrVariable' v
  eff_type <- ToAnf $ asksStrict (lookup_object_type . anfVariableMap)
  return $ Gluon.mkInternalConAppE (Gluon.builtin Gluon.the_AtE) [eff_type, Gluon.mkInternalVarE addr]
  where
    lookup_object_type env =
      case Map.lookup v env
           of Just (ReferenceVar {objectType = t}) -> t
              Just (ValueVar {}) -> internalError "getEffectType: Not a reference"
              Nothing -> internalError "getEffectType: No information"

-- | Get the object type of the data referenced by a state variable.  The
-- type does not include modifiers indicating whether the variable is defined.
getObjectType :: Var -> ToAnf RType
getObjectType v = ToAnf $ asksStrict (lookup_object_type . anfVariableMap)
  where
    lookup_object_type env =
      case Map.lookup (varID v) env
           of Just (ReferenceVar {objectType = t}) -> t
              Just (ValueVar {}) -> internalError "getStateType: Not a reference"
              Nothing -> internalError "getStateType: No information"

getStateType :: Var -> ToAnf RType
getStateType v = do
  addr <- getAddrVariable v
  obj_type <- getObjectType v
  let at = Gluon.builtin Gluon.the_AtS
  return $ Gluon.mkInternalConAppE at [obj_type, Gluon.mkInternalVarE addr]

getUndefStateType :: Var -> ToAnf RType
getUndefStateType v = do
  addr <- getAddrVariable v
  obj_type <- getObjectType v
  let at = Gluon.builtin Gluon.the_AtS
      undef = Anf.anfBuiltin Anf.the_Undef
  return $ Gluon.mkInternalConAppE at [Gluon.mkInternalConAppE undef [obj_type], Gluon.mkInternalVarE addr]

-- | Record that a state variable has been used and had its contents defined
defineStateVariable :: Var -> ToAnf ()
defineStateVariable v = ToAnf $ do
  put =<< lift . mark_as_defined =<< get
  where
    -- Create a new variable and mark the state as defined
    mark_as_defined s =
      case Map.lookup (varID v) $ anfStateMap s
      of Just elaboration@(VarStateElaboration {stateVar = sv}) -> do
           sv' <- duplicateVar sv
           let elaboration' = elaboration { isDefinedVar = True
                                          , stateVar = sv'}
           return $ s {anfStateMap = Map.insert (varID v) elaboration' $ anfStateMap s}
         Nothing -> internalError $ "defineStateVariable: Not in scope: " ++ show v

-- | Remove a state variable from the environment
consumeStateVariable :: Var -> ToAnf ()
consumeStateVariable v = ToAnf $ modify (delete v)
  where
    delete v s = s {anfStateMap = Map.delete (varID v) $ anfStateMap s}

-- | Get the parameter-passing convention for this type.
getAnfPassConv :: RType -> ToAnf Anf.RVal
getAnfPassConv passed_type = do
  passed_type' <- evalHead' passed_type 
  case unpackRenamedWhnfAppE passed_type' of
    Just (con, [])
      | con `Gluon.isBuiltin` Gluon.the_Int ->
          return $ Anf.mkConV pos $ Anf.anfBuiltin Anf.the_PassConv_int
      | con `Gluon.isBuiltin` Gluon.the_Float ->
          return $ Anf.mkConV pos $ Anf.anfBuiltin Anf.the_PassConv_float
    Just (con, args) 
      | Just size <- whichPyonTupleTypeCon con -> do
          let pass_conv_con =
                case size
                of 2 -> Anf.anfBuiltin Anf.the_PassConv_PyonTuple2
                   
          -- Compute parameter-passing conventions for tuple fields
          field_pass_convs <- mapM getAnfPassConv (map substFully args)
          
          -- Pass the tuple field types and parameter-passing
          -- conventions to the tuple parameter-passing convention constructor
          let params = map (Anf.mkExpV . substFully) args ++
                       field_pass_convs
          return $ Anf.mkAppV pos (Anf.mkConV pos pass_conv_con) params
    Nothing ->
      case fromWhnf passed_type'
      of Gluon.VarE {Gluon.expVar = v} -> do
           -- Look up in the environment
           result <- liftPureToAnf $ findM matchType =<< getPureTypes
           case result of
             Just (dict_var, _) -> return $ Anf.mkInternalVarV dict_var
             Nothing -> internalError "getAnfPassConv: Can't find dictionary"
  where
    pos = getSourcePos passed_type

    passed_type_v = verbatim passed_type

    -- Return True if ty == PassConv passed_type, False otherwise
    matchType (_, ty) = do
      ty' <- evalHead' ty
      case unpackRenamedWhnfAppE ty' of
        Just (con, [arg]) | con `isPyonBuiltin` the_PassConv ->
          testEquality passed_type_v arg
        _ -> return False

withVariableElaboration :: Var -> VarElaboration -> ToAnf a -> ToAnf a
withVariableElaboration v elaboration (ToAnf m) =
  ToAnf $ local add_elaboration m
  where
    add_elaboration env =
      env {anfVariableMap =
              Map.insert (varID v) elaboration $ anfVariableMap env}

-- | Define the variable as a value variable
withValueVariable :: Var -> RType -> ToAnf a -> ToAnf a
withValueVariable v ty k =
  withVariableElaboration v (ValueVar {valueType = ty}) $
  assumePure v ty $
  k

withClosureVariable :: Var -> RType -> ToAnf a -> ToAnf a
withClosureVariable v ty k =
  withVariableElaboration v (ValueVar {valueType = ty}) $
  assumePure v ty $
  k

-- | The variable is pass-by-reference.  Define address and pointer variables
-- for it.
withReferenceVariable :: Var -> RType -> ToAnf a -> ToAnf a
withReferenceVariable v ty k = do
  -- Create new variables for the address and pointer
  address_var_id <- fresh
  pointer_var_id <- fresh
  let address_var = Gluon.mkVar address_var_id (varName v) ObjectLevel
      pointer_var = Gluon.mkVar pointer_var_id (varName v) ObjectLevel
    
  -- Put into environment
  withVariableElaboration v (ReferenceVar address_var pointer_var ty) $
    assumePure address_var addressType $
    assumePure pointer_var (pointerType (Gluon.mkInternalVarE address_var)) $
    k

withStateVariable :: Var -> ToAnf a -> ToAnf a
withStateVariable v (ToAnf m) = ToAnf $ do
  -- Create a new state variable
  new_v_id <- lift fresh
  let new_v = Gluon.mkVar new_v_id (varName v) ObjectLevel

  -- Run the computation with the modified state.
  -- Ensure that the state has been consumed.
  modify (add_local_state new_v)
  x <- m
  verify_local_state
  return x
  where
    add_local_state new_v env =
      env {anfStateMap = add_local_state2 new_v $ anfStateMap env}

    -- Ensure that the state variable was consumed
    verify_local_state = do
      m <- gets anfStateMap
      when (varID v `Map.member` m) $
        internalError "withStateVariable: state escapes"
      
    add_local_state2 new_v m =
      let elaboration = VarStateElaboration False new_v
      in Map.insert (varID v) elaboration m

-------------------------------------------------------------------------------

anfValue :: SourcePos -> Value -> ToAnf Anf.RVal
anfValue pos value =
  case value
  of VarV v component -> do
       real_v <- get_var_component v component
       return $ Anf.mkVarV pos real_v
     ConV c Value -> return $ Anf.mkConV pos c
     ConV c FunRef -> return $ Anf.mkConV pos c
     ConV c _ -> internalError "anfValue"
     LitV (IntL n) -> return $ Anf.mkLitV pos (Gluon.IntL n)
     TypeV ty -> return $ Anf.mkExpV ty
     FunV f -> do f' <- anfProc f
                  return $ Anf.mkLamV f'
     AppV op args -> do op' <- anfValue pos op
                        args' <- mapM (anfValue pos) args 
                        return $ Anf.mkAppV pos op' args'
  where
    get_var_component v component =
      case component
      of Value -> getValueVariable v
         FunRef -> getValueVariable v
         Address -> getAddrVariable v
         Pointer -> getPointerVariable v
         State -> getStateVariableX "anfValue" v

-- | Get the ANF type of a function
anfFunctionType :: FlatFun -> ToAnf RType
anfFunctionType ffun =
  add_parameters (ffunParams ffun) $
  convert_return_type (ffunReturnType ffun)
  where
    pos = getSourcePos (ffunInfo ffun)
    
    add_parameters params k = foldr add_parameter k params
    
    -- Create a function type by adding the parameter's type to the type
    -- produced by the continuation 'k'.
    -- Only type and address parameters are used dependently; we can use
    -- the given variables as dependent type/address variables without
    -- renaming them.
    add_parameter :: RBinder Component -> ToAnf RType -> ToAnf RType
    add_parameter (Binder v ty component) k =
      case component
      of Value
           | getLevel ty == KindLevel -> dependent
           | otherwise -> non_dependent
         FunRef -> dependent
         Address -> dependent
         Pointer -> non_dependent
         State -> non_dependent
      where
        dependent = do
          rng <- k
          return (Gluon.mkFunE pos False v ty rng)
        
        non_dependent = do
          rng <- k
          return (Gluon.mkArrowE pos False ty rng)

    convert_return_type ty = return ty

anfProc :: FlatFun -> ToAnf (Anf.Proc Rec)
anfProc ffun = hideState $
  -- Convert function parameters and make a local parameter mapping
  anfBindParameters return_variable (ffunParams ffun) $ \params -> do
    -- Convert return and effect types
    rt <- convert_return_type (ffunReturn ffun) (ffunReturnType ffun)
    et <- anfEffectType (ffunEffect ffun)

    -- Convert body
    body <- anfStmt $ ffunBody ffun
    
    -- Consume the return state, if ther is any
    case return_variable of
      Just v -> consumeStateVariable v
      Nothing -> return ()
    
    return $ Anf.Proc (ffunInfo ffun) params rt et body
  where
    -- Find the parameter variable that is being used for returning stuff
    -- It's the only parameter with component 'State'
    return_variable =
      case find is_return_parameter $ ffunParams ffun
      of Just (Binder v _ _) -> Just v
         Nothing -> Nothing
      where
        is_return_parameter (Binder _ _ State) = True
        is_return_parameter _ = False

    -- Not implemented: Convert return type
    convert_return_type _ rt = return rt

anfCreateParameterMaps :: Maybe Var -> [RBinder Component] -> ToAnf a -> ToAnf a
anfCreateParameterMaps return_var params k =
  foldr ($) k $ map (anfCreateParameterMap return_var) params
               
-- | Create variable elaboration information for a parameter.
-- Skip pointer and state parameters; handle them when the address 
-- parameter is encountered.
anfCreateParameterMap :: Maybe Var -> RBinder Component -> ToAnf a -> ToAnf a
anfCreateParameterMap return_var (Binder v ty component) k =
      case component
      of Value -> withValueVariable v ty k
         FunRef -> withValueVariable v ty k
         Address 
           | Just v == return_var ->
               withReferenceVariable v ty $ withStateVariable v k
           | otherwise ->
               withReferenceVariable v ty k
         Pointer -> k
         State -> k

anfBindParameters :: Maybe Var
                  -> [RBinder Component]
                  -> ([RBinder ()] -> ToAnf a)
                  -> ToAnf a
anfBindParameters return_var params k =
  anfCreateParameterMaps return_var params $ do
    k =<< mapM convert_parameter params
  where
    -- Convert a parameter binder to the ANF equivalent binder.
    -- Use the 'component' field of the binder to select the 
    -- actual variable and type.
    convert_parameter (Binder v ty component) =
      case component
      of Value -> do
           real_v <- getValueVariable v
           return $ Binder real_v ty ()
         FunRef -> do
           real_v <- getValueVariable v
           return $ Binder real_v ty ()
         Address -> do
           real_v <- getAddrVariable v
           return $ Binder real_v addressType ()
         Pointer -> do
           real_v <- getPointerVariable v
           real_ty <- getPointerType v
           return $ Binder real_v real_ty ()
         State -> do
           -- State parameters start out undefined
           real_v <- getStateVariableX "anfBindParameters" v
           real_ty <- getUndefStateType v
           return $ Binder real_v real_ty ()

-- | Compute the effect type corresponding to this effect.    
anfEffectType :: Effect -> ToAnf RType
anfEffectType eff = do
  types <- mapM getEffectType' $ Map.keys eff
  return $ foldr
    Gluon.Core.Builtins.Effect.sconj
    Gluon.Core.Builtins.Effect.empty
    types

anfDef :: FlatDef -> ToAnf (Anf.ProcDef Rec)
anfDef (FlatDef v f) = do
  f' <- anfProc f 
  return $ Anf.ProcDef v f'

anfDefGroup :: [FlatDef] -> ToAnf a -> ToAnf (Anf.ProcDefGroup Rec, a)
anfDefGroup dg m =
  -- Add the definition group to the local environment
  flip (foldr add_def_to_environment) dg $ do
    dg' <- mapM anfDef dg
    x <- m
    return (dg', x)
  where
    add_def_to_environment (FlatDef v fun) k = do
      -- Compute the new function type
      ty <- anfFunctionType fun
      
      -- Put it in the environment
      withClosureVariable v ty k

-- | Generate ANF code for a statement.
--
-- FIXME: Extra state variable parameters and returns are inserted here,
-- in the translation of 'ReadingS' and 'LocalS'.
-- Do we really handle those properly?
anfStmt :: Stmt -> ToAnf Anf.RStm
anfStmt statement =
  case statement
  of -- These cases have a corresponding ANF expression
     ValueS {fexpValue = val} -> do
       val' <- anfValue pos val
       return $ Anf.ReturnS anf_info val'
     CallS {fexpOper = op, fexpArgs = args} -> do
       op' <- anfValue pos op
       args' <- mapM (anfValue pos) args
       return $ Anf.CallS anf_info $ Anf.AppV anf_info op' args'
     LetS {fexpBinder = Binder v ty _, fexpRhs = rhs, fexpBody = body} -> do
       rhs' <- anfStmt rhs
       body' <- withValueVariable v ty $ anfStmt body
       return $ Anf.LetS anf_info (Binder v ty ()) rhs' body'
     EvalS {fexpRhs = rhs, fexpBody = body} ->
       case fexpReturn statement
       of VariableReturn ty v -> do
            state_v <- getStateVariableX "evalS" v
            state_ty <- getStateType v
            rhs' <- anfStmt rhs
            body' <- anfStmt body
            return $ Anf.LetS anf_info (Binder state_v state_ty ()) rhs' body'
          _ -> internalError "anfStmt"
     LetrecS {fexpDefs = defs, fexpBody = body} -> do
       (defs', body') <- anfDefGroup defs $ anfStmt body
       return $ Anf.LetrecS anf_info defs' body'
     CaseValS {fexpScrutinee = val, fexpValAlts = alts} -> do
       val' <- anfValue pos val
       alts' <- mapM anfAlternative alts
       return $ Anf.CaseS anf_info val' alts'
       
     -- These cases do not have a direct ANF translation, and instead must be
     -- converted to function calls
     CopyValueS {fexpValue = val} ->
       case fexpReturn statement
       of VariableReturn return_type dst ->
            anfStoreValue pos return_type dst val
          _ -> internalError "anfStmt"
     CaseRefS { fexpScrutineeVar = var
              , fexpScrutineeType = scr_ty
              , fexpRefAlts = alts} -> do
       anfCaseRef pos var scr_ty alts
     ReadingS { fexpScrutineeVar = var
              , fexpScrutineeType = ty
              , fexpBody = body} -> do
       anfReading pos ty (fexpReturn statement) var body
     LocalS {fexpVar = var, fexpType = ty, fexpBody = body} -> do
       anfLocal pos ty (fexpReturn statement) var body
     CopyS {fexpSrc = src} ->
       case fexpReturn statement
       of VariableReturn return_type dst ->
            anfCopyValue pos return_type dst src
          _ -> internalError "anfStmt"
  where
    pos = getSourcePos anf_info
    anf_info = fexpInfoInfo $ fexpInfo statement

anfReading :: SourcePos -> RType -> FlatReturn -> Var -> Stmt
           -> ToAnf Anf.RStm 
anfReading pos ty return_info var body = do
  -- Get the type of the variable to be read
  -- (should be a defined state variable)
  obj_type <- getObjectType var
  addr_var <- getAddrVariable var
  
  -- Turn the body into a lambda function
  body_fn <- anfStmtToProc no_extra_parameters body

  -- Create the parameter to the body function: either a state variable, or
  -- a unit value
  body_param <-
    case fexpReturn body
    of VariableReturn _ v -> liftM (Anf.mkVarV pos) $ getStateVariableX "anfReading" v 
       _ -> return $ Anf.mkExpV unit_value

  -- Get the body function's effect and return type.  Mask out the effect
  -- of reading the parameter variable.
  let effect_type = mask_effect_on addr_var $ Anf.procEffectType body_fn
      return_type = Anf.procReturnType body_fn

  -- Create a "reading" expression
  let reading = Anf.mkConV pos $ Anf.anfBuiltin Anf.the_reading 
      stmt = Anf.mkCallAppS pos reading [ Anf.mkExpV effect_type
                                        , Anf.mkExpV return_type
                                        , Anf.mkExpV obj_type
                                        , Anf.mkVarV pos addr_var
                                        , Anf.mkLamV body_fn
                                        , body_param
                                        ]
             
  -- This statement writes to the state variable
  case fexpReturn body of
    VariableReturn _ v -> defineStateVariable v
    _ -> return ()

  return stmt
  where
    -- Remove any effect affecting the given address variable.
    -- We assume the effect is a composition of atomic effects on addresses.
    mask_effect_on addr eff =
      case eff
      of Gluon.AppE { Gluon.expOper = Gluon.ConE {Gluon.expCon = con}
                    , Gluon.expArgs = args}
           | con `Gluon.isBuiltin` Gluon.the_SconjE ->
               -- Recurse on sub-effects
               case args
               of [l, r] ->
                    let l' = mask_effect_on addr l
                        r' = mask_effect_on addr r
                    in Gluon.Core.Builtins.Effect.sconj l' r'
               
           | con `Gluon.isBuiltin` Gluon.the_AtE ->
               -- Determine whether this effect is masked out
               case args
               of [obj_type, addr_type] ->
                    case addr_type
                    of Gluon.VarE {Gluon.expVar = this_addr}
                         | addr == this_addr ->
                             -- Mask out this effect
                             Gluon.Core.Builtins.Effect.empty
                         | otherwise ->
                             -- Leave it unchanged
                             eff
                             
                       -- Other effect types should not show up
                       _ -> internalError "anfReading: Unexpected effect"

         Gluon.ConE {Gluon.expCon = con}
           | con `Gluon.isBuiltin` Gluon.the_EmpE ->
               -- The empty effect is unchanged
               eff

         -- Other effect types should not show up
         _ -> internalError "anfReading: Unexpected effect"

    -- We don't need any extra parameters in the body function
    no_extra_parameters :: forall a. ([RBinder ()] -> Maybe RType -> ToAnf a)
                        -> ToAnf a
    no_extra_parameters f = f [] Nothing

    unit_value = Gluon.TupE (Gluon.mkSynInfo pos ObjectLevel) Gluon.Nil

-- | Create and use a local variable
-- FIXME: This function isn't complete
anfLocal :: SourcePos -> RType -> FlatReturn -> Var -> Stmt
         -> ToAnf Anf.RStm 
anfLocal pos ty return_info var body = do
  -- The given type is the type of the local object
  let obj_type = ty

  -- Turn the body into a lambda function
  body_fn <- anfStmtToProc add_local_object body
    
  -- Get the body function's effect and return type
  let effect_type = Anf.procEffectType body_fn
      return_type = Anf.procReturnType body_fn

  -- Create the new statement
  let local = Anf.mkConV pos $ Anf.anfBuiltin Anf.the_local
      stmt = Anf.mkCallAppS pos local [ Anf.mkExpV effect_type
                                      , Anf.mkExpV return_type
                                      , Anf.mkExpV obj_type
                                      , Anf.mkLamV body_fn
                                      ]
    
  return stmt
  where
    -- Pass the local object as an extra parameter in the body function.
    -- Also return it.
    add_local_object :: forall a. ([RBinder ()] -> Maybe RType -> ToAnf a)
                     -> ToAnf a
    add_local_object f =
      -- The local object is defined here
      withReferenceVariable var ty $ withStateVariable var $ do
        -- Create parameters for the local variable
        (local_addr, local_ptr, local_st) <- getWriteReferenceVariables var
        input_st_type <- getUndefStateType var
        let params = [ Binder local_addr addressType ()
                     , Binder local_ptr (pointerType $ Gluon.mkInternalVarE local_addr) ()
                     , Binder local_st input_st_type ()
                     ]

        -- Create the return type
        output_st_type <- getStateType var
        let return_type = Just output_st_type
        
        x <- f params return_type

        -- Consume the local state (it's returned)
        consumeStateVariable var

        return x

-- | Help transform a statement to a procedure.  This function masks linear
-- variables out of the evaluation context.  The linear variable modified by 
-- the statement (if any) is replaced in the context.
anfGetStmtReturnParameter :: Stmt
                          -> (Maybe (Var, RBinder (), RType) ->
                              ToAnf (Anf.Proc Rec))
                          -> ToAnf (Anf.Proc Rec)
anfGetStmtReturnParameter stm k = hideState $
  -- No state variables are accessible.  New state variables are created
  -- for the state that is explicitly passed to the function.
  case linear_variable
  of Nothing -> k Nothing
     Just v -> withStateVariable v $ do
       -- Create binder and return type of this variable
       param_type <- getUndefStateType v
       input_state_var <- getStateVariableX "anfGetStmtReturnParameter" v
       let binder = Binder input_state_var param_type ()
       
       return_type <- getStateType v

       -- Run a computation too create a procedure
       x <- k (Just (v, binder, return_type))
       
       -- The local variable is no longer in use
       consumeStateVariable v
       return x
  where
    -- Check the return value to determine what linear variables are used
    -- by this statement
    linear_variable =
      case fexpReturn stm
      of VariableReturn _ v -> Just v
         ValueReturn _ -> Nothing
         ClosureReturn _ _ -> Nothing

-- | Convert an ANF statement to a procedure.
--
-- The procedure takes either the unit value or a state object as a 
-- parameter.  It returns either a return value or a state object.  Pure
-- variable inputs are referenced directly.
anfStmtToProc :: (forall a. ([RBinder ()] -> Maybe RType -> ToAnf a) -> ToAnf a)
              -> Stmt
              -> ToAnf (Anf.Proc Rec)
anfStmtToProc initialize_params stm =
  -- Set up the context for a new procedure; set up the return state
  anfGetStmtReturnParameter stm $ \return_state ->
  -- Set up any other context we need
  initialize_params $ \ext_params ext_return_type ->
  -- Create the procedure
  make_proc return_state ext_params ext_return_type
  where
    -- Create a procedure that returns by value
    make_proc Nothing ext_params ext_return_type = do
      -- Create a dummy parameter variable
      v_id <- fresh
      let param_var = Gluon.mkAnonymousVariable v_id ObjectLevel
          dummy_param = Binder param_var unit_type ()

      -- Get effect type
      effect_type <- anfEffectType $ fexpEffect stm
      
      -- Return the unit type.  If a return type is given, return it instead
      let return_type = case ext_return_type
                        of Nothing -> unit_type
                           Just ty -> ty
      
      -- Create body
      body <- anfStmt stm
      
      -- Return the new procedure
      return $! Anf.Proc { Anf.procInfo = Gluon.mkSynInfo pos ObjectLevel
                         , Anf.procParams = ext_params ++ [dummy_param]
                         , Anf.procReturnType = return_type
                         , Anf.procEffectType = effect_type
                         , Anf.procBody = body
                         }

    -- Create a procedure that returns by reference 
    make_proc (Just (_, param, rt)) ext_params ext_return_type = do
      -- Get effect type
      effect_type <- anfEffectType $ fexpEffect stm
      
      -- Return the state.  If other return types are given, return them also
      let return_type = case ext_return_type
                        of Nothing -> rt
                           Just ty -> pair_type ty rt
      -- Create body
      body <- anfStmt stm
  
      -- Return the new procedure
      return $! Anf.Proc { Anf.procInfo = Gluon.mkSynInfo pos ObjectLevel
                         , Anf.procParams = ext_params ++ [param]
                         , Anf.procReturnType = return_type
                         , Anf.procEffectType = effect_type
                         , Anf.procBody = body
                         }

    pos = fexpSourcePos stm
    
    unit_type = Gluon.TupTyE (Gluon.mkSynInfo pos TypeLevel) Gluon.Unit
    pair_type t1 t2 =
      Gluon.TupTyE (Gluon.mkSynInfo pos TypeLevel) $
      Binder' Nothing t1 () Gluon.:*: Binder' Nothing t2 () Gluon.:*: Gluon.Unit

anfAlternative :: FlatValAlt -> ToAnf (Anf.Alt Rec)
anfAlternative (FlatValAlt con ty_args params body) = do
  anfBindParameters Nothing params $ \params' -> do
    body' <- anfStmt body
    return $ Anf.Alt con params' body'

-- | Convert a pass-by-reference case statement to ANF.
-- It is converted to a call to an elimination function.
anfCaseRef :: SourcePos -> Var -> RType -> [FlatRefAlt] -> ToAnf Anf.RStm
anfCaseRef pos scrutinee_var scrutinee_type alts = do
  -- Process all case alternatives using the same starting state.
  -- They should not change the state.
  (alternatives, _) <-
    let keep_state_consistent initial_state ss =
          -- All states must match
          case anfStateMapDifference $ map anfStateMap ss
          of (common, uniques)
               | all Map.null uniques -> (ToAnfState common, ())
               | otherwise -> internalError "anfCaseRef: Inconsistent state"
    in anfParallel keep_state_consistent $ map (anfRefAlternative pos) alts

  -- Dispatch based on the data type that's being inspected
  scrutinee_type' <- liftPureToAnf $ evalHead' scrutinee_type
  return $! case Gluon.unpackRenamedWhnfAppE scrutinee_type'
            of Just (con, args)
                 | con `isPyonBuiltin` the_bool ->
                   build_bool_case args alternatives
                 | con `isPyonBuiltin` the_PassConv ->
                   build_PassConv_case args alternatives
                 | Just tuple_size <- whichPyonTupleTypeCon con ->
                   build_tuple_case tuple_size args alternatives
                 | otherwise -> unrecognized_constructor con
               _ -> internalError $ "anfCaseRef: Unrecognized data type"
  where
    -- Get the return type from one of the alternatives
    return_type = refAltReturnType $ head alts

    unrecognized_constructor con =
      let name = showLabel (Gluon.conName con)
      in internalError $ 
         "anfCaseRef: Unrecognized data type with constructor " ++ name

    lookupCon con_selector alternatives =
      case lookup (pyonBuiltin con_selector) alternatives
      of Just x -> x
         Nothing -> internalError "anfCaseRef: Missing case alternative"

    build_bool_case args alternatives =
      let eliminator = Anf.mkInternalConV $ Anf.anfBuiltin Anf.the_elim_bool
          true_case = lookupCon the_True alternatives
          false_case = lookupCon the_False alternatives
      in Anf.mkCallAppS pos eliminator [ Anf.mkExpV return_type
                                       , Anf.mkLamV true_case
                                       , Anf.mkLamV false_case
                                       ]
    
    build_PassConv_case args alternatives =
      internalError "build_PassConv_case: not implemented"

    build_tuple_case size args alternatives =
      let eliminator =
            case size
            of 2 -> Anf.mkInternalConV $ Anf.anfBuiltin Anf.the_elim_PyonTuple2
          
          -- There is only one pattern to match against
          body = lookupCon (const $ getPyonTupleCon' size) alternatives
          
          -- Pass all type parameters to the eliminator
          type_args = map substFully args
          
          elim_args = map Anf.mkExpV (return_type : type_args) ++ [Anf.mkLamV body]
      in Anf.mkCallAppS pos eliminator elim_args

-- | Convert a by-reference alternative to a function.  The function arguments
-- are the parameters to the alternative.
anfRefAlternative :: SourcePos -> FlatRefAlt -> ToAnf (Con, Anf.Proc Rec)
anfRefAlternative pos (FlatRefAlt con _ params eff ret ret_ty body) = do
  proc <- anfStmtToProc alternative_parameters body
  return (con, proc)
  where
    return_value_type =
      case ret
      of ValueReturn ty -> Just ty
         ClosureReturn ty _ -> Just ty
         VariableReturn _ _ -> Nothing

    alternative_parameters k =
      -- Make each object field be a function parameter.
      anfBindParameters Nothing params $ \anf_params ->
        -- If returning by value, then indicate so
        k anf_params return_value_type
  {-do
  let function = FlatFun { ffunInfo = Gluon.mkSynInfo pos ObjectLevel
                         , ffunParams = params
                         , ffunReturn = ret
                         , ffunEffect = eff
                         , ffunReturnType = ret_ty
                         , ffunBody = body
                         }
  proc <- anfProc function
  return (con, proc) -}

anfStoreValue :: SourcePos -> RType -> Var -> Value -> ToAnf Anf.RStm
anfStoreValue pos ty dst val = do
  -- Storing a value will update the destination variable
  (dst_addr, dst_ptr, dst_st) <- getWriteReferenceVariables dst
  
  -- Generate a function call for the store
  stm <- create_store_statement dst_addr dst_ptr dst_st
  
  -- The output is now defined
  defineStateVariable dst
  
  return stm
  where
    create_store_statement dst_addr dst_ptr dst_st =
      case ty
      of Gluon.ConE {Gluon.expCon = c}
           | c `Gluon.isBuiltin` Gluon.the_Int ->
               case val
               of LitV (IntL n) ->
                    let literal = Gluon.mkLitE pos (Gluon.IntL n)
                        oper = Anf.anfBuiltin Anf.the_store_int
                    in store_literal oper literal
           | c `Gluon.isBuiltin` Gluon.the_Float ->
               case val
               of LitV (FloatL d) ->
                    let literal = Gluon.mkLitE pos (Gluon.FloatL d)
                        oper = Anf.anfBuiltin Anf.the_store_float
                    in store_literal oper literal
           | c `isPyonBuiltin` the_bool ->
               case val
               of LitV (BoolL b) ->
                    let literal =
                          Gluon.mkConE pos $ if b
                                             then pyonBuiltin the_True
                                             else pyonBuiltin the_False
                        oper = Anf.anfBuiltin Anf.the_store_bool
                    in store_literal oper literal
           | c `isPyonBuiltin` the_NoneType ->
                 case val
                 of LitV NoneL ->
                      let literal =
                            Gluon.mkConE pos $ pyonBuiltin the_None
                          oper = Anf.anfBuiltin Anf.the_store_NoneType
                      in store_literal oper literal
         _ -> internalError "Cannot store literal value"
        where
          -- Use function 'oper' to store literal value 'lit'
          store_literal oper lit =
            let oper_anf = Anf.mkConV pos oper
                args = [ Anf.mkVarV pos dst_addr
                       , Anf.mkVarV pos dst_ptr
                       , Anf.mkExpV lit
                       , Anf.mkVarV pos dst_st]
            in return $ Anf.mkCallAppS pos oper_anf args

anfCopyValue :: SourcePos -> RType -> Var -> Var -> ToAnf Anf.RStm
anfCopyValue pos ty dst src = do
  -- Look up all parameters
  pc <- getAnfPassConv ty
  (src_addr, src_ptr) <- getReadReferenceVariables src
  (dst_addr, dst_ptr, dst_st) <- getWriteReferenceVariables dst
  defineStateVariable dst

  let con  = Anf.mkConV pos $ Anf.anfBuiltin Anf.the_copy
      args = [Anf.mkExpV ty, pc,
              Anf.mkVarV pos src_addr, Anf.mkVarV pos dst_addr,
              Anf.mkVarV pos src_ptr, Anf.mkVarV pos dst_ptr,
              Anf.mkVarV pos dst_st]
  return $ Anf.mkCallAppS pos con args

anfModule :: [[FlatDef]] -> ToAnf (Anf.Module Rec)
anfModule defss = liftM Anf.Module $ top_level_group defss
  where
    top_level_group (defs:defss) =
      liftM (uncurry (:)) $ anfDefGroup defs $ top_level_group defss
    top_level_group [] = return []