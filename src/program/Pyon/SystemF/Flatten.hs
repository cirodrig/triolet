
{-# LANGUAGE ViewPatterns, FlexibleInstances, RelaxedPolyRec #-}
module Pyon.SystemF.Flatten(flatten)
where

import Control.Monad
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace 
import Text.PrettyPrint.HughesPJ hiding(Mode)

import Gluon.Common.Label
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
import qualified Gluon.Core as Gluon
import Gluon.Eval.Environment
import Gluon.Eval.Eval
import Gluon.Eval.Typecheck
import Pyon.Globals
import Pyon.SystemF.Builtins
import Pyon.SystemF.Syntax
import Pyon.SystemF.Typecheck
import Pyon.SystemF.Print

withMany :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c
withMany f xs k = go xs k
  where
    go (x:xs) k = f x $ \y -> go xs $ \ys -> k (y:ys)
    go []     k = k []

type TExp = SFRecExp (Typed Rec)
type TType = RecType (Typed Rec)

data Mode = ByVal | ByRef | ByClo
data Component = Value | FunRef | Address | Pointer | State

data AtomicEffect = ReadEff | WriteEff
type Effect = Map.Map VarID AtomicEffect

data FlatArgument =
  ValueArgument !Value | VariableArgument !Var

data FlatReturn =
  ValueReturn | VariableReturn !Var

data Value =
    VarV Var !Component
  | ConV Con !Component
  | LitV Lit
  | TypeV RType
  | FunV FlatFun
  | AppV Value [Value]

data Stmt =
    ValueS
    { fexpInfo :: ExpInfo
    , fexpValue :: Value
    }
    -- | Store a value into a variable.  This must be the RHS of a 
    -- LetS.
  | StoreValueS
    { fexpInfo :: ExpInfo
    , fexpVar :: Var
    , fexpValue :: Value
    }
  | CallS
    { fexpInfo :: ExpInfo
    , fexpOper :: Value
    , fexpArgs :: [Value]
    }
    -- | Perform an action and store its result in a variable.
    -- The action may have the side effect of writing some variables.
    -- The written variables are listed in 'fexpUpdates'.  These variables
    -- will become returned state variables.
  | LetS
    { fexpInfo :: ExpInfo
    , fexpBinder :: RBinder Component
    , fexpUpdates :: [RBinder ()]
    , fexpRhs :: Stmt
    , fexpBody :: Stmt
    }
  | ThenS
    { fexpInfo :: ExpInfo
    , fexpUpdates :: [RBinder ()]
    , fexpRhs :: Stmt
    , fexpBody :: Stmt
    }
  | LetrecS
    { fexpInfo :: ExpInfo
    , fexpDefs :: [FlatDef]
    , fexpBody :: Stmt
    }
    -- | Case-of-value
  | CaseValS
    { fexpInfo :: ExpInfo
    , fexpScrutinee :: Value
    , fexpValAlts :: [FlatValAlt]
    }
    -- | Case-of-reference
  | CaseRefS
    { fexpInfo :: ExpInfo
    , fexpScrutineeVar :: Var
    , fexpRefAlts :: [FlatRefAlt]
    }
    -- | Put a writable object into readable mode.  This is inserted by
    -- effect inference.
  | ReadingS
    { fexpInfo :: ExpInfo
    , fexpScrutinee :: Value
    , fexpBody :: Stmt
    }
    -- | Allocate some memory that is alive only during the body of this
    -- expression.  This is inserted by effect inference.
  | LocalS
    { fexpInfo :: ExpInfo
    , fexpVar :: Var
    , fexpBody :: Stmt
    }
    -- | Copy from one variable to another.  This is inserted by effect
    -- inference
  | CopyS
    { fexpInfo :: ExpInfo
    , fexpSrc :: Var
    , fexpDst :: Var
    }

data FlatValAlt =
  FlatValAlt Con [Value] [RBinder Component] Stmt

data FlatRefAlt =
  FlatRefAlt Con [Value] [RBinder Component] Effect Stmt

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

fromTypedFun :: Fun (Typed Rec) -> RFun
fromTypedFun (TypedSFFun (TypeAnn _ (Fun info ty_params params return_type body))) =
  Fun info (map from_ty_param ty_params) (map from_param params) (fromTypedType return_type) (fromTypedExp body)
  where
    from_ty_param (TyPat v ty) = TyPat v (fromTypedType ty)
    from_param (VarP v ty) = VarP v (fromTypedType ty)

fromTypedType :: TType -> RType
fromTypedType (TypedSFType t) = t

expectValueArgument :: FlatArgument -> Value
expectValueArgument (ValueArgument v) = v
expectValueArgument _ = internalError "Expecting value argument"

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
  case statement
  of ValueS {fexpValue = val} ->
       pprValue val
     StoreValueS {fexpVar = v, fexpValue = val} ->
       text "set" <+> pprVar v <+> text "<-" <+> pprValue val
     CallS {fexpOper = op, fexpArgs = args} ->
       pprValue op <+> fsep (map pprValue args)
     LetS {} -> pprStmts statement
     ThenS {} -> pprStmts statement
     LetrecS {} -> pprStmts statement
     ReadingS {} -> pprStmts statement
     LocalS {} -> pprStmts statement
     CaseValS {fexpScrutinee = v, fexpValAlts = alts} ->
       text "case" <+> pprValue v $$
       text "of" <+> pprBlock (map pprAlt alts)
     CaseRefS {fexpScrutineeVar = v, fexpRefAlts = alts} ->
       text "case" <+> pprVar v $$
       text "of" <+> pprBlock (map pprRefAlt alts)
     CopyS {fexpSrc = src, fexpDst = dst} ->
       text "copy" <+> pprVar dst <+> text "<-" <+> pprVar src

pprAlt :: FlatValAlt -> Doc
pprAlt (FlatValAlt c ty_args params body) =
  let con_doc = text (showLabel $ Gluon.conName c)
      ty_docs = map pprValue ty_args
      param_docs = map pprParam params
      body_doc = pprStmt body
  in hang (con_doc <+> sep (ty_docs ++ param_docs) <> text ".") 4 body_doc

pprRefAlt :: FlatRefAlt -> Doc
pprRefAlt (FlatRefAlt c ty_args params eff body) =
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
         ThenS { fexpRhs = rhs
               , fexpBody = body} ->
           pprStmt rhs : statement_sequence body
         LetrecS { fexpDefs = defs
                 , fexpBody = body} ->
           let defs_doc = map pprFlatDef defs
               body_doc = statement_sequence body
           in (text "letrec" $$ nest 2 (pprBlock defs_doc)) : body_doc
         ReadingS {fexpScrutinee = val, fexpBody = body} ->
           (text "reading" <+> pprValue val) : statement_sequence body
         LocalS {fexpVar = v, fexpBody = body} ->
           (text "local" <+> pprVar v) : statement_sequence body
         _ -> [pprStmt statement]

pprFlatDef :: FlatDef -> Doc
pprFlatDef (FlatDef v f) = hang (pprVar v <+> text "=") 4 (pprFlatFun f)

pprFlatFun :: FlatFun -> Doc
pprFlatFun function =
  let params = map pprParam $ ffunParams function
      rv = case ffunReturn function
           of ValueReturn -> parens $ Gluon.pprExp (ffunReturnType function)
              VariableReturn v -> parens $ pprVar v `pprDotted` State <+> text ":" <+> Gluon.pprExp (ffunReturnType function)
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
  LocalS (Gluon.mkSynInfo pos ObjectLevel) v stmt

-- | Perform two actions in sequence
eval :: SourcePos -> Stmt -> StmtContext
eval pos s1 s2 =
  ThenS (Gluon.mkSynInfo pos ObjectLevel) [] s1 s2

-- | Assign a value to a local variable over the scope of a statement
assignTemporaryValue :: SourcePos -> Var -> RType -> Stmt -> StmtContext
assignTemporaryValue pos v ty stmt body =
  LetS (Gluon.mkSynInfo pos ObjectLevel) (Binder v ty Value) [] stmt body

assignState :: SourcePos -> Var -> RType -> Stmt -> StmtContext
assignState pos v ty stmt body =
  LetS (Gluon.mkSynInfo pos ObjectLevel) (Binder v ty State) [] stmt body

assignTemporaryFunction :: SourcePos -> Var -> RType -> Stmt -> StmtContext
assignTemporaryFunction pos v ty stmt body =
  LetS (Gluon.mkSynInfo pos ObjectLevel) (Binder v ty FunRef) [] stmt body

type F = PureTC

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
    _ -> traceShow (Gluon.pprExp $ fromWhnf $ Gluon.substFullyUnderWhnf ty) $ internalError "lookupPassConv"
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
    addr_parameter (VariableArgument v) = Just (VarV v Address)
    
    value_parameter (ValueArgument fv) = Just fv
    value_parameter (VariableArgument v) = Just (VarV v Pointer)
    
    (return_addr_parameter, return_ptr_parameter, return_state_parameter) =
      case ret
      of ValueReturn -> (Nothing, Nothing, Nothing)
         VariableReturn v -> (Just (VarV v Address),
                              Just (VarV v Pointer),
                              Just (VarV v State))

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
    of ByVal -> return (ValueReturn, Nothing, Nothing, Nothing)
       ByRef -> do rv <- newAnonymousVariable
                   return (VariableReturn rv,
                           Just (Binder rv return_type Address),
                           Just (Binder rv return_type Pointer),
                           Just (Binder rv return_type State))
       ByClo -> return (ValueReturn, Nothing, Nothing, Nothing)

  -- Construct parameter list
  let flat_params =
        map convert_ty_param ty_params ++
        mapMaybe param_address (zip params param_modes) ++
        maybeToList return_address ++
        mapMaybe param_value (zip params param_modes) ++
        maybeToList return_pointer ++
        maybeToList return_state
        
  -- Calculate side effect
  let effect1 = Map.fromList $ catMaybes $
                zipWith param_effect params param_modes
      effect = case return_mode
               of ByVal -> effect1
                  ByRef -> case return_var
                           of VariableReturn rv ->
                                Map.insert (varID rv) WriteEff effect1
                  ByClo -> effect1

  return (flat_params, effect, return_mode, return_var)
  where
    convert_ty_param (TyPat v ty) = Binder v (fromTypedType ty) Value
    
    choose_param_mode (VarP v ty) = chooseMode (fromTypedType ty)
    choose_param_mode _ = internalError "not a variable parameter"

    param_address (VarP v ty, ByVal) = Nothing
    param_address (VarP v ty, ByRef) = Just (Binder v (fromTypedType ty) Address)
    param_address (VarP v ty, ByClo) = Nothing
    param_address (_, _) = internalError "not a variable parameter"

    param_value (VarP v ty, ByVal) = Just (Binder v (fromTypedType ty) Value)
    param_value (VarP v ty, ByRef) = Just (Binder v (fromTypedType ty) Pointer)
    param_value (VarP v ty, ByClo) = Just (Binder v (fromTypedType ty) FunRef)
    param_value (_, _) = internalError "not a variable parameter"
    
    param_effect (VarP v ty) ByVal = Nothing
    param_effect (VarP v ty) ByRef = Just (varID v, ReadEff)
    param_effect (VarP v ty) ByClo = Nothing
    param_effect _ _ = internalError "not a variable parameter"

-- | Get the parameter and result types of a case alternative
getAltParameterTypes :: Alt (Typed Rec) -> F ([Gluon.WRExp], Gluon.WRExp)
getAltParameterTypes (Alt { altConstructor = con
                          , altTyArgs = ty_args
                          , altParams = param_vars
                          }) = do
  con_type <- getConstructorType con
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
  param_modes <- traceShow (text "param_types" <+> (vcat $ map (Gluon.pprExp . fromWhnf) param_types)) $ mapM (chooseMode . fromWhnf) param_types
  
  -- Construct parameter binders
  let parameters =
        zipWith3 makeParamBinder (altParams alt) param_types param_modes
      ty_args = map (TypeV . fromTypedType) $ altTyArgs alt
  return (altConstructor alt, ty_args, parameters)
  where
    -- Only pass-by-value parameters are permitted
    makeParamBinder var ty ByVal = Binder var (fromWhnf ty) Value 
    makeParamBinder var ty ByClo = Binder var (fromWhnf ty) FunRef
    makeParamBinder _ ty _ = traceShow (Gluon.pprExp $ fromWhnf ty) $ internalError "buildValueCaseParameters"

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
  let addr_parameters =
        catMaybes $
        zipWith3 make_addr_param (altParams alt) param_types param_modes
      value_parameters =
        catMaybes $
        zipWith3 make_value_param (altParams alt) param_types param_modes
      effects =
        Map.fromList $
        catMaybes $
        zipWith3 make_effect (altParams alt) param_types param_modes
      parameters = addr_parameters ++ value_parameters
      ty_args = map (TypeV . fromTypedType) $ altTyArgs alt
  return (altConstructor alt, ty_args, parameters, effects)
  where
    make_addr_param var ty ByRef = Just $ Binder var (fromWhnf ty) Address 
    make_addr_param var ty ByVal = Nothing
    make_addr_param _ _ _ = internalError "buildRefCaseParameters"

    make_value_param var ty ByRef = Just $ Binder var (fromWhnf ty) Pointer
    make_value_param var ty ByVal = Just $ Binder var (fromWhnf ty) Value
    make_value_param _ _ _ = internalError "buildRefCaseParameters"

    make_effect _ _ ByVal = Nothing
    make_effect var ty ByRef = Just (varID var, ReadEff)

unpackTypeApplication :: TExp -> (TExp, [TType])
unpackTypeApplication e = unpack [] e
  where
    unpack types (discardExpType -> TyAppE {expOper = op, expTyArg = ty}) =
      unpack (ty : types) op
    unpack types e = (e, types)

-------------------------------------------------------------------------------

flattenValueToStmt :: ExpInfo -> F (StmtContext, Value) -> F Stmt
flattenValueToStmt inf m = do
  (context, value) <- m
  return (context $ ValueS inf value)

-- | Make the value of an expression available over some local scope
withFlattenedExp :: StmtExtensible a =>
                    TExp -> (FlatArgument -> F a) -> F a
withFlattenedExp typed_expression@(TypedSFExp (TypeAnn ty _)) k = do
  mode <- chooseMode $ fromWhnf ty
  case mode of
    ByVal -> do
      (ctx, val) <- flattenExpValue typed_expression
      result <- k $ ValueArgument val
      return $ addContext ctx result
    ByClo -> do
      (ctx, val) <- flattenExpValue typed_expression
      result <- k $ ValueArgument val
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
  withFlattenedExps (fromMaybe [] margs) $ \arguments -> do
    -- Get the function call parameters
    let params = buildCallArguments arguments ret
        op = expectValueArgument real_op_argument
    
    -- Create the function call statement
    return $ CallS inf op params
  where
    -- Get the real operator and its type arguments 
    (poly_op, ty_args) = unpackTypeApplication mono_op

-- | Flatten a \'let\' expression, making its bound variable available locally
flattenLet :: StmtExtensible a =>
              ExpInfo -> Pat (Typed Rec) -> TExp -> a -> F a
flattenLet inf (VarP v (fromTypedType -> ty)) rhs body = do
  -- Decide the variable's parameter passing mode
  mode <- chooseMode ty

  -- Assign the variable in the body's context
  assignment <-
    case mode
    of ByVal -> flattenExpWriteValue inf v rhs
       ByRef -> return . eval (getSourcePos inf) =<<
                flattenExpWriteReference v rhs
  
  return $ addContext assignment body

-- | Flatten a \'letrec\' expression
flattenLetrec :: StmtExtensible a =>
                 ExpInfo -> [Def (Typed Rec)] -> a -> F a
flattenLetrec inf defs body = do
  defs' <- mapM flattenDef defs
  let context body = LetrecS inf defs' body
  return $ addContext context body

-- | Flatten a \'case\' expression to a statement
flattenCase :: (TExp -> F Stmt) -> ExpInfo -> TExp -> [Alt (Typed Rec)]
            -> F Stmt 
flattenCase flattenBranch inf scrutinee alts =
  withFlattenedExp scrutinee flatten
  where
    scrutinee_type = case scrutinee of TypedSFExp (TypeAnn ty _) -> fromWhnf ty

    -- Create a flattened case statement with the given scrutinee
    flatten (ValueArgument scrutinee_val) = do
      -- Flatten all case alternatives
      flat_alts <- mapM (flattenValAlt flattenBranch scrutinee_type) alts
      return $ CaseValS inf scrutinee_val flat_alts

    flatten (VariableArgument scrutinee_var) = do
      -- Flatten all case alternatives
      flat_alts <- mapM (flattenRefAlt flattenBranch scrutinee_type) alts
      return $ CaseRefS inf scrutinee_var flat_alts
      
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
      return $ FlatRefAlt con ty_args params eff body

-- Expression flattening functions

-- | Flatten an expression whose result is a value.  Assign the value to
-- the given return variable.
flattenExpWriteValue :: ExpInfo -> Var -> TExp -> F StmtContext
flattenExpWriteValue inf dest texp@(TypedSFExp (TypeAnn ty expression)) =
  case expression
  of VarE {expVar = v} -> returnValue $ VarV v Value
     ConE {expCon = c} -> returnValue $ ConV c Value
     LitE {expLit = l} -> returnValue $ LitV l
     TyAppE {expInfo = inf, expOper = op} -> do 
       stmt <- flattenCall inf ValueReturn texp Nothing
       return $ assignTemporaryValue pos dest (fromWhnf ty) stmt
     CallE {expInfo = inf, expOper = op, expArgs = args} -> do
       stmt <- flattenCall inf ValueReturn op (Just args)
       return $ assignTemporaryValue pos dest (fromWhnf ty) stmt
     FunE {expInfo = inf, expFun = f} -> do
       f' <- flattenFun f
       returnValue $ FunV f'
     LetE { expInfo = inf
          , expBinder = binder
          , expValue = rhs
          , expBody = body} ->
       -- Assign the bound variable, then write the destination value in the
       -- body expression
       flattenLet inf binder rhs =<< flattenExpWriteValue inf dest body
     LetrecE {expInfo = inf, expDefs = defs, expBody = body} ->
       flattenLetrec inf defs =<< flattenExpWriteValue inf dest body
     CaseE { expInfo = inf
           , expScrutinee = scrutinee
           , expAlternatives = alts} -> do
       stmt <- flattenCase (flattenValueToStmt inf . flattenExpValue) inf scrutinee alts
       return $ assignTemporaryValue pos dest (fromWhnf ty) stmt
  where
    pos = getSourcePos inf
    returnValue val =
      return $ assignTemporaryValue pos dest (fromWhnf ty) (ValueS inf val)

flattenExpValue :: TExp -> F (StmtContext, Value)
flattenExpValue typed_expression@(TypedSFExp (TypeAnn ty expression)) =
  case expression
  of VarE {expVar = v} -> returnValue $ VarV v Value
     ConE {expCon = c} -> returnValue $ ConV c Value
     LitE {expLit = l} -> returnValue $ LitV l
     TyAppE {expInfo = inf} -> do
       -- Create a temporary variable to hold the result
       tmp_var <- newAnonymousVariable
       
       stmt <- flattenCall inf ValueReturn typed_expression Nothing
       
       -- Bind the call's result to a variable
       let context = assignTemporaryValue pos tmp_var (fromWhnf ty) stmt
           
       return (context, VarV tmp_var Value)
     CallE {expInfo = inf, expOper = op, expArgs = args} -> do
       -- Create a temporary variable to hold the result
       tmp_var <- newAnonymousVariable
       
       -- Create the function call
       stmt <- flattenCall inf ValueReturn op (Just args)
       
       -- Bind the call's result to a variable
       let context = assignTemporaryValue pos tmp_var (fromWhnf ty) stmt
           
       return (context, VarV tmp_var Value)
     FunE {expInfo = inf, expFun = f} -> do
       f' <- flattenFun f
       returnValue $ FunV f'
     LetE { expInfo = inf
          , expBinder = binder
          , expValue = rhs
          , expBody = body} ->
       flattenLet inf binder rhs =<< flattenExpValue body
     LetrecE {expInfo = inf, expDefs = defs, expBody = body} ->
       flattenLetrec inf defs =<< flattenExpValue body
     CaseE { expInfo = inf
           , expScrutinee = scrutinee
           , expAlternatives = alts} -> do
       stmt <- flattenCase (flattenValueToStmt inf . flattenExpValue) inf scrutinee alts
       
       -- Assign the value to a temporary variable
       tmp_var <- newAnonymousVariable
       let context = assignTemporaryValue pos tmp_var (fromWhnf ty) stmt
       return (context, VarV tmp_var Value)
  where
    pos = getSourcePos expression
    returnValue v = return (idContext, v)

-- | Flatten an expression whose value will be read by reference.
-- The variable representing the expression's storage will be returned. 
flattenExpReference :: TExp -> F (StmtContext, Var)
flattenExpReference texp@(TypedSFExp (TypeAnn ty expression)) =
  case expression
  of VarE {expVar = v} -> return (idContext, v)
     ConE {expCon = c} -> do
       -- Allocate the constructor value in a local memory area
       tmp_var <- newAnonymousVariable
       let context = allocateLocalMemory pos tmp_var (fromWhnf ty)
       return (context, tmp_var)
     LitE {expLit = l} -> do
       -- Allocate the variable value in a local memory area
       tmp_var <- newAnonymousVariable
       let tmp_var_ty = fromWhnf ty
           context =
             allocateLocalMemory pos tmp_var tmp_var_ty .
             assignState pos tmp_var tmp_var_ty (StoreValueS (Gluon.mkSynInfo pos ObjectLevel) tmp_var (LitV l))
       return (context, tmp_var)
     TyAppE {expInfo = inf} -> do
       -- Create a temporary variable to hold the result
       tmp_var <- newAnonymousVariable
            
       -- Create a function call
       stmt <- flattenCall inf (VariableReturn tmp_var) texp Nothing

       -- Bind the call's result to a locally allocated variable
       let context body =
             allocateLocalMemory (getSourcePos expression) tmp_var (fromWhnf ty) $
             LetS inf (Binder tmp_var (fromWhnf ty) State) [] stmt body
       return (context, tmp_var)       
     CallE {expInfo = inf, expOper = op, expArgs = args} -> do
       -- Create a temporary variable to hold the result
       tmp_var <- newAnonymousVariable
            
       -- Create a function call
       stmt <- flattenCall inf (VariableReturn tmp_var) op (Just args)

       -- Bind the call's result to a locally allocated variable
       let context body =
             allocateLocalMemory (getSourcePos expression) tmp_var (fromWhnf ty) $
             LetS inf (Binder tmp_var (fromWhnf ty) State) [] stmt body
       return (context, tmp_var)
  where
    pos = getSourcePos expression

-- | Flatten an expression whose value will be written to the specified
-- variable.
flattenExpWriteReference :: Var -> TExp -> F Stmt
flattenExpWriteReference return_var texp@(TypedSFExp (TypeAnn ty expression)) =
  case expression
  of VarE {expInfo = inf, expVar = v} -> do
       -- Copy this variable to the destination
       pc <- getPassConv $ fromWhnf ty
       return $ CopyS inf v return_var
     ConE {expInfo = inf, expCon = c} ->
       return $ StoreValueS inf return_var (ConV c Value)
     LitE {expInfo = inf, expLit = l} ->
       return $ StoreValueS inf return_var (LitV l)
     TyAppE {expInfo = inf} ->
       flattenCall inf (VariableReturn return_var) texp Nothing
     CallE {expInfo = inf, expOper = op, expArgs = args} ->
       flattenCall inf (VariableReturn return_var) op (Just args)
     LetE { expInfo = inf
          , expBinder = binder
          , expValue = rhs
          , expBody = body} -> do
       flattenLet inf binder rhs =<< flattenExpWriteReference return_var body
     CaseE { expInfo = inf
           , expScrutinee = scrutinee
           , expAlternatives = alts} ->
       flattenCase (flattenExpWriteReference return_var) inf scrutinee alts

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
         (ctx, val) <- flattenExpValue (funBody function)
         let return_value =
               ValueS (expInfo $ discardExpType (funBody function)) val
         return $ ctx return_value
       ByRef ->
         case ret
         of VariableReturn v ->
              -- Flatten the expression,
              -- which writes the result as a side effect
              flattenExpWriteReference v (funBody function)
            _ -> internalError "flattenFun"
       ByClo -> do
         -- Flatten the expression and return its result value 
         (ctx, val) <- flattenExpValue (funBody function)
         let return_value =
               ValueS (expInfo $ discardExpType (funBody function)) val
         return $ ctx return_value

  return $ FlatFun { ffunInfo = funInfo function
                   , ffunParams = params
                   , ffunReturn = ret
                   , ffunReturnType = fromTypedType $ funReturnType function
                   , ffunEffect = eff
                   , ffunBody = body
                   }
  where
    -- Assume variables bound by one of the binders
    assumeValueParameters params m = foldr assumeValueParameter m params
    
    assumeValueParameter (Binder v ty Value) m = assumePure v ty m
    assumeValueParameter (Binder _ _ _)      m = m

flattenDef :: Def (Typed Rec) -> F FlatDef
flattenDef (Def v f) = do
  f' <- flattenFun f
  return $ FlatDef v f'

flattenModule :: Module (Typed Rec) -> F [[FlatDef]]
flattenModule (Module defss exports) = do
  defss' <- mapM (mapM flattenDef) defss
  return defss'

flatten :: RModule -> IO ()
flatten mod = do
  -- Get type information
  result1 <- typeCheckModule annotateTypes mod
  
  case result1 of
    Left errs -> fail "Type checking failed"
    Right tc_mod -> do
      result2 <- withTheVarIdentSupply $ \var_supply ->
        runPureTCIO var_supply $ flattenModule tc_mod
      case result2 of
        Left errs -> fail "Flattening failed"
        Right defss -> do print $ vcat $ map (vcat . map pprFlatDef) defss 
                          return ()
