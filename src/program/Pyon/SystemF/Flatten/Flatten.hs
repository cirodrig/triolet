{-# LANGUAGE ViewPatterns, FlexibleContexts, FlexibleInstances,
             RelaxedPolyRec, GeneralizedNewtypeDeriving, Rank2Types #-}
module Pyon.SystemF.Flatten.Flatten
       (flattenModule,
        chooseMode,
        isDictionaryTypeConstructor
       )
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

import Pyon.SystemF.Flatten.FlatData

type TExp = SFRecExp (Typed Rec)
type TType = RecType (Typed Rec)

discardExpType :: TExp -> SFExpOf Rec (Typed Rec)
discardExpType (TypedSFExp (TypeAnn _ e)) = e

fromTypedExp :: TExp -> RExp
fromTypedExp e = mapSFExp fromTypedExp fromTypedFun fromTypedType $
                 discardExpType e

unpackTypedExp :: TExp -> (RType, SFExpOf Rec (Typed Rec))
unpackTypedExp (TypedSFExp (TypeAnn ty e)) = (fromWhnf ty, e)

fromTypedTyPat :: TyPat (Typed Rec) -> TyPat Rec
fromTypedTyPat (TyPat v ty) = TyPat v (fromTypedType ty)

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

typePatternBinder :: TyPat Rec -> RBinder ()
typePatternBinder (TyPat v ty) = Binder v ty ()

patternBinder :: RPat -> RBinder ()
patternBinder (VarP v ty) = Binder v ty ()
patternBinder _ = internalError "Expecting a variable parameter"

expectClosureArgument :: FlatArgument -> (Value, FunctionEffect)
expectClosureArgument (ClosureArgument v e) = (v, e)
expectClosureArgument _ = internalError "Expecting closure argument"

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
  if fexpEffect stmt `affects` v
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
             | fexpEffect s2 `affects` write_var ->
                 locallyRead pos write_var write_ty s2
           _ -> s2
      effect1 = fexpEffect s1
      effect2 = fexpEffect s2'
      info = mkFlatInfo pos (fexpReturn s2') (effectUnion effect1 effect2)
  in EvalS info s1 s2'

-- | Change a writeable variable to a readable one over the scope of a
-- statement
locallyRead :: SourcePos -> Var -> RType -> StmtContext
locallyRead pos var ty stmt =
  let -- Do not propagate effects on this variable
      info = extendStmtInfo pos (maskEffect var) stmt
  in ReadingS info var ty stmt

-- | Assign a value to a local variable over the scope of a statement
assignTemporaryValue :: SourcePos -> Var -> RType -> DataMode -> Stmt
                     -> StmtContext
assignTemporaryValue pos v ty mode stmt body =
  let effect1 = fexpEffect stmt
      info = extendStmtInfo pos (effectUnion effect1) body
  in LetS info (Binder v ty mode) stmt body

-------------------------------------------------------------------------------
-- A monad that keeps track of types and function side effects

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

newAnonymousVariable :: F Var
newAnonymousVariable = Gluon.newAnonymousVariable ObjectLevel

-------------------------------------------------------------------------------

-- | Find a parameter-passing convention dictionary for this type variable
-- in the environment.  Throw an error if it can't be found. 
findVarPassConv :: Var -> F Value
findVarPassConv v = do
  result <- findM matchType =<< getPureTypes
  case result of
    Just (dict_var, _) -> return $ VarV dict_var IOVal
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

-- | Get an expression that computes this type's parameter-passing convention
getPassConv' :: RType -> F Value
getPassConv' ty = getPassConv $ verbatim ty

-- | Get this type's parameter-passing convention
getPassConv :: Gluon.SRExp -> F Value
getPassConv ty = do
  ty' <- evalHead ty
  case Gluon.unpackRenamedWhnfAppE ty' of
    Just (con, [])
      | con `Gluon.isBuiltin` Gluon.the_Int -> primitive the_passConv_Int
      | con `Gluon.isBuiltin` Gluon.the_Float -> primitive the_passConv_Float
      | con `isPyonBuiltin` the_bool -> primitive the_passConv_bool
      | con `isPyonBuiltin` the_Any -> primitive the_passConv_Any
    Just (con, [t1, t2])
      | con == getPyonTupleType' 2 -> do
          pc1 <- getPassConv t1
          pc2 <- getPassConv t2
          return $ AppV (ConV (getPyonTuplePassConv' 2) IOVal)
            [TypeV (substFully t1), TypeV (substFully t2), pc1, pc2]
    Nothing ->
      case fromWhnf ty' of
        Gluon.VarE {Gluon.expVar = v} -> findVarPassConv v
        _ -> internalError "getPassConv"
    _ -> internalError "getPassConv"
  where
    primitive pc =
      let con = pyonBuiltin pc
      in return $ ConV con IOVal

-- | Choose a parameter-passing mode for a data type.
-- Dictionary types inserted by type inference are passed by value.
-- Functions are passed as closures.
-- Other types are passed by reference.
chooseMode :: EvalMonad m => RType -> m TypeMode
chooseMode t
  | getLevel t == ObjectLevel = internalError "chooseMode"
  | getLevel t /= TypeLevel = return PassByVal
  | otherwise = do
      t' <- evalHead' t
      return $! case Gluon.unpackRenamedWhnfAppE t'
                of Just (con, _)
                     | isDictionaryTypeConstructor con -> PassByVal
                     | otherwise -> PassByRef
                   Nothing -> case substFullyUnder $ fromWhnf t'
                              of Gluon.FunE {} -> PassByClo
                                 _ -> PassByRef

-- | True if this is a type constructor for a constraint type.
-- Data of these types are always passed by value. 
isDictionaryTypeConstructor con =
  any (con `isPyonBuiltin`) [the_PassConv, the_EqDict, the_OrdDict,
                             the_TraversableDict, the_AdditiveDict,
                             the_VectorDict]

-- | Build the argument list for a function call
buildCallArguments :: [FlatArgument] -> FlatReturn -> [Value]
buildCallArguments args ret =
  map inp_parameter args ++ maybeToList (out_parameter ret)
  where
    inp_parameter (ValueArgument val) = val
    inp_parameter (ClosureArgument val _) = val
    inp_parameter (VariableArgument v) = VarV v InRef
    
    out_parameter (ValueReturn _) = Nothing
    out_parameter (ClosureReturn _ _) = Nothing
    out_parameter (VariableReturn _ v) = Just (VarV v OutRef)

-- | Set the parameter binder's mode based on its type
setParameterMode :: RBinder () -> F (RBinder DataMode)
setParameterMode (Binder v ty ()) = do
  mode <- chooseMode ty
  return $! Binder v ty $! parameterInMode mode

createReturnBinder :: RType
                   -> F (Maybe (RBinder DataMode), TypeMode, FlatReturn)
createReturnBinder return_type = do
  return_mode <- chooseMode return_type
  case return_mode of
    PassByVal -> do
      return (Nothing, PassByVal, ValueReturn return_type)
    PassByClo -> do
      return_effect <- functionTypeEffect return_type
      return (Nothing, PassByClo, ClosureReturn return_type return_effect)
    PassByRef -> do
      rv <- newAnonymousVariable
      return (Just (Binder rv return_type OutRef),
              PassByRef,
              VariableReturn return_type rv)

-- | Build the parameter list for a function
buildFunctionParameters :: [TyPat (Typed Rec)]
                        -> [Pat (Typed Rec)]
                        -> RType
                        -> F ([RBinder DataMode], Effect, FlatReturn)
buildFunctionParameters ty_params params return_type = do
  -- Determine parameter passing modes
  ty_params' <-
    mapM (setParameterMode . typePatternBinder . fromTypedTyPat) ty_params
  params' <- mapM (setParameterMode . patternBinder . fromTypedPat) params

  -- Determine return mode
  (return_binder, _, return_spec) <- createReturnBinder return_type
  
  -- Determine effect
  let effect = parameterEffects params'

  return (ty_params' ++ params' ++ maybeToList return_binder, effect, return_spec)

-- | Get the parameter and result types of a case alternative
getAltParameterTypes :: Alt (Typed Rec) -> PureTC ([Gluon.WRExp], Gluon.WRExp)
getAltParameterTypes (Alt { altConstructor = con
                          , altTyArgs = ty_args
                          }) = do
  con_type <- getConstructorType con
  compute_fotype con_type ty_args
  where
    -- Compute the first-order type of a data constructor, instantiated with 
    -- type arguments 'args'  Assume the application is well-typed.
    compute_fotype :: Gluon.SRExp -> [TType] -> PureTC ([Gluon.WRExp], Gluon.WRExp)
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
buildCaseParameters :: RType    -- ^ Scrutinee type
                    -> Alt (Typed Rec)
                    -> F (Con, [Value], [RBinder DataMode], Effect)
buildCaseParameters scrutinee_type alt = do
  -- Get types of the value parameters and scrutinee
  (param_types, inferred_scrutinee_type) <- liftPure $ getAltParameterTypes alt

  -- Scrutinee type should match.
  -- We assume the expression is well-typed, so skip the test.
  when False $ tcAssertEqual noSourcePos (verbatim scrutinee_type)
                                         (verbatim $ fromWhnf inferred_scrutinee_type)

  -- Set the alternative's parameter types to the inferred types.
  -- Then find the appropriate parameter passing modes.
  params' <-
    let set_param_type (Binder v _ ()) ty = Binder v (fromWhnf ty) ()
    in mapM setParameterMode $
       zipWith set_param_type (altParams alt) param_types

  -- Compute side effect
  let effect = parameterEffects params'

  let ty_args = map (TypeV . fromTypedType) $ altTyArgs alt

  return (altConstructor alt, ty_args, params', effect)

parameterEffects :: [RBinder DataMode] -> Effect
parameterEffects patterns = effectUnions $ map parameterEffect patterns

parameterEffect (Binder v _ mode) =
  case mode
  of IOVal -> noEffect
     IOClo -> noEffect
     InRef -> varEffect v
     OutRef -> internalError "parameterEffect"

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
      in if length args < length effs && isSomeEffect effect
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
               case mode of PassByVal -> ignore_continue rng
                            PassByRef -> add_effect_continue rng
                            PassByClo -> ignore_continue rng
           | otherwise -> internalError "functionTypeEffect"
         _ -> end
      where
        -- ignore this parameter
        ignore_continue rng = liftM (ignore :) $ parameter_effects rng

        -- This parameter's effect should be added
        add_effect_continue rng = liftM (add_effect :) $ parameter_effects rng
        
        end = return []
        
        ignore _ effect = effect
        
        add_effect (VariableArgument v) effect = effectUnion (varEffect v) effect
        add_effect _ effect = internalError "functionTypeEffect"
        
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
withFlattenedExp typed_expression@(unpackTypedExp -> (ty, _)) k = do
  mode <- chooseMode ty
  case mode of
    PassByVal -> do
      (ctx, val) <- flattenExpValue (ValueReturn ty) typed_expression
      result <- k $ ValueArgument val
      return $ addContext ctx result
    PassByClo -> do
      parameterized_eff <- functionTypeEffect ty
      (ctx, val) <- flattenExpValue (ClosureReturn ty parameterized_eff) typed_expression
      result <- k $ ClosureArgument val parameterized_eff
      return $ addContext ctx result
    PassByRef -> do 
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
    of PassByVal -> flattenExpWriteValue inf (ValueReturn ty) v rhs
       PassByClo -> do eff <- functionTypeEffect ty
                       flattenExpWriteValue inf (ClosureReturn ty eff) v rhs
       PassByRef -> do stmt <- flattenExpWriteReference v rhs
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
    scrutinee_type = case unpackTypedExp scrutinee of (ty, _) -> ty

    -- Create a flattened case statement with the given scrutinee
    flatten (ValueArgument scrutinee_val) = do
      -- Flatten all case alternatives
      flat_alts <- mapM (flattenValAlt flattenBranch scrutinee_type) alts
      
      -- Get the return value of one of the alternatives (should be the same
      -- for all alternatives)
      let ret = fexpReturn $ valAltBody $ head flat_alts

      -- Take the union of all alternatives' side effects
      let effect = effectUnions $ map (fexpEffect . valAltBody) flat_alts
      
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
            effectUnions [ fexpEffect stmt `effectDiff` local_eff
                       | FlatRefAlt _ _ _ local_eff _ _ stmt <- flat_alts]
          effect = alternatives_effect `effectUnion` varEffect scrutinee_var
      
      let new_info = mkFlatInfo (getSourcePos inf) ret effect
      return $ CaseRefS new_info scrutinee_var scrutinee_type flat_alts

    flatten (ClosureArgument _ _) =
      internalError "flattenCase: scrutinee is a function"
      
    -- Flatten a value-case alternative
    flattenValAlt flattenBranch scrutinee_type alt = do
      -- Get the parameters to the pattern match  
      (con, ty_args, params, eff) <- buildCaseParameters scrutinee_type alt
      
      -- No side effects allowed in the pattern match
      unless (isNoEffect eff) $ internalError "flattenCase"

      -- Flatten the body
      body <- flattenBranch (altBody alt)
      return $ FlatValAlt con ty_args params body

    -- Flatten a reference-case alternative
    flattenRefAlt flattenBranch scrutinee_type alt = do
      -- Get the parameters to the pattern match  
      (con, ty_args, params, eff) <- buildCaseParameters scrutinee_type alt

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
                     texp@(unpackTypedExp -> (ty, expression)) =
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
           in return $ assignTemporaryValue pos dest ty IOVal value
         ClosureReturn ty eff ->
           let value = ValueS (mkClosureReturnInfo pos ty eff) val
           in return $ assignTemporaryValue pos dest ty IOClo value
         _ -> internalError "flattenExpWriteValue"

    return_component = returnMode return_mode

flattenExpValue :: FlatReturn -> TExp -> F (StmtContext, Value)
flattenExpValue (VariableReturn _ _) _ = internalError "flattenExpValue"

flattenExpValue return_mode
                typed_expression@(unpackTypedExp -> (ty, expression)) =
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
    return_component = returnMode return_mode
    returnValue v = return (idContext, v)

-- | Flatten an expression whose value will be read by reference.
-- The variable representing the expression's storage will be returned. 
flattenExpReference :: TExp -> F (StmtContext, Var)
flattenExpReference texp@(unpackTypedExp -> (ty, expression)) =
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
flattenExpWriteReference return_var texp@(unpackTypedExp -> (ty, expression)) =
  case expression
  of VarE {expInfo = inf, expVar = v} -> do
       -- Copy this variable to the destination
       pc <- getPassConv' ty
       let new_info = mkFlatInfo pos return_mode (varEffect v)
       return $ CopyS new_info v
     ConE {expCon = c} ->
       returnValue $ ConV c IOVal
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
  (_, eff, _) <- buildFunctionParameters ty_params params return_type
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
      in renameEffect rename_effect eff
    
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
  (params, eff, ret) <-
    buildFunctionParameters (funTyParams function) (funParams function) return_type
  
  -- Convert function body
  body <-
    assumeValueParameters params $
    case ret
    of ValueReturn _ -> do
         -- Flatten the expression and return its result value
         (ctx, val) <- flattenExpValue (ValueReturn return_type) (funBody function)
         let return_value =
               ValueS (mkValueReturnInfo body_pos return_type) val
         return $ ctx return_value
         
       VariableReturn _ v ->
         -- Flatten the expression,
         -- which writes the result as a side effect
         flattenExpWriteReference v (funBody function)
         
       ClosureReturn _ eff -> do
         -- Flatten the expression and return its result value
         (ctx, val) <- flattenExpValue (ClosureReturn return_type eff) (funBody function)
         let return_value =
               ValueS (mkClosureReturnInfo body_pos return_type eff) val
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

    assumeValueParameter (Binder v ty IOVal) m = assumePure v ty m
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

flattenModule :: Supply VarID -> Module (Typed Rec) -> IO [[FlatDef]]
flattenModule var_supply mod = do
  result <- runF var_supply $ flatten_module mod
  case result of
    Left errs -> fail "Flattening failed"
    Right defss -> return defss
  where
    flatten_module (Module defss exports) = do
      defss' <- flattenTopLevelDefGroups defss
      return defss'

