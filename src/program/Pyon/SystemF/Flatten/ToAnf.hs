
{-# LANGUAGE ViewPatterns, FlexibleContexts, FlexibleInstances,
             RelaxedPolyRec, GeneralizedNewtypeDeriving, Rank2Types #-}
module Pyon.SystemF.Flatten.ToAnf(flatten)
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
import Pyon.SystemF.Flatten.Flatten

flatten :: RModule -> IO Anf.RModule
flatten mod = do
  -- Get type information
  result1 <- typeCheckModule annotateTypes mod

  case result1 of
    Left errs -> fail "Type checking failed"
    Right tc_mod ->
      withTheVarIdentSupply $ \var_supply -> do
        -- Flatten module
        flat_mod <- flattenModule var_supply tc_mod
        
        -- DEBUG: print the flattened module
        print $ vcat $ map (vcat . map pprFlatDef) flat_mod
        
        -- Convert to ANF
        runToAnf var_supply $ anfModule flat_mod

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
           sv' <- Gluon.duplicateVar sv
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
  types <- mapM getEffectType' $ effectVars eff
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
       case fexpReturn rhs
       of VariableReturn ty v -> do
            rhs' <- anfStmt rhs
            state_v <- getStateVariableX "evalS" v
            state_ty <- getStateType v
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
  (body_return_spec, body_fn) <- anfStmtToProc no_extra_parameters body

  -- Create the parameter to the body function: either a state variable, or
  -- a unit value
  body_param <-
    case fexpReturn body
    of VariableReturn _ v ->
         liftM (Anf.mkVarV pos) $ getStateVariableX "anfReading" v 
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
    no_extra_parameters :: forall a. 
                           ([RBinder ()] -> StmtReturn -> ToAnf a)
                        -> ToAnf a
    no_extra_parameters = anfGetStmtReturnParameter body

    unit_value = Gluon.TupE (Gluon.mkSynInfo pos ObjectLevel) Gluon.Nil

-- | Create and use a local variable
anfLocal :: SourcePos -> RType -> FlatReturn -> Var -> Stmt
         -> ToAnf Anf.RStm 
anfLocal pos ty return_info var body = do
  -- The given type is the type of the local object
  let obj_type = ty

  -- Turn the body into a lambda function
  (body_return_spec, body_fn) <- anfStmtToProc add_local_object body

  -- Get the body function's effect type
  let effect_type = Anf.procEffectType body_fn

  -- The body's return type is a tuple containing the local state variable 
  -- and other things.  Remove the local state variable.
  let return_type =
        case Anf.procReturnType body_fn
        of rt@(Gluon.TupTyE {Gluon.expTyFields = _ Gluon.:*: fs}) ->
             rt {Gluon.expTyFields = fs}

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
    add_local_object :: forall a. ([RBinder ()] -> StmtReturn -> ToAnf a)
                     -> ToAnf a
    add_local_object f =
      -- Set up return value
      anfGetStmtReturnParameter body $ \ret_params ret_spec ->
      
      -- Set up the local object
      withReferenceVariable var ty $ withStateVariable var $ do
        -- Create parameters for the local variable
        (local_addr, local_ptr, local_st) <- getWriteReferenceVariables var
        input_st_type <- getUndefStateType var
        let params = [ Binder local_addr addressType ()
                     , Binder local_ptr (pointerType $ Gluon.mkInternalVarE local_addr) ()
                     , Binder local_st input_st_type ()
                     ]

        -- Create the return specification
        output_st_type <- getStateType var
        let ret_spec' = StmtTupleReturn [ret_spec
                                        , StmtStateReturn output_st_type var]
        
        -- Run the main computation
        f (params ++ ret_params) ret_spec'

-- | Help transform a statement to a procedure.  This function masks linear
-- variables out of the evaluation context.  The linear variable modified by 
-- the statement (if any) is replaced in the context.
anfGetStmtReturnParameter :: Stmt
                          -> ([RBinder ()] -> StmtReturn -> ToAnf a)
                          -> ToAnf a
anfGetStmtReturnParameter stm k =
  case fexpReturn stm
  of ValueReturn ty -> value_return ty
     ClosureReturn ty _ -> value_return ty
     VariableReturn ty v -> variable_return ty v
  where 
    value_return ty = k [] (StmtValueReturn ty)
    
    -- If returning a state variable, then set up the environment,
    -- create a parameter, and indicate that it shall be returned.
    variable_return ty v = withStateVariable v $ do
       -- Create binder and return type of this variable
       param_type <- getUndefStateType v
       input_state_var <- getStateVariableX "anfGetStmtReturnParameter" v
       let binder = Binder input_state_var param_type ()
       
       return_type <- getStateType v

       -- Run the main computation
       k [binder] (StmtStateReturn return_type v)

-- | The return specification for a procedure created by 'anfStmtToProc'.
-- This specifies what data type to return and what data it contains.
data StmtReturn =
    StmtValueReturn RType       -- ^ The return value of the statement
  | StmtStateReturn RType !Var  -- ^ A state variable
  | StmtTupleReturn [StmtReturn] -- ^ A tuple of things

pprStmtReturn :: StmtReturn -> Doc
pprStmtReturn (StmtValueReturn _) = text "Value"
pprStmtReturn (StmtStateReturn _ v) = text "State" <+> Gluon.pprVar v
pprStmtReturn (StmtTupleReturn xs) =
  parens $ sep $ punctuate (text ",") $ map pprStmtReturn xs

-- | Generate code to create a return value according to the specification.
-- The return value is some combination of the statement's return value and
-- other state variables.
buildStmtReturnValue :: StmtReturn -- ^ What to return
                     -> FlatReturn -- ^ Given statement's return value
                     -> Anf.RStm   -- ^ Given statement
                     -> ToAnf (RType, Anf.RStm)

-- First, handle cases where the statement's return value is already right
buildStmtReturnValue (StmtValueReturn ty) (ValueReturn _) stm =
  return (ty, stm)

buildStmtReturnValue (StmtValueReturn ty) (ClosureReturn _ _) stm =
  return (ty, stm)

buildStmtReturnValue (StmtStateReturn ty v) (VariableReturn _ v') stm 
  | v == v' = do
      return_type <- getStateType v
      consumeStateVariable v
      return (return_type, stm)

-- Now handle other cases
buildStmtReturnValue return_spec ret stm = do
  -- Bind the statement's result to a temporary variable
  stmt_result_id <- fresh
  let stmt_result_var = Gluon.mkAnonymousVariable stmt_result_id ObjectLevel
      result_binder = Binder stmt_result_var (returnType ret) ()
   
  -- Construct the return value
  (return_exp, return_type) <- make_return_value stmt_result_var return_spec
  
  -- Construct a let expression out of the whole thing
  let result_stm = Anf.mkReturnS $ Anf.mkExpV return_exp
      complete_info = Gluon.mkSynInfo stmt_pos ObjectLevel
      complete_stm = Anf.LetS complete_info result_binder stm result_stm
  
  return (return_type, complete_stm)
  where
    stmt_pos = getSourcePos stm

    -- | Construct a return value expression and its type
    make_return_value stmt_result_var return_spec = mrv return_spec
      where
        -- Return the statement's result
        mrv (StmtValueReturn ty) =
          return (Gluon.mkVarE stmt_pos stmt_result_var, ty)
        
        -- Consume and return a state variable
        mrv (StmtStateReturn _ state_v) = do
          v <- getStateVariableX "buildStmtReturnValue" state_v
          ty <- getStateType state_v
          consumeStateVariable state_v
          return (Gluon.mkVarE stmt_pos v, ty)
        
        -- Construct a tuple
        mrv (StmtTupleReturn xs) = do
          -- Make the field values
          fields <- mapM mrv xs
          
          -- Construct a tuple expression
          let add_tuple_field (field_exp, field_ty) tuple_expr =
                Binder' Nothing field_ty field_exp Gluon.:&: tuple_expr
              tuple = foldr add_tuple_field Gluon.Nil fields
          
          -- Construct the tuple type 
          let add_type_field (_, field_ty) type_expr =
                Binder' Nothing field_ty () Gluon.:*: type_expr
              tuple_type = foldr add_type_field Gluon.Unit fields
          
          return (Gluon.mkTupE stmt_pos tuple,
                  Gluon.mkTupTyE stmt_pos tuple_type)

  

-- | Convert an ANF statement to a procedure.
--
-- The first parameter sets up the procedure's parameters, return value, and
-- context.  If the 
-- The procedure takes either the unit value or a state object as a 
-- parameter.  It returns either a return value or a state object.  Pure
-- variable inputs are referenced directly.
anfStmtToProc :: (forall a. ([RBinder ()] -> StmtReturn -> ToAnf a) -> ToAnf a)
              -> Stmt
              -> ToAnf (StmtReturn, Anf.Proc Rec)
anfStmtToProc initialize_params stm =
  -- State variables outside the procedure are not accessible
  hideState $
  -- Set up any context we need, then create the procedure
  initialize_params make_proc
  where
    -- Create a procedure that returns by value
    make_proc ext_params ext_return_spec = do
      -- Get effect type
      effect_type <- anfEffectType $ fexpEffect stm

      -- Create body
      body <- anfStmt stm
      
      -- Construct the return expression
      (return_type, body') <-
        buildStmtReturnValue ext_return_spec (fexpReturn stm) body

      -- Return the new procedure
      let proc = Anf.Proc { Anf.procInfo = Gluon.mkSynInfo pos ObjectLevel
                          , Anf.procParams = ext_params
                          , Anf.procReturnType = return_type
                          , Anf.procEffectType = effect_type
                          , Anf.procBody = body'
                          }
      return (ext_return_spec, proc)

    pos = fexpSourcePos stm
    
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
  (return_spec, proc) <- anfStmtToProc alternative_parameters body
  return (con, proc)
  where
    return_value_type =
      case ret
      of ValueReturn ty -> Just ty
         ClosureReturn ty _ -> Just ty
         VariableReturn _ _ -> Nothing

    alternative_parameters k =
      -- Pass state in and out if required 
      anfGetStmtReturnParameter body $ \stmt_params stmt_ret ->
      -- Make each object field be a function parameter
      anfBindParameters Nothing params $ \anf_params -> do
        -- Always have one state parameter
        stmt_params' <-
          case stmt_params
          of [param] -> return stmt_params
             [] -> do -- Create a dummy parameter
                      v_id <- fresh
                      let dummy_v = Gluon.mkAnonymousVariable v_id ObjectLevel 
                      return [Binder dummy_v unitType ()]
             _ -> internalError "anfRetAlternative"
             
        -- The alternative body gets the object fields as parameters 
        -- plus one extra parameter for input state
        k (anf_params ++ stmt_params') stmt_ret

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