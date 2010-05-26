
{-# LANGUAGE ViewPatterns, FlexibleContexts, FlexibleInstances,
             ParallelListComp,
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

import Pyon.SystemF.Flatten.BuiltinsMap
import Pyon.SystemF.Flatten.FlatData
import Pyon.SystemF.Flatten.Flatten

mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM f (x:xs) = f x >>= continue
  where
    continue Nothing  = mapMaybeM f xs
    continue (Just y) = do ys <- mapMaybeM f xs
                           return (y : ys)

mapMaybeM _ [] = return []

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

-- | Types that have been converted from System F to ANF.
newtype AnfType = AnfType {fromAnfType :: RType}

anfBinder :: Var -> AnfType -> RBinder ()
anfBinder v (AnfType t) = Binder v t ()

anfBinder' :: Maybe Var -> AnfType -> RBinder' ()
anfBinder' mv (AnfType t) = Binder' mv t ()

actionType :: AnfType -> AnfType -> AnfType
actionType (AnfType eff) (AnfType ret) =
  let action = Anf.anfBuiltin Anf.the_Action
  in AnfType $ Gluon.mkInternalConAppE action [eff, ret]

unitValue :: Anf.RVal
unitValue = Anf.mkExpV $
            Gluon.TupE (Gluon.internalSynInfo ObjectLevel) Gluon.Nil

emptyEffect :: AnfType
emptyEffect = AnfType Gluon.Core.Builtins.Effect.empty

addrEffect :: Var -> AnfType -> AnfType
addrEffect v (AnfType obj_ty) =
  AnfType $ Gluon.mkInternalConAppE (Gluon.builtin Gluon.the_AtE) [obj_ty, Gluon.mkInternalVarE v]

anfEffectUnion :: [AnfType] -> AnfType
anfEffectUnion xs = AnfType $ foldr Gluon.Core.Builtins.Effect.sconj Gluon.Core.Builtins.Effect.empty $ map fromAnfType xs

-- Remove any effect affecting the given address variable.
-- We assume the effect is a composition of atomic effects on addresses.
anfMaskEffect addr effect = mask_effect effect
  where
    mask_effect eff@(Gluon.AppE { Gluon.expOper =
                                     Gluon.ConE {Gluon.expCon = con}
                                , Gluon.expArgs = args})
      | con `Gluon.isBuiltin` Gluon.the_SconjE = mask_sconj args
      | con `Gluon.isBuiltin` Gluon.the_AtE = mask_at eff args

    -- The empty effect is unchanged
    mask_effect eff@(Gluon.ConE {Gluon.expCon = con})
      | con `Gluon.isBuiltin` Gluon.the_EmpE = eff

    -- Other effect types should not show up
    mask_effect _ = internalError "anfMaskEffect: Unexpected effect"

    -- For a compound effect, process sub-effects
    mask_sconj [l, r] =
      let l' = mask_effect l
          r' = mask_effect r
      in Gluon.Core.Builtins.Effect.sconj l' r'

    -- An atomic effect is either masked out or unchanged
    mask_at old_eff [_, addr_type] =
      case addr_type
      of Gluon.VarE {Gluon.expVar = this_addr}
           | addr == this_addr -> Gluon.Core.Builtins.Effect.empty
           | otherwise -> old_eff

         -- Other effect types should not show up
         _ -> internalError "anfMaskEffect: Unexpected effect"

-- | Pure variable information.
data VarElaboration =
    ValueVar { valueVar :: !Var
             , valueType :: !AnfType
             }
  | ReferenceVar { addressVar :: !Var
                 , pointerVar :: !Var
                 , objectType :: !AnfType
                 }

-- | State variable information.
data VarStateElaboration =
  VarStateElaboration { -- | The state variable holding the currently live
                        -- state object corresponding to the original variable.
                        stateVar :: !Var
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
    internalError $ "hideState: State escapes: " ++ show (Map.keys $ anfStateMap s')
  return (x, s, w)

traceState :: ToAnf a -> ToAnf a
traceState (ToAnf m) = ToAnf $ RWST $ \r s -> do
  traceShow (Map.keys $ anfStateMap s) $ runRWST m r s

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
         Nothing -> internalError $ "getAddrVariable: No information for " ++ show v

getPointerVariable v =
  ToAnf $ asksStrict (lookup_pointer_variable . anfVariableMap)
  where
    lookup_pointer_variable env =
      case Map.lookup (varID v) env
      of Just (ReferenceVar {pointerVar = v'}) -> v'
         Just (ValueVar {}) -> internalError "getPointerVariable: Not a pointer"
         Nothing -> internalError "getPointerVariable: No information"

getValueVariableX s v = getValueVariable v
  -- trace s $ getValueVariable v

getValueVariable v =
  ToAnf $ asksStrict (lookup_value_variable . anfVariableMap)
  where
    lookup_value_variable env =
      case Map.lookup (varID v) env
      of Just (ValueVar {valueVar = v'}) -> v'
         Just (ReferenceVar {}) -> internalError "getValueVariable: Not a value "
         Nothing -> internalError $ "getValueVariable: No information"

getStateVariable v =
  ToAnf $ getsStrict (lookup_state_variable . anfStateMap)
  where
    lookup_state_variable env =
      case Map.lookup (varID v) env
      of Just (VarStateElaboration {stateVar = v'}) -> v'
         Nothing -> internalError $
                    "getStateVariable: No information for " ++ show v

-- | For debugging; calls 'getStateVariable'
getStateVariableX s v = trace s $ getStateVariable v
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

getPointerType :: Var -> ToAnf AnfType
getPointerType v = do
  addr <- getAddrVariable v
  return $ AnfType $ pointerType (Gluon.mkInternalVarE addr)

getEffectType :: Var -> ToAnf AnfType
getEffectType v = getEffectType' (varID v)

getEffectType' :: VarID -> ToAnf AnfType
getEffectType' v = do
  addr <- getAddrVariable' v
  AnfType obj_type <- ToAnf $ asksStrict (lookup_object_type . anfVariableMap)
  return $ AnfType $ effectType obj_type (Gluon.mkInternalVarE addr)
  where
    lookup_object_type env =
      case Map.lookup v env
           of Just (ReferenceVar {objectType = t}) -> t
              Just (ValueVar {}) -> internalError "getEffectType: Not a reference"
              Nothing -> internalError "getEffectType: No information"

-- | Get the value type of the data referenced by a variable.
getValueType :: Var -> ToAnf AnfType
getValueType v = ToAnf $ asksStrict (lookup_type . anfVariableMap)
  where
    lookup_type env =
      case Map.lookup (varID v) env
           of Just (ValueVar {valueType = t}) -> t
              Just (ReferenceVar {}) -> internalError "getValueType: Not a value"
              Nothing -> internalError "getValueType: No information"

-- | Get the object type of the data referenced by a variable.  The
-- type does not include modifiers indicating whether the variable is defined.
getObjectType :: Var -> ToAnf AnfType
getObjectType v = ToAnf $ asksStrict (lookup_object_type . anfVariableMap)
  where
    lookup_object_type env =
      case Map.lookup (varID v) env
           of Just (ReferenceVar {objectType = t}) -> t
              Just (ValueVar {}) -> internalError "getStateType: Not a reference"
              Nothing -> internalError "getStateType: No information"

getStateType :: Var -> ToAnf AnfType
getStateType v = do
  addr <- getAddrVariable v
  AnfType obj_type <- getObjectType v
  return $ AnfType $ stateType obj_type (Gluon.mkInternalVarE addr)

getUndefStateType :: Var -> ToAnf AnfType
getUndefStateType v = do
  addr <- getAddrVariable v
  AnfType obj_type <- getObjectType v
  return $ AnfType $ undefStateType obj_type (Gluon.mkInternalVarE addr)

-- | Get the parameter-passing convention for this type.  The type parameter
-- is a System F type, not an ANF type.
getAnfPassConv :: RType -> ToAnf Anf.RVal
getAnfPassConv passed_type = do
  passed_type' <- evalHead' passed_type 
  case unpackRenamedWhnfAppE passed_type' of
    Just (con, [])
      | con `isPyonBuiltin` the_int ->
          return $ Anf.mkConV pos $ Anf.anfBuiltin Anf.the_passConv_int
      | con `isPyonBuiltin` the_float ->
          return $ Anf.mkConV pos $ Anf.anfBuiltin Anf.the_passConv_float
      | con `isPyonBuiltin` the_bool ->
          return $ Anf.mkConV pos $ Anf.anfBuiltin Anf.the_passConv_bool
    Just (con, args) 
      | Just size <- whichPyonTupleTypeCon con -> do
          let pass_conv_con =
                case size
                of 2 -> Anf.anfBuiltin Anf.the_passConv_PyonTuple2
                   
          -- Compute parameter-passing conventions for tuple fields
          field_pass_convs <- mapM getAnfPassConv (map substFully args)
          
          -- Convert the type arguments
          anf_args <- mapM convertType $ map substFully args
          
          -- Pass the tuple field types and parameter-passing
          -- conventions to the tuple parameter-passing convention constructor
          let params = map (Anf.mkExpV . fromAnfType) anf_args ++
                       field_pass_convs
          return $ Anf.mkAppV pos (Anf.mkConV pos pass_conv_con) params
    Nothing ->
      case fromWhnf passed_type'
      of Gluon.VarE {Gluon.expVar = v} -> do
           -- Translate from a System F type variable to an ANF object variable
           anf_v <- getValueVariable v
           let anf_e = Gluon.mkInternalVarE anf_v
           
           -- Look up in the environment
           result <- liftPureToAnf $ findM (matchType anf_e) =<< getPureTypes
           case result of
             Just (dict_var, _) -> return $ Anf.mkInternalVarV dict_var
             Nothing -> internalError "getAnfPassConv: Can't find dictionary"
  where
    pos = getSourcePos passed_type

    passed_type_v = verbatim passed_type

    -- Return True if ty == PassConv anf_e, False otherwise
    matchType anf_e (_, ty) = do
      ty' <- evalHead' ty
      case unpackRenamedWhnfAppE ty' of
        Just (con, [arg]) | con == Anf.anfBuiltin Anf.the_PassConv ->
          testEquality (verbatim anf_e) arg
        _ -> return False

-- | Extend the environment with a specificaiton of how to translate a 
-- variable from System F to ANF.
withVariableElaboration :: Var -> VarElaboration -> ToAnf a -> ToAnf a
withVariableElaboration v elaboration (ToAnf m) =
  ToAnf $ local add_elaboration m
  where
    add_elaboration env =
      env {anfVariableMap =
              Map.insert (varID v) elaboration $ anfVariableMap env}

-- | Define the variable as a value variable.
-- Note that the variable's level may change from System F to ANF.
withValueVariable :: Var -> RType -> ToAnf a -> ToAnf a
withValueVariable v ty k = do
  ty'@(AnfType anf_type) <- convertType ty
  v' <- Gluon.newVar (varName v) (pred $ getLevel anf_type)
  withVariableElaboration v (ValueVar {valueVar = v', valueType = ty'}) $
    assumePure v' anf_type k

-- | Define the variable as a closure variable.  Use the given type, which 
-- is an ANF type.
withClosureVariableAnf :: Var -> AnfType -> ToAnf a -> ToAnf a
withClosureVariableAnf v (AnfType anf_type) k = do
  v' <- Gluon.newVar (varName v) (pred $ getLevel anf_type)
  withVariableElaboration v (ValueVar {valueVar = v', valueType = AnfType anf_type}) $
    assumePure v' anf_type k

withClosureVariable :: Var -> RType -> ToAnf a -> ToAnf a
withClosureVariable v ty k = do
  ty' <- convertType ty
  withClosureVariableAnf v ty' k

-- | The variable is pass-by-reference.  Define address and pointer variables
-- for it.
withReferenceVariable :: Var -> RType -> ToAnf a -> ToAnf a
withReferenceVariable v ty k = do
  -- Create new variables for the address and pointer
  address_var <- Gluon.newVar (varName v) ObjectLevel
  pointer_var <- Gluon.newVar (varName v) ObjectLevel
    
  -- Convert the object type
  ty' <- convertType ty  

  -- Put into environment
  withVariableElaboration v (ReferenceVar address_var pointer_var ty') $
    assumePure address_var addressType $
    assumePure pointer_var (pointerType (Gluon.mkInternalVarE address_var)) $
    k

-- | Create a new state variable for the given System F variable and put it in 
-- the environment.  There must not be a preexisting state variable at this 
-- key.
defineStateVariable :: Var -> ToAnf ()
defineStateVariable v = ToAnf $ defineStateVariableRWST v

defineStateVariableRWST :: Var -> RWST ToAnfEnv () ToAnfState PureTC ()
defineStateVariableRWST v = do
  v' <- lift $ Gluon.newVar (varName v) ObjectLevel
  assignStateVariableRWST v v'

assignStateVariable v v' = ToAnf $ assignStateVariableRWST v v'

assignStateVariableRWST v v' = modify (insert v v')
  where
    insert v v' s = s {anfStateMap = ins $ anfStateMap s}
      where
        ins m
          | varID v `Map.member` m =
              internalError $ "defineStateVariable: already defined " ++ show v -- DEBUG
          | otherwise =
              Map.insert (varID v) (VarStateElaboration v') m

-- | Remove a state variable from the environment
consumeStateVariable :: Var -> ToAnf ()
consumeStateVariable v = ToAnf $ modify (delete v)
  where
    delete v s = s {anfStateMap = Map.delete (varID v) $ anfStateMap s}

withStateVariable :: Var -> ToAnf a -> ToAnf a
withStateVariable v (ToAnf m) = ToAnf $ trace ("withStateVariable " ++ show v) $ do
  -- Create a new state variable
  defineStateVariableRWST v
  x <- m
  -- Verify that the local variable has been consumed
  assert_deleted_local_state =<< get
  return x
  where
    assert_deleted_local_state s
      | varID v `Map.member` anfStateMap s =
          internalError $ "withStateVariable: state escapes: " ++ show v
      | otherwise = return ()

anfCreateParameterMaps :: [RBinder DataMode] -> ToAnf a -> ToAnf a
anfCreateParameterMaps params k =
  foldr ($) k $ map anfCreateParameterMap params
               
-- | Create variable elaboration information for a parameter.
-- Skip pointer and state parameters; handle them when the address 
-- parameter is encountered.
anfCreateParameterMap :: RBinder DataMode -> ToAnf a -> ToAnf a
anfCreateParameterMap (Binder v ty data_mode) k =
      case data_mode
      of InHM  -> withValueVariable v ty k
         IOVal -> withValueVariable v ty k
         IOClo -> withValueVariable v ty k
         InRef -> withReferenceVariable v ty k
         OutRef -> withReferenceVariable v ty $ withStateVariable v k

-- | Convert a System F type to an ANF type.
convertType :: RType -> ToAnf AnfType
convertType ty = do
  mode <- chooseMode ty
  case mode of
    PassByClo -> convertClosureType ty
    PassByVal -> convertValType ty
    PassByRef -> convertValType ty

convertValType :: RType -> ToAnf AnfType
convertValType expression =
  case expression
  of Gluon.VarE {Gluon.expVar = v} -> do
       -- Types follow the pass-by-value convention
       v' <- getValueVariableX "convertValType" v
       return $ AnfType $ Gluon.mkVarE pos v'
     Gluon.ConE {Gluon.expCon = c} ->
       return $ AnfType $ Gluon.mkConE pos $ sfToAnfCon c
     Gluon.LitE {Gluon.expLit = literal} ->
       case literal
       of Gluon.KindL Gluon.PureKind ->
            return $ AnfType $ Gluon.mkInternalConE $ Gluon.builtin Gluon.the_Object
     Gluon.AppE {Gluon.expOper = op, Gluon.expArgs = args} -> do
       AnfType op' <- convertType op
       args' <- mapM convertType args
       return $ AnfType $ Gluon.mkAppE pos op' (map fromAnfType args')
     Gluon.FunE { Gluon.expMParam = Binder' Nothing dom ()
                , Gluon.expRange = rng} -> do
       AnfType dom' <- convertType dom
       AnfType rng' <- convertType rng
       return $ AnfType $ Gluon.mkArrowE pos False dom' rng'
     Gluon.FunE { Gluon.expMParam = Binder' (Just v) dom ()
                , Gluon.expRange = rng} -> do
       -- Dependent parameters are always passed by value
       withValueVariable v dom $ do
         real_v <- getValueVariableX "convertValType" v
         AnfType real_t <- getValueType v
         AnfType rng' <- convertType rng
         return $ AnfType $ Gluon.mkFunE pos False real_v real_t rng'
     _ -> internalError "convertType"
  where
    pos = getSourcePos expression

-- | Convert a SystemF function type to an ANF procedure type.
convertClosureType :: RType -> ToAnf AnfType
convertClosureType expression = convertPolyClosureType False expression

-- | Convert a SystemF polymorphic function type to an ANF procedure type.
--
-- The boolean parameter keeps track of whether any parameters corresponding 
-- to HM polymorphism have been seen.  If none are seen, then this function
-- is treated just like a monomorphic function.
convertPolyClosureType :: Bool -> RType -> ToAnf AnfType
convertPolyClosureType have_poly_parameters expression =
  case expression
  of Gluon.FunE {Gluon.expMParam = Binder' mv dom (), Gluon.expRange = rng} 
       | isPolyParameterType dom ->
         case mv
         of Nothing -> do
              AnfType dom' <- convertType dom
              AnfType rng' <- convertPolyClosureType True rng
              return $ AnfType $ Gluon.mkArrowE pos False dom' rng'
            Just v -> withValueVariable v dom $ do
              -- Dependent parameters are always passed by value
              real_v <- getValueVariableX "convertPolyClosureType" v
              AnfType real_t <- getValueType v
              AnfType rng' <- convertPolyClosureType True rng
              return $ AnfType $ Gluon.mkFunE pos False real_v real_t rng'
       | otherwise -> do
           anf_type <- convertMonoClosureType expression
           
           -- Create an 'Action' constructor if appropriate
           if have_poly_parameters
             then return $ pure_action_type anf_type 
             else return anf_type
     _ -> convertMonoClosureType expression
  where
    pos = getSourcePos expression

    pure_action_type return_type =
      actionType (AnfType Gluon.Core.Builtins.Effect.empty) return_type

convertMonoClosureType expression = do
  -- Get domain and return types
  let (dom_types, ret_type) = deconstruct_function_type id expression

  -- Determine parameter passing modes
  param_modes <- mapM chooseMode dom_types
  
  -- Create variables for new dependent parameters
  withMany with_param_var (zip dom_types param_modes) $ \param_binders -> 
    convertClosureReturn ret_type $ \return_binders ->
    let (addr_binders, value_binders, effects) = unzip3 param_binders
        (raddr_binder, rvalue_binder, rstate_binder, anf_ret_ty) =
          return_binders
        binders = catMaybes $ addr_binders ++ [raddr_binder] ++
                  value_binders ++ [rvalue_binder] ++
                  [rstate_binder]
    in do
      -- Create the effect type
      let eff = anfEffectUnion effects

      -- Build the function type
      let AnfType range = actionType eff anf_ret_ty
          converted_type = foldr mk_fun range binders
          
      return $ AnfType converted_type
  where
    pos = getSourcePos expression

    mk_fun param range =
      Gluon.FunE { Gluon.expInfo = Gluon.mkSynInfo pos (getLevel range)
                 , Gluon.expIsLinear = False
                 , Gluon.expMParam = param
                 , Gluon.expRange = range
                 }

    with_param_var (param_type, mode) k = 
      case mode
      of PassByVal -> do
           ty' <- convertType param_type
           k (Nothing, Just (anfBinder' Nothing ty'), emptyEffect)
         PassByClo -> do
           ty' <- convertType param_type
           k (Nothing, Just (anfBinder' Nothing ty'), emptyEffect)
         PassByRef -> do
           -- Create a new variable for the address
           address_var <- Gluon.newAnonymousVariable ObjectLevel
    
           -- Convert the object type
           obj_ty <- convertType param_type
      
           let pointer_type = AnfType $ pointerType (Gluon.mkInternalVarE address_var)
           assumePure address_var addressType $
             k (Just (anfBinder' (Just address_var) (AnfType addressType)), 
                Just (anfBinder' Nothing pointer_type),
                addrEffect address_var obj_ty)

    -- Deconstruct a function type into a parameter list and return type
    deconstruct_function_type hd function_type =
      case function_type
      of Gluon.FunE { Gluon.expMParam = Binder' Nothing dom ()
                    , Gluon.expRange = rng} ->
           deconstruct_function_type (hd . (dom :)) rng
         Gluon.FunE {Gluon.expMParam = Binder' (Just _) _ ()} ->
           internalError "convertMonoClosureType: Unexpected dependent type"
         _ -> (hd [], function_type)

-- | Convert a function return type and pass it to the continuation.
convertClosureReturn :: RType 
                     -> ((Maybe (RBinder' ()), Maybe (RBinder' ()), Maybe (RBinder' ()), AnfType) -> ToAnf a)
                     -> ToAnf a
convertClosureReturn ret_type k = do
  mode <- chooseMode ret_type
  case mode of
    PassByVal -> convert_return_type ret_type
    PassByClo -> convert_return_type ret_type
    PassByRef -> do
      -- Create a new variable for the address
      address_var <- Gluon.newAnonymousVariable ObjectLevel
    
      -- Convert the object type
      AnfType ty' <- convertType ret_type
      
      let addr_expr    = Gluon.mkInternalVarE address_var
          pointer_type = AnfType $ pointerType addr_expr
          state_type   = AnfType $ undefStateType ty' addr_expr
          return_type  = AnfType $ stateType ty' addr_expr
      assumePure address_var addressType $
        k (Just (anfBinder' (Just address_var) (AnfType addressType)),
           Just (anfBinder' Nothing pointer_type),
           Just (anfBinder' Nothing state_type),
           return_type)    
  where
    -- Return a value or closure
    convert_return_type expression = do
      return_type <- convertType expression
      k (Nothing, Nothing, Nothing, return_type)

isPolyParameterType :: RType -> Bool
isPolyParameterType ty
  | getLevel ty == ObjectLevel = internalError "isPolyParameterType"
  | getLevel ty /= TypeLevel = True 
  | otherwise =
      case ty
      of Gluon.ConE {Gluon.expCon = c} ->
           isDictionaryTypeConstructor c
         Gluon.AppE {Gluon.expOper = Gluon.ConE {Gluon.expCon = c}} ->
           isDictionaryTypeConstructor c
         _ -> False

-------------------------------------------------------------------------------

-- | Produce the value corresponding to this expression.
-- Only pass-by-value terms can be converted to a value.
anfValue :: SourcePos -> Value -> ToAnf Anf.RVal
anfValue pos value =
  case value
  of VarV v mode 
       | mode == InHM || mode == IOVal || mode == IOClo -> do
           real_v <- getValueVariableX "anfValue" v
           return $ Anf.mkVarV pos real_v
       | otherwise -> internalError "anfValue"
     ConV c mode 
       | mode == InHM || mode == IOVal || mode == IOClo -> do
           return $ Anf.mkConV pos (sfToAnfCon c)
       | otherwise -> internalError "anfValue"
     LitV (IntL n) -> return $ Anf.mkLitV pos (Gluon.IntL n)
     TypeV ty -> do AnfType ty' <- convertType ty
                    return $ Anf.mkExpV ty'
     FunV f -> do f' <- anfProc f
                  return $ Anf.mkLamV f'
     AppV op args -> do op' <- anfValue pos op
                        args' <- mapM (anfValue pos) args 
                        return $ Anf.mkAppV pos op' args'

-- | Produce an argument list corresponding to these expressions.  The
-- argument list will be passed to a function call.
anfArguments :: SourcePos -> [Value] -> ToAnf [Anf.RVal]
anfArguments pos values = do
  ty_values <- mapMaybeM convert_type values
  addr_values <- mapMaybeM convert_address values
  val_values <- mapMaybeM convert_value values
  st_values <- mapMaybeM convert_state values
  return $ ty_values ++ addr_values ++ val_values ++ st_values
  where
    convert_type value
      | is_hm_type value = liftM Just $ anfValue pos value
      | otherwise = return Nothing
    
    convert_address value =
      case value
      of VarV v mode ->
           case mode
           of InHM  -> return Nothing
              IOVal -> return Nothing
              IOClo -> return Nothing
              InRef -> addr_param v
              OutRef -> addr_param v
         ConV c mode ->
           case mode
           of InHM  -> return Nothing 
              IOVal -> return Nothing
              IOClo -> return Nothing
              InRef -> can't_convert value
              OutRef -> can't_convert value
         LitV _ -> return Nothing
         TypeV _ -> return Nothing
         FunV _ -> return Nothing
         AppV _ _ -> return Nothing

    -- For pass-by-reference data, pass a pointer 
    -- For other data, pass the value
    convert_value value
      | is_hm_type value = return Nothing
      | otherwise =
          case value
          of VarV v InRef  -> pointer_param v
             VarV v OutRef -> pointer_param v
             _             -> liftM Just $ anfValue pos value
         
    convert_state value = 
      case value
      of VarV v mode ->
           case mode
           of InHM  -> return Nothing
              IOVal -> return Nothing
              IOClo -> return Nothing
              InRef -> return Nothing
              OutRef -> state_param v
         _ -> return Nothing    -- State parameters are only for return values

    addr_param v = do
      real_v <- getAddrVariable v
      return $ Just $ Anf.mkVarV pos real_v

    value_param v = do
      real_v <- getValueVariableX "anfArguments" v
      return $ Just $ Anf.mkVarV pos real_v

    pointer_param v = do
      real_v <- getPointerVariable v
      return $ Just $ Anf.mkVarV pos real_v

    state_param v = do
      real_v <- getStateVariableX "anfArguments" v
      trace ("anfArguments: consume " ++ show v) $ consumeStateVariable v
      return $ Just $ Anf.mkVarV pos real_v
    
    is_hm_type (VarV _ mode) = mode == InHM
    is_hm_type (ConV _ mode) = mode == InHM
    is_hm_type (LitV _) = False
    is_hm_type (TypeV _) = True
    is_hm_type (FunV _) = False
    is_hm_type (AppV op _) = internalError "is_hm_type: not implemented"

    can't_convert value =
      internalError "anfArguments: Can't convert value"

-- | Build the arguments to the ANF translation of a tuple data constructor.
-- In addition to the regular parameters, the tuple takes some
-- parameter-passing conventions.
tupleDataConArguments :: SourcePos -> [Value] -> ToAnf [Anf.RVal]
tupleDataConArguments pos values = do
  -- Get normal arguments
  anf_args <- anfArguments pos values
  
  -- For each type parameter, get a parameter-passing convention
  let typarams = get_type_args values
  passconv_args <- mapM getAnfPassConv typarams

  return $ combine_args anf_args passconv_args
  where
    -- Get the type arguments, which are at the beginning of the argument list
    get_type_args args = [ty | TypeV ty <- args]
    
    -- Put the passing convention arguments after type arguments
    combine_args anf passconv =
      case splitAt (length passconv) anf
      of (ty, other) -> ty ++ passconv ++ other

-- | Given the System F operator of a call statement, build an argument list
-- from the arguments.  For most operators this calls 'anfArguments', but some
-- require special handling.
buildArgumentList :: Value -> SourcePos -> [Value] -> ToAnf [Anf.RVal]
buildArgumentList operator =
  case operator
  of ConV sf_con _
       | Just _ <- whichPyonTupleCon sf_con -> tupleDataConArguments
     _ -> anfArguments

-- | Return True if the operator is a known non-monadic System F function or
-- object-level constructor.  Return False for anything else.
isPureOperator :: Value -> Bool
isPureOperator (ConV c _) =
  c `elem` [pyonBuiltin the_eqDict, pyonBuiltin the_ordDict,
            pyonBuiltin the_traversableDict, pyonBuiltin the_additiveDict,
            pyonBuiltin the_vectorDict]

isPureOperator _ = False

-- | Get the ANF type of a function.
--
-- The translation from binders to arrow types in this function matches
-- the translation from binders to binders in 'anfBindParameters'.
anfFunctionType :: FlatFun -> ToAnf AnfType
anfFunctionType ffun = 
  anfGetFunctionParameters ffun $ \stmt_params rt eff_ty -> do
    params <- toAnfParameters stmt_params
    
    -- Compute the return type
    ret_ty <- buildStmtReturnType pos rt
    let AnfType range = actionType eff_ty ret_ty
        
    -- We don't need any state variables.  Consume the return value.
    consumeStmtReturn rt
    
    -- Create a function type
    return $ AnfType $ foldr mk_fun range params
  where
    pos = getSourcePos $ ffunInfo ffun
    mk_fun (Binder v ty ()) rng
      | rng `Gluon.mentions` v = Gluon.mkFunE pos False v ty rng
      | otherwise              = Gluon.mkArrowE pos False ty rng

anfProc :: FlatFun -> ToAnf (Anf.Proc Rec)
anfProc ffun = hideState $
  -- Convert function parameters and make a local parameter mapping
  anfBindParameters (ffunParams ffun) $ \params -> do
    -- Convert effect type
    et <- anfEffectType (ffunEffect ffun)
    
    -- Get return type
    body_return <- stmtReturn $ ffunBody ffun 
    let rt = case body_return
             of StmtValueReturn t -> t
                StmtStateReturn t _ -> t

    -- Convert body
    body <- anfStmt body_return $ ffunBody ffun
    
    return $ Anf.Proc (ffunInfo ffun) params (fromAnfType rt) (fromAnfType et) body
  where
    -- Find the parameter variable that is being used for returning stuff
    -- It's the only parameter with component 'State'
    return_variable =
      case find is_return_parameter $ ffunParams ffun
      of Just (Binder v _ _) -> Just v
         Nothing -> Nothing
      where
        is_return_parameter (Binder _ _ OutRef) = True
        is_return_parameter _ = False

    pos = getSourcePos (ffunInfo ffun)

-- | Convert System F parameters (such as function parameters) to ANF
-- parmeters.
--
-- The parameter conversion must match how function types are converted
-- in 'anfFunctionType'.
anfBindParameters :: [RBinder DataMode]
                  -> ([RBinder ()] -> ToAnf a)
                  -> ToAnf a
anfBindParameters params k =
  anfCreateParameterMaps params $ do
    ty_params <- mapMaybeM convert_type params
    addr_params <- mapMaybeM convert_address params
    val_params <- mapMaybeM convert_value params
    st_params <- mapMaybeM convert_state params
    let all_params = ty_params ++ addr_params ++ val_params ++ st_params
    k all_params
  where
    convert_type (Binder v ty d_mode) =
      case d_mode
      of InHM -> value_parameter v
         _ -> return Nothing

    convert_address (Binder v ty d_mode) =
      case d_mode
      of InHM  -> return Nothing
         IOVal -> return Nothing
         IOClo -> return Nothing
         InRef -> address_parameter v
         OutRef -> address_parameter v
    
    convert_value (Binder v ty d_mode) =
      case d_mode
      of InHM  -> return Nothing
         IOVal -> value_parameter v
         IOClo -> value_parameter v
         InRef -> pointer_parameter v
         OutRef -> pointer_parameter v

    convert_state (Binder v ty d_mode) =
      case d_mode
      of InHM  -> return Nothing 
         IOVal -> return Nothing
         IOClo -> return Nothing
         InRef -> return Nothing
         OutRef -> state_parameter v

    address_parameter v = do
      real_v <- getAddrVariable v
      return $ Just $ Binder real_v addressType ()
      
    value_parameter v = do
      real_v <- getValueVariable v
      AnfType real_t <- getValueType v
      return $ Just $ Binder real_v real_t ()

    pointer_parameter v = do
      real_v <- getPointerVariable v
      AnfType real_t <- getPointerType v
      return $ Just $ Binder real_v real_t ()

    state_parameter v = do
      real_v <- getStateVariableX "anfBindParameters" v
      AnfType real_t <- getUndefStateType v
      return $ Just $ Binder real_v real_t ()

-- | Compute the effect type corresponding to the read part of this effect.
anfEffectType :: Effect -> ToAnf AnfType
anfEffectType eff = do
  types <- mapM getEffectType' $ effectReadVars eff
  return $ AnfType $ foldr
    Gluon.Core.Builtins.Effect.sconj
    Gluon.Core.Builtins.Effect.empty
    (map fromAnfType types)

anfDef :: FlatDef -> ToAnf (Anf.ProcDef Rec)
anfDef (FlatDef v f) = do
  f' <- anfProc f 
  v' <- getValueVariableX "anfDef" v
  return $ Anf.ProcDef v' f'

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
      withClosureVariableAnf v ty k

-- | Generate ANF code for a statement.  The code retuns the statement's
-- return value.
evalAnfStmt :: Stmt -> ToAnf Anf.RStm
evalAnfStmt statement = do
  statement_return <- stmtReturn statement
  anfStmt statement_return statement

-- | Generate ANF code for a statement.
--
-- After generating the statement, apply the transformation to it to package 
-- its return value.
anfStmt :: StmtReturn -> Stmt -> ToAnf Anf.RStm
anfStmt statement_return statement = trace (stmtString statement) $ stop_on_error $
  case statement
  of -- These cases have a corresponding ANF expression
     ValueS {fexpValue = val} -> do
       val' <- anfValue pos val
       wrap_statement $ Anf.ReturnS anf_info val'
     CallS {fexpOper = op, fexpArgs = args} -> do
       op' <- anfValue pos op
       args' <- buildArgumentList op pos args
       let call = Anf.AppV anf_info op' args'
           
       -- If the operator has no side effects, then generate a pure call
       -- otherwise generate a side-effecting call
       wrap_statement $! if isPureOperator op
                         then Anf.ReturnS anf_info call
                         else Anf.CallS anf_info call
     LetS {fexpBinder = Binder v ty _, fexpRhs = rhs, fexpBody = body} -> do
       rhs' <- evalAnfStmt rhs
       (anf_v, anf_ty, body') <- withValueVariable v ty $ do 
         anf_v <- getValueVariable v
         AnfType anf_ty <- getValueType v
         
         -- Generate the body of the 'let'
         body' <- anfStmt statement_return body
         return (anf_v, anf_ty, body')
       
       return $ Anf.LetS anf_info (Binder anf_v anf_ty ()) rhs' body'
     EvalS {fexpRhs = rhs, fexpBody = body} ->
       case fexpReturn rhs
       of VariableReturn _ v -> do
            rhs' <- evalAnfStmt rhs
            
            -- The let-binding introduces a new definition of this variable
            defineStateVariable v
            state_v <- getStateVariableX "evalS" v
            AnfType state_ty <- getStateType v
         
            -- Generate the body of the 'let'
            body' <- anfStmt statement_return body
            return $ Anf.LetS anf_info (Binder state_v state_ty ()) rhs' body'
          _ -> internalError "anfStmt"
     LetrecS {fexpDefs = defs, fexpBody = body} -> do
       (defs', body') <- anfDefGroup defs $ anfStmt statement_return body
       return $ Anf.LetrecS anf_info defs' body'
     CaseValS {fexpScrutinee = val, fexpValAlts = alts} -> do
       val' <- anfValue pos val
       alts' <- mapM anfAlternative alts
       wrap_statement $ Anf.CaseS anf_info val' alts'
       
     -- These cases do not have a direct ANF translation, and instead must be
     -- converted to function calls
     CopyValueS {fexpValue = val} ->
       case fexpReturn statement
       of VariableReturn return_type dst -> do
            wrap_statement =<< anfStoreValue pos return_type dst val
          _ -> internalError "anfStmt"
     CaseRefS { fexpScrutineeVar = var
              , fexpScrutineeType = scr_ty
              , fexpRefAlts = alts} -> do
       wrap_statement =<< anfCaseRef pos var scr_ty (fexpEffect statement) (fexpReturn statement) alts
     ReadingS { fexpScrutineeVar = var
              , fexpScrutineeType = ty
              , fexpBody = body} -> do
       anfReading pos ty statement_return (fexpReturn statement) var body
     LocalS {fexpVar = var, fexpType = ty, fexpBody = body} -> do
       wrap_statement =<< anfLocal pos ty (fexpReturn statement) var body
     CopyS {fexpSrc = src} ->
       case fexpReturn statement
       of VariableReturn return_type dst ->
            wrap_statement =<< anfCopyValue pos return_type dst src
          _ -> internalError "anfStmt"
  where
    -- Fix up the statement's return value
    wrap_statement s =
      buildStmtReturnValue statement_return (fexpReturn statement) s

    pos = getSourcePos anf_info
    anf_info = fexpInfoInfo $ fexpInfo statement
    
    -- DEBUG: Don't continue after encountering an error
    stop_on_error (ToAnf m) = do
      (errs, x) <- ToAnf $ RWST $ \r s -> do
        (err, (x, s, w)) <- tellErrors (runRWST m r s)
        return ((err, x), s, w)
      if null errs then return x else internalError (concatMap showTypeCheckError errs)

anfReading :: SourcePos -> RType -> StmtReturn -> FlatReturn -> Var -> Stmt
           -> ToAnf Anf.RStm 
anfReading pos _ anf_return_spec return_info read_var body = do
  -- Get the type of the variable to be read
  -- (should be a defined state variable)
  obj_type <- getObjectType read_var
  addr_var <- getAddrVariable read_var
  
  -- Turn the body into a lambda function
  (body_return_spec, body_fn) <- anfStmtToProc no_extra_parameters body

  -- Create the parameter to the body function: either a state variable, or
  -- a unit value
  (body_param_spec, _) <- anfGetStmtReturnParameter True body
  (body_param, body_param_type) <- anfGetStmtStateInput pos (fexpReturn body)

  -- Get the body function's effect and return type.  Mask out the effect
  -- of reading the parameter variable.
  let effect_type = anfMaskEffect addr_var $ Anf.procEffectType body_fn
      return_type = AnfType $ Anf.procReturnType body_fn

  -- Get the state variable to read from.  Redefine the variable
  read_param_var <- getStateVariableX "anfReading" read_var
  read_param_type <- getStateType read_var
  consumeStateVariable read_var
  
  -- Create a "reading" expression
  let reading = Anf.mkConV pos $ Anf.anfBuiltin Anf.the_reading 
      stmt = Anf.mkCallAppS pos reading [ Anf.mkExpV effect_type
                                        , Anf.mkExpV (fromAnfType body_param_type)
                                        , Anf.mkExpV (fromAnfType return_type)
                                        , Anf.mkExpV (fromAnfType obj_type)
                                        , Anf.mkVarV pos addr_var
                                        , Anf.mkLamV body_fn
                                        , Anf.mkVarV pos read_param_var
                                        , body_param
                                        ]

  -- The result of the expression is a (new state, return value) pair.
  -- Unpack the result, then wrap the return value to get
  -- the real return value.
  let actual_return = StmtTupleReturn [ StmtStateReturn read_param_type read_var
                                      , body_return_spec
                                      ]
  adaptStmtReturn actual_return anf_return_spec stmt
  where
    -- We don't need any extra parameters in the body function
    no_extra_parameters :: forall a. 
                           ([StmtParam] -> StmtReturn -> ToAnf a)
                        -> ToAnf a
    no_extra_parameters = withStmtReturnParameters True body

-- | Create and use a local variable
anfLocal :: SourcePos -> RType -> FlatReturn -> Var -> Stmt
         -> ToAnf Anf.RStm
anfLocal pos ty return_info var body = do
  -- Convert the local object's type to its ANF equivalent
  obj_type <- convertType ty

  -- Get the parameter-passing convention for this type
  pass_conv <- getAnfPassConv ty

  -- Turn the body into a lambda function
  (body_return_spec, body_fn) <- anfStmtToProc add_local_object body

  -- Get the body function's effect type
  let effect_type = Anf.procEffectType body_fn

  -- The body returns a tuple containing the local state variable 
  -- and the actual return value.  Get the type of the actual return value.
  return_type <-
    case body_return_spec
    of StmtTupleReturn [rt, _] ->
         case rt
         of StmtValueReturn ty -> return ty
            StmtStateReturn _ v -> getStateType v
            _ -> internalError "anfLocal"
       _ -> internalError "anfLocal"
  
  -- Do we need to pass state in/out?
  (state_param, state_param_type) <- anfGetStmtStateInput pos (fexpReturn body)

  -- Create the new statement
  let local = Anf.mkConV pos $ Anf.anfBuiltin Anf.the_local
      stmt = Anf.mkCallAppS pos local [ Anf.mkExpV effect_type
                                      , Anf.mkExpV (fromAnfType state_param_type)
                                      , Anf.mkExpV (fromAnfType return_type)
                                      , Anf.mkExpV (fromAnfType obj_type)
                                      , pass_conv
                                      , Anf.mkLamV body_fn
                                      , state_param
                                      ]
    
  return stmt
  where
    -- Pass the local object as an extra parameter in the body function.
    -- Also return it.
    add_local_object :: forall a. ([StmtParam] -> StmtReturn -> ToAnf a)
                     -> ToAnf a
    add_local_object f =
      -- Set up return value
      withStmtReturnParameters True body $ \ret_params ret_spec ->
      
      -- Set up the local object
      withReferenceVariable var ty $ withStateVariable var $ do
        -- Create parameters for the local variable
        (local_addr, local_ptr) <- getReadReferenceVariables var
        let params = [ StmtRefParam
                       (Binder local_addr addressType ())
                       (Binder local_ptr (pointerType $ Gluon.mkInternalVarE local_addr) ())
                     , StmtStateParam False var
                     ]

        -- Create the return specification
        output_st_type <- getStateType var
        let ret_spec' = StmtTupleReturn [ ret_spec
                                        , StmtStateReturn output_st_type var]
        
        -- Run the main computation
        f (params ++ ret_params) ret_spec'

-- | Get parameters and returns that are used for a statement's return 
-- value, when converting it to a function.
withStmtReturnParameters :: Bool
                         -> Stmt
                         -> ([StmtParam] -> StmtReturn -> ToAnf a)
                         -> ToAnf a
withStmtReturnParameters use_dummy_param stm k = do
  (params, ret) <- anfGetStmtReturnParameter use_dummy_param stm
  with_parameter params $ k params ret
  where
    -- Only three parameter-passing cases to deal with
    with_parameter [] k = k
    with_parameter [StmtValueParam False (Binder v ty ())] k =
      assumeIfPure v ty k
    with_parameter [StmtStateParam _ v] k = withStateVariable v k
    with_parameter _ _ = internalError "withStmtReturnParameters"

anfGetStmtReturnParameter :: Bool -> Stmt -> ToAnf ([StmtParam], StmtReturn)
anfGetStmtReturnParameter use_dummy_param stm =
  case fexpReturn stm
  of ValueReturn ty -> value_return ty
     ClosureReturn ty _ -> value_return ty
     VariableReturn ty v -> variable_return ty v
  where
    value_return sf_ty = do
      params <- if use_dummy_param
                then do v <- Gluon.newAnonymousVariable ObjectLevel
                        return [StmtValueParam False (Binder v unitType ())]
                else return []
      return (params, StmtValueReturn (AnfType unitType))
    
    -- If returning a state variable, then set up the environment,
    -- create a parameter, and indicate that it shall be returned.
    variable_return _ v = do
      return_type <- getStateType v
      return ([StmtStateParam False v], StmtStateReturn return_type v)

-- | Get a value that can be passed as input state to a statement.
anfGetStmtStateInput :: SourcePos -> FlatReturn -> ToAnf (Anf.RVal, AnfType)
anfGetStmtStateInput pos (ValueReturn _) =
  return (unitValue, AnfType unitType)
anfGetStmtStateInput pos (ClosureReturn _ _) =
  return (unitValue, AnfType unitType)
anfGetStmtStateInput pos (VariableReturn _ v) = do
  ty <- getUndefStateType v
  st_var <- getStateVariableX "anfGetStmtStateInput" v
  consumeStateVariable v
  return (Anf.mkVarV pos st_var, ty)

-- | The return specification for a procedure created by 'anfStmtToProc'.
-- This specifies what ANF data type to return and what data it contains.
data StmtReturn =
    StmtValueReturn AnfType       -- ^ The return value of the statement
  | StmtStateReturn AnfType !Var  -- ^ A state variable
  | StmtTupleReturn [StmtReturn]  -- ^ A tuple of things

-- | Return True iff the two given values represent the same return expression.
--
-- Since any statement can only have one \"value\" return, instances of
-- 'StmtValueReturn' are always regarded as equal.
sameStmtReturn :: StmtReturn -> StmtReturn -> Bool
sameStmtReturn x y = 
  case (x, y)
  of (StmtValueReturn _, StmtValueReturn _) ->
       True
     (StmtStateReturn _ v1, StmtStateReturn _ v2) ->
       v1 == v2
     (StmtTupleReturn xs, StmtTupleReturn ys) ->
       and $ zipWith sameStmtReturn xs ys

stmtReturn :: Stmt -> ToAnf StmtReturn
stmtReturn s =
  case fexpReturn s
  of ValueReturn ty -> do anf_type <- convertType ty
                          return $ StmtValueReturn anf_type
     ClosureReturn ty _ -> do anf_type <- convertType ty
                              return $ StmtValueReturn anf_type
     VariableReturn ty v -> do anf_type <- getStateType v
                               return $ StmtStateReturn anf_type v
pprStmtReturn :: StmtReturn -> Doc
pprStmtReturn (StmtValueReturn _) = text "Value"
pprStmtReturn (StmtStateReturn _ v) = text "State" <+> Gluon.pprVar v
pprStmtReturn (StmtTupleReturn xs) =
  parens $ sep $ punctuate (text ",") $ map pprStmtReturn xs

-- | Parameters to a statement.
-- Parameters are grouped according to the System F convention, but expanded
-- into ANF.  Pass-by-reference parameters, for example, consist of two
-- binders.   Types are in ANF.
data StmtParam =
    -- | A value parameter derived from System F.
    -- If the flag is True, this is a type or dictionary parameter and it 
    -- comes before other parameters.
    StmtValueParam !Bool (RBinder ())
    -- | A (read or write) reference parameter derived from System F.  The
    -- parameter consists of an address and a pointer.
  | StmtRefParam (RBinder ()) (RBinder ())
    -- | A dummy parameter of unit type.  The parameter's ANF variable is
    -- given.
  | StmtDummyParam !Var
    -- | A System F state variable that is passed as a parameter.
    -- The boolean value is False if the variable's is an 'Undef' type.
  | StmtStateParam !Bool !Var
    -- | A collection of state variables passed as a tuple.  The tuple is bound
    -- to an ANF parameter variable, given as the first parameter.
  | StmtStatesParam !Var [(Bool, Var)]

pprStmtParam :: StmtParam -> Doc
pprStmtParam (StmtValueParam is_type (Binder v ty ())) =
  let ty_doc = text $ if is_type then "type" else "val"
  in parens $ ty_doc <+> Gluon.pprVar v <+> text ":" <+> Gluon.pprExp ty

pprStmtParam (StmtRefParam (Binder v1 ty1 ()) (Binder v2 ty2 ())) =
  parens $ text "ref" <+>
  Gluon.pprVar v1 <+> text ":" <+> Gluon.pprExp ty1 <+> text ";" <+>
  Gluon.pprVar v2 <+> text ":" <+> Gluon.pprExp ty2

pprStmtParam (StmtDummyParam v) = parens $ text "dummy" <+> Gluon.pprVar v

pprStmtParam (StmtStateParam True v) =
  parens $ text "state" <+> Gluon.pprVar v
  
pprStmtParam (StmtStateParam False v) =
  parens $ text "undef state" <+> Gluon.pprVar v

pprStmtParam (StmtStatesParam v xs) =
  let states_doc = parens $ hcat $ punctuate (text ",") $ map sub_state xs
  in parens $ text "states" <+> states_doc <+> text "as" <+> Gluon.pprVar v
  where
    sub_state (b, v) =
      let label = text $ if b then "state" else "undef state"
      in label <+> Gluon.pprVar v

-- | Convert System F parameters to StmtParam parameters.  Anf variables are
-- created.
sfToStmtParams :: [RBinder DataMode] -> ([StmtParam] -> ToAnf a) -> ToAnf a
sfToStmtParams binders k =
  -- Translate System F variables to ANF variables
  anfCreateParameterMaps binders $ do
  
    -- Convert all parameters
    parameter_data <- mapM convert binders
    let (params, m_state_params) = unzip parameter_data
        state_params = catMaybes m_state_params
  
    k (params ++ state_params)
  where
    convert (Binder v ty d_mode) =
      case d_mode
      of InHM  -> pass_by_value True v
         IOVal -> pass_by_value False v
         IOClo -> pass_by_value False v
         InRef -> pass_in_reference v
         OutRef -> pass_out_reference v 

    pass_by_value is_type v = do
      val_v <- getValueVariable v
      AnfType val_type <- getValueType v
      return (StmtValueParam is_type (Binder val_v val_type ()), Nothing)
    
    pass_in_reference v = do
      (address_v, pointer_v) <- getReadReferenceVariables v
      let address_b = Binder address_v addressType ()
          pointer_b = Binder pointer_v (pointerType (Gluon.mkInternalVarE address_v)) ()
      return (StmtRefParam address_b pointer_b, Nothing)

    -- Like pass-in-reference, but also take a state parameter
    pass_out_reference v = do
      (param, Nothing) <- pass_in_reference v
      return (param, Just (StmtStateParam False v))

toAnfParameters :: [StmtParam] -> ToAnf [RBinder ()]
toAnfParameters params = do
  other_parameters <- mapMaybeM get_other_parameter params
  return $ mapMaybe ty_parameter params ++
           mapMaybe addr_parameter params ++
           other_parameters
  where
    ty_parameter (StmtValueParam True p) = Just p
    ty_parameter _ = Nothing

    addr_parameter (StmtRefParam p _) = Just p
    addr_parameter _ = Nothing

    get_other_parameter (StmtValueParam True p) = return Nothing
    get_other_parameter (StmtValueParam False p) = return $ Just p
    get_other_parameter (StmtRefParam _ p) = return $ Just p
    get_other_parameter (StmtDummyParam v) = return $ Just $ Binder v unitType ()
    get_other_parameter (StmtStateParam is_def v) = do
      state_v <- getStateVariableX "toAnfParameters" v
      AnfType state_type <-
        if is_def then getStateType v else getUndefStateType v
      return $ Just $ Binder state_v state_type ()
    get_other_parameter _ = internalError "toAnfParameters"

anfGetFunctionParameters :: FlatFun
                         -> ([StmtParam] -> StmtReturn -> AnfType -> ToAnf a)
                         -> ToAnf a
anfGetFunctionParameters ffun k =
  -- Translate System F variables to ANF variables
  anfCreateParameterMaps (ffunParams ffun) $ do
  
    -- Convert all parameters
    parameter_data <- mapM convert (ffunParams ffun)
    let (params, m_state_params, effects) = unzip3 parameter_data
        state_params = catMaybes m_state_params
        effect = anfEffectUnion effects
        
    -- Convert return type
    return_spec <- case ffunReturn ffun of
      ValueReturn ty -> do
        anf_ty <- convertType ty
        return $ StmtValueReturn anf_ty
      ClosureReturn ty _ -> do
        anf_ty <- convertType ty
        return $ StmtValueReturn anf_ty
      VariableReturn _ v -> do
        anf_ty <- getStateType v
        return $ StmtStateReturn anf_ty v
    
    -- Pass to the continuation
    k (params ++ state_params) return_spec effect
  where
    convert (Binder v ty d_mode) =
      case d_mode
      of InHM  -> pass_by_value True v
         IOVal -> pass_by_value False v
         IOClo -> pass_by_value False v
         InRef -> pass_in_reference v
         OutRef -> pass_out_reference v 
    
    pass_by_value is_type v = do
      val_v <- getValueVariable v
      AnfType val_type <- getValueType v
      return (StmtValueParam is_type (Binder val_v val_type ()), Nothing,
              emptyEffect)
    
    pass_in_reference v = do
      eff_type <- getEffectType v
      (address_v, pointer_v) <- getReadReferenceVariables v
      let address_b = Binder address_v addressType ()
          pointer_b = Binder pointer_v (pointerType (Gluon.mkInternalVarE address_v)) ()
      return (StmtRefParam address_b pointer_b, Nothing, eff_type)

    -- Like pass-in-reference, but also take a state parameter
    pass_out_reference v = do
      (param, Nothing, _) <- pass_in_reference v
      return (param, Just (StmtStateParam False v), emptyEffect)

-- | Consume state variables in a StmtReturn without producing anything.
consumeStmtReturn :: StmtReturn -> ToAnf ()
consumeStmtReturn (StmtValueReturn _) = return ()
consumeStmtReturn (StmtStateReturn _ v) = consumeStateVariable v
consumeStmtReturn (StmtTupleReturn t) = mapM_ consumeStmtReturn t

-- | Generate code to create a return value according to the specification.
-- The return value is some combination of the statement's return value and
-- other state variables.
--
-- Instances of this function are passed to 'anfStmt'.
buildStmtReturnValue :: StmtReturn -- ^ What to return
                     -> FlatReturn -- ^ Given statement's return value
                     -> Anf.RStm   -- ^ Given statement
                     -> ToAnf Anf.RStm

-- First, handle cases where the statement's return value is already right
buildStmtReturnValue (StmtValueReturn ty) (ValueReturn _) stm =
  return stm

buildStmtReturnValue (StmtValueReturn ty) (ClosureReturn _ _) stm =
  return stm

buildStmtReturnValue (StmtStateReturn ty v) (VariableReturn _ v') stm 
  | v == v'   = consumeStateVariable v >> return stm
  | otherwise = internalError "buildStmtReturnValue"

-- Now handle other cases
buildStmtReturnValue return_spec ret stm = do
  -- Create a temporary variable to hold the statement's result value.
  -- 
  (stmt_result_var, value_expr, anf_return_type) <-
    case ret
    of ValueReturn ty -> do
         v <- Gluon.newAnonymousVariable ObjectLevel
         rt <- convertType ty
         return (v, Just (Gluon.mkVarE stmt_pos v), rt)
       ClosureReturn ty _ -> do
         v <- Gluon.newAnonymousVariable ObjectLevel
         rt <- convertType ty
         return (v, Just (Gluon.mkVarE stmt_pos v), rt)
       VariableReturn _ v -> do
         trace "buildStmtReturnValue: define state variable" $ defineStateVariable v
         sv <- getStateVariableX "buildStmtReturnValue" v
         rt <- getStateType v
         return (sv, Nothing, rt)

  -- Construct a new return value that possibly uses the temporary variable
  return_exp <- buildStmtReturnValueFrom stmt_pos return_spec value_expr 
  
  -- Construct a let expression out of the whole thing
  let result_binder = Binder stmt_result_var (fromAnfType anf_return_type) ()
      result_stm = Anf.mkReturnS return_exp
      complete_info = Gluon.mkSynInfo stmt_pos ObjectLevel
      complete_stm = Anf.LetS complete_info result_binder stm result_stm
  
  return complete_stm
  where
    stmt_pos = getSourcePos stm

-- | Given a return value specification, and possibly a pass-by-value value,
-- build a return value.
buildStmtReturnValueFrom :: SourcePos -- ^ Source code position
                         -> StmtReturn -- ^ Specification of return value
                         -> Maybe Gluon.RExp -- ^ Pass-by-value return (if any)
                         -> ToAnf Anf.RVal
buildStmtReturnValueFrom pos return_spec maybe_value = do
  (return_exp, _) <- mrv return_spec
  return $ Anf.mkExpV return_exp
  where
    -- Return the pass-by-value part
    mrv (StmtValueReturn ty) =
      case maybe_value
      of Just v -> return (v, fromAnfType ty)
         Nothing -> internalError "buildStmtReturnValueFrom"

    -- Consume and return a state variable
    mrv (StmtStateReturn _ state_v) = do
      v <- getStateVariableX "buildStmtReturnValue" state_v
      ty <- getStateType state_v
      consumeStateVariable state_v
      return (Gluon.mkVarE pos v, fromAnfType ty)
    
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
      
      return (Gluon.mkTupE pos tuple,
              Gluon.mkTupTyE pos tuple_type)

buildStmtReturnType :: SourcePos  -- ^ Position that the type belongs to
                    -> StmtReturn -- ^ What to return
                    -> ToAnf AnfType
-- First, handle cases where the statement's return value is already right
buildStmtReturnType _ (StmtValueReturn ty) = return ty

buildStmtReturnType _ (StmtValueReturn ty) = return ty

buildStmtReturnType _ (StmtStateReturn ty v) = getStateType v

-- Now handle other cases
buildStmtReturnType stmt_pos return_spec =
  liftM AnfType $ mrv return_spec
  where
    -- Return the statement's result
    mrv (StmtValueReturn ty) = return $ fromAnfType ty
    
    -- Consume and return a state variable
    mrv (StmtStateReturn _ state_v) = do
      ty <- getStateType state_v
      return $ fromAnfType ty
    
    -- Construct a tuple
    mrv (StmtTupleReturn xs) = do
      -- Make the field values
      fields <- mapM mrv xs
      
      -- Construct the tuple type 
      let add_type_field field_ty type_expr =
            Binder' Nothing field_ty () Gluon.:*: type_expr
          tuple_type = foldr add_type_field Gluon.Unit fields
      
      return $ Gluon.mkTupTyE stmt_pos tuple_type

adaptStmtReturn :: StmtReturn   -- ^ Return spec of the given statement
                -> StmtReturn   -- ^ Desired return spec
                -> Anf.RStm     -- ^ Given statement
                -> ToAnf Anf.RStm -- ^ Adapted statement
adaptStmtReturn given_spec target_spec statement
  | sameStmtReturn given_spec target_spec =
      -- The statement already returns the right thing
      return statement
  | otherwise = traceShow (text "adaptStmtReturn " <+> pprStmtReturn given_spec <+> text "to" <+> pprStmtReturn target_spec) $
      unpack_stmt given_spec Nothing statement $ build_return_statement
    where
      -- Unpack 'stmt' according to the specification.  Generate a 'case' or
      -- 'let' expression that unpacks the statement and then executes the
      -- code generated by 'k'.
      unpack_stmt :: StmtReturn -> Maybe Var -> Anf.RStm
                  -> (Maybe Var -> ToAnf Anf.RStm)
                  -> ToAnf Anf.RStm
      unpack_stmt spec value_var stmt k =
        case spec
        of StmtValueReturn ty -> do
             -- The value variable should not have been defined before
             unless (isNothing value_var) $ internalError "adaptStmtReturn"

             -- Create a temporary variable to hold the value
             new_value_var <- Gluon.newAnonymousVariable ObjectLevel
             return_stmt <- k (Just new_value_var)

             -- Bind the input statement to the value variable, then execute
             -- the return statement
             let binder = Binder new_value_var (fromAnfType ty) ()
             return $ Anf.mkLetS binder stmt return_stmt

           StmtStateReturn _ state_v -> do
             -- Define the state variable
             defineStateVariable state_v
             tmp_v <- getStateVariableX "adaptStmtReturn" state_v
             tmp_t <- getStateType state_v

             -- Run the continuation, which should consume this state variable
             return_stmt <- k value_var
             
             -- Bind the input statement to the variable, then execute the
             -- return statement
             let binder = Binder tmp_v (fromAnfType tmp_t) ()
             return $ Anf.mkLetS binder stmt return_stmt
             
           StmtTupleReturn _ -> do
             -- Create a temporary variable to hold the value
             tmp_var <- Gluon.newAnonymousVariable ObjectLevel
             tmp_ty <- buildStmtReturnType (getSourcePos stmt) spec
             
             -- Use the unpacked variable  
             return_stmt <-
               unpack_value (getSourcePos stmt) spec value_var tmp_var k
             
             -- Bind the temporary variable
             let binder = Binder tmp_var (fromAnfType tmp_ty) ()
             return $ Anf.mkLetS binder stmt return_stmt

      unpack_value pos spec value_var var_exp k =
        case spec
        of StmtValueReturn ty -> do
             -- The value variable should not have been defined before
             unless (isNothing value_var) $ internalError "adaptStmtReturn"

             -- Pass this variable as the value variable.  There's no need
             -- to create additional code.
             k (Just var_exp)
             
           StmtStateReturn _ state_v -> do
             -- Assign this variable to be the state variable
             -- There's no need to create additional code.
             assignStateVariable state_v var_exp
             k value_var

           StmtTupleReturn fields -> do
             let num_fields = length fields
                 
             -- Create binders for all fields
             field_vars <- replicateM num_fields $
                           Gluon.newAnonymousVariable ObjectLevel

             field_types <- mapM (buildStmtReturnType pos) fields
             
             let binders = [Binder v ty () | v <- field_vars
                                           | AnfType ty <- field_types]
                 
             -- Create the return statement
             return_stmt <- unpack_fields pos fields field_vars value_var k
             
             -- Create a case statement
             let alternative = Anf.TupleAlt binders return_stmt
                 info = Gluon.mkSynInfo pos ObjectLevel
                 new_stmt = Anf.CaseS info (Anf.mkVarV pos var_exp) [alternative]
                 
             return new_stmt
             
      unpack_fields pos (field:fields) (var:vars) value_var k =
        unpack_value pos field value_var var $ \value_var' ->
        unpack_fields pos fields vars value_var' k
      
      unpack_fields pos [] [] value_var k = k value_var

      build_return_statement v =
        let pos = getSourcePos statement
            val = fmap (Gluon.mkVarE pos) v
        in do ret_val <- buildStmtReturnValueFrom pos target_spec val
              return $ Anf.mkReturnS ret_val

-- | Convert an ANF statement to a procedure.
--
-- The first parameter sets up the procedure's parameters, return value, and
-- context.  If the 
-- The procedure takes either the unit value or a state object as a 
-- parameter.  It returns either a return value or a state object.  Pure
-- variable inputs are referenced directly.
anfStmtToProc :: (forall a. ([StmtParam] -> StmtReturn -> ToAnf a) -> ToAnf a)
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
      params <- toAnfParameters ext_params
        
      -- Get effect type
      AnfType effect_type <- anfEffectType $ fexpEffect stm

      -- Create body; package the body's return value appropriately
      body <- anfStmt ext_return_spec stm
      
      -- Compute the return type
      (AnfType return_type) <-
        buildStmtReturnType (fexpSourcePos stm) ext_return_spec

      -- Return the new procedure
      let proc = Anf.Proc { Anf.procInfo = Gluon.mkSynInfo pos ObjectLevel
                          , Anf.procParams = params
                          , Anf.procReturnType = return_type
                          , Anf.procEffectType = effect_type
                          , Anf.procBody = body
                          }
      return (ext_return_spec, proc)

    pos = fexpSourcePos stm
    
    pair_type t1 t2 =
      Gluon.mkTupTyE pos $
      Binder' Nothing t1 () Gluon.:*: Binder' Nothing t2 () Gluon.:*: Gluon.Unit

anfAlternative :: FlatValAlt -> ToAnf (Anf.Alt Rec)
anfAlternative (FlatValAlt con ty_args params body) = do
  anfBindParameters params $ \params' -> do
    body' <- evalAnfStmt body
    return $ Anf.ConAlt (sfToAnfCon con) params' body'

-- | Convert a pass-by-reference case statement to ANF.
-- It is converted to a call to an elimination function.
anfCaseRef :: SourcePos -> Var -> RType -> Effect -> FlatReturn -> [FlatRefAlt]
           -> ToAnf Anf.RStm
anfCaseRef pos scrutinee_var scrutinee_type effect_info return_info alts = do
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

  -- Get effect and return types
  effect_type <- anfEffectType effect_info
  return_type <- case return_info
                 of ValueReturn ty -> convertType ty
                    ClosureReturn ty _ -> convertType ty
                    VariableReturn _ v -> getStateType v

  -- Determine what state variables are updated in the case statement
  (state_param, state_param_type) <- anfGetStmtStateInput pos return_info
  -- with_local_state $ \state_param state_return -> do
  
  -- Dispatch based on the data type that's being inspected
  scrutinee_type' <- liftPureToAnf $ evalHead' scrutinee_type
  case Gluon.unpackRenamedWhnfAppE scrutinee_type' of
    Just (con, args)
      | con `isPyonBuiltin` the_bool ->
          build_bool_case effect_type return_type state_param_type args state_param alternatives
      | con `isPyonBuiltin` the_PassConv ->
          build_PassConv_case effect_type return_type state_param_type args state_param alternatives
      | Just tuple_size <- whichPyonTupleTypeCon con ->
          build_tuple_case effect_type return_type state_param_type tuple_size args state_param alternatives
      | otherwise -> unrecognized_constructor con
    _ -> internalError $ "anfCaseRef: Unrecognized data type"
  where
    unrecognized_constructor con =
      let name = showLabel (Gluon.conName con)
      in internalError $ 
         "anfCaseRef: Unrecognized data type with constructor " ++ name

    lookupCon con_selector alternatives =
      case lookup (pyonBuiltin con_selector) alternatives
      of Just x -> x
         Nothing -> internalError "anfCaseRef: Missing case alternative"

    build_bool_case effect_type return_type state_param_type args st_param alternatives =
      let eliminator = Anf.mkInternalConV $ Anf.anfBuiltin Anf.the_elim_bool
          true_case = lookupCon the_True alternatives
          false_case = lookupCon the_False alternatives
          arguments = [ Anf.mkExpV (fromAnfType effect_type)
                      , Anf.mkExpV (fromAnfType state_param_type)
                      , Anf.mkExpV (fromAnfType return_type)
                      , Anf.mkLamV true_case
                      , Anf.mkLamV false_case
                      , st_param
                      ]
      in return $ Anf.mkCallAppS pos eliminator arguments
    
    build_PassConv_case effect_type return_type state_param_type args st_param alternatives =
      internalError "build_PassConv_case: not implemented"

    build_tuple_case effect_type return_type state_param_type size args st_param alternatives = do
      let eliminator =
            case size
            of 2 -> Anf.mkInternalConV $ Anf.anfBuiltin Anf.the_elim_PyonTuple2
          
          -- There is only one pattern to match against
          body = lookupCon (const $ getPyonTupleCon' size) alternatives
          
      -- Pass all type parameters to the eliminator
      ty_args <- mapM convertType $ map substFully args
          
      let elim_args = [ Anf.mkExpV (fromAnfType effect_type)
                      , Anf.mkExpV (fromAnfType state_param_type)
                      , Anf.mkExpV (fromAnfType return_type)
                      ] ++
                      map (Anf.mkExpV . fromAnfType) ty_args ++
                      [Anf.mkLamV body, st_param]
      return $ Anf.mkCallAppS pos eliminator elim_args

-- | Convert a by-reference alternative to a function.  The function arguments
-- are the parameters to the alternative.
anfRefAlternative :: SourcePos -> FlatRefAlt -> ToAnf (Con, Anf.Proc Rec)
anfRefAlternative pos (FlatRefAlt con _ params eff ret ret_ty body) = do
  (return_spec, proc) <- anfStmtToProc alternative_parameters body
  return (con, proc)
  where
    alternative_parameters k =
      -- Pass state in and out if required 
      withStmtReturnParameters True body $ \ret_params stmt_ret ->
      -- Make each object field be a function parameter
      sfToStmtParams params $ \stmt_params ->
        -- The alternative body gets the object fields as parameters 
        -- plus one extra parameter for input state
        k (stmt_params ++ ret_params) stmt_ret

anfStoreValue :: SourcePos -> RType -> Var -> Value -> ToAnf Anf.RStm
anfStoreValue pos ty dst val = do
  -- Storing a value will update the destination variable
  (dst_addr, dst_ptr, dst_st) <- getWriteReferenceVariables dst
  
  -- Generate a function call for the store
  create_store_statement dst_addr dst_ptr dst_st
  where
    create_store_statement dst_addr dst_ptr dst_st =
      case ty
      of Gluon.ConE {Gluon.expCon = c}
           | c `isPyonBuiltin` the_int ->
               case val
               of LitV (IntL n) ->
                    let literal = Gluon.mkLitE pos (Gluon.IntL n)
                        oper = Anf.anfBuiltin Anf.the_store_int
                    in store_literal oper literal
           | c `isPyonBuiltin` the_float ->
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
                                             then Anf.anfBuiltin Anf.the_TrueV
                                             else Anf.anfBuiltin Anf.the_FalseV
                        oper = Anf.anfBuiltin Anf.the_store_bool
                    in store_literal oper literal
           | c `isPyonBuiltin` the_NoneType ->
                 case val
                 of LitV NoneL ->
                      let literal =
                            Gluon.mkConE pos $ Anf.anfBuiltin Anf.the_NoneV
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
  AnfType anf_ty <- convertType ty
  pc <- getAnfPassConv ty
  (src_addr, src_ptr) <- getReadReferenceVariables src
  (dst_addr, dst_ptr, dst_st) <- getWriteReferenceVariables dst

  let con  = Anf.mkConV pos $ Anf.anfBuiltin Anf.the_copy
      args = [Anf.mkExpV anf_ty,       -- Object type to copy
              pc,                      -- Parameter passing info
              Anf.mkVarV pos src_addr, -- Source address
              Anf.mkVarV pos dst_addr, -- Destination address
              Anf.mkVarV pos src_ptr,  -- Source pointer
              Anf.mkVarV pos dst_ptr,  -- Destination pointer
              Anf.mkVarV pos dst_st]   -- Destination state
  return $ Anf.mkCallAppS pos con args

anfModule :: [[FlatDef]] -> ToAnf (Anf.Module Rec)
anfModule defss = liftM Anf.Module $ top_level_group defss
  where
    top_level_group (defs:defss) =
      liftM (uncurry (:)) $ anfDefGroup defs $ top_level_group defss
    top_level_group [] = return []