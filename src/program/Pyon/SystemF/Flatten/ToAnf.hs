
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

anfBinder' :: Maybe Var -> AnfType -> RBinder' ()
anfBinder' mv (AnfType t) = Binder' mv t ()

actionType :: AnfType -> AnfType -> AnfType
actionType (AnfType eff) (AnfType ret) =
  let action = Anf.anfBuiltin Anf.the_Action
  in AnfType $ Gluon.mkInternalConAppE action [eff, ret]
     
emptyEffect :: AnfType
emptyEffect = AnfType Gluon.Core.Builtins.Effect.empty

addrEffect :: Var -> AnfType -> AnfType
addrEffect v (AnfType obj_ty) =
  AnfType $ Gluon.mkInternalConAppE (Gluon.builtin Gluon.the_AtE) [obj_ty, Gluon.mkInternalVarE v]

anfEffectUnion :: [AnfType] -> AnfType
anfEffectUnion xs = AnfType $ foldr Gluon.Core.Builtins.Effect.sconj Gluon.Core.Builtins.Effect.empty $ map fromAnfType xs

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
      of Just (ValueVar {valueVar = v'}) -> v'
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

-- | Get the parameter-passing convention for this type.  The type parameter
-- is a System F type, not an ANF type.
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

-- | Extend the environment with a specificaiton of how to translate a 
-- variable from System F to ANF.
withVariableElaboration :: Var -> VarElaboration -> ToAnf a -> ToAnf a
withVariableElaboration v elaboration (ToAnf m) =
  ToAnf $ local add_elaboration m
  where
    add_elaboration env =
      env {anfVariableMap =
              Map.insert (varID v) elaboration $ anfVariableMap env}

-- | Define the variable as a value variable
withValueVariable :: Var -> RType -> ToAnf a -> ToAnf a
withValueVariable v ty k = do
  v' <- Gluon.duplicateVar v
  ty'@(AnfType anf_type) <- convertType ty
  withVariableElaboration v (ValueVar {valueVar = v', valueType = ty'}) $
    assumePure v' anf_type k

-- | Define the variable as a closure variable.  Use the given type, which 
-- is an ANF type.
withClosureVariableAnf :: Var -> AnfType -> ToAnf a -> ToAnf a
withClosureVariableAnf v (AnfType anf_type) k = do
  v' <- Gluon.duplicateVar v
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

withStateVariable :: Var -> ToAnf a -> ToAnf a
withStateVariable v (ToAnf m) = ToAnf $ do
  -- Create a new state variable
  new_v <- lift $ Gluon.newVar (varName v) ObjectLevel

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
       v' <- getValueVariable v
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
         real_v <- getValueVariable v
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
              real_v <- getValueVariable v
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
      return $ AnfType $ foldr mk_fun range binders
  where
    pos = getSourcePos expression

    mk_fun param range =
      Gluon.FunE { Gluon.expInfo = Gluon.internalSynInfo (getLevel range)
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
           deconstruct_function_type ((dom :) . hd) rng
         Gluon.FunE {Gluon.expMParam = Binder' (Just _) _ ()} ->
           traceShow (Gluon.pprExp function_type) $ internalError "convertMonoClosureType: Unexpected dependent type"
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
       | mode == IOVal || mode == IOClo -> do
           real_v <- getValueVariable v
           return $ Anf.mkVarV pos real_v
       | otherwise -> internalError "anfValue"
     ConV c mode 
       | mode == IOVal || mode == IOClo -> do
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
  addr_values <- mapMaybeM convert_address values
  val_values <- mapM convert_value values
  st_values <- mapMaybeM convert_state values
  return $ addr_values ++ val_values ++ st_values
  where
    convert_address value = 
      case value
      of VarV v mode ->
           case mode
           of IOVal -> return Nothing
              IOClo -> return Nothing
              InRef -> addr_param v
              OutRef -> addr_param v
         ConV c mode ->
           case mode
           of IOVal -> return Nothing
              IOClo -> return Nothing
              InRef -> can't_convert value
              OutRef -> can't_convert value
         LitV _ -> return Nothing
         TypeV _ -> return Nothing
         FunV _ -> return Nothing
         AppV _ _ -> return Nothing

    -- For pass-by-reference data, pass a pointer 
    -- For other data, pass the value
    convert_value value =
      case value
      of VarV v InRef  -> pointer_param v
         VarV v OutRef -> pointer_param v
         _             -> anfValue pos value
         
    convert_state value = 
      case value
      of VarV v mode ->
           case mode
           of IOVal -> return Nothing
              IOClo -> return Nothing
              InRef -> return Nothing
              OutRef -> state_param v
         _ -> return Nothing    -- State parameters are only for return values

    addr_param v = do
      real_v <- getAddrVariable v
      return $ Just $ Anf.mkVarV pos real_v

    value_param v = do
      real_v <- getValueVariable v
      return $ Just $ Anf.mkVarV pos real_v

    pointer_param v = do
      real_v <- getPointerVariable v
      return $ Anf.mkVarV pos real_v

    state_param v = do
      real_v <- getStateVariable v
      return $ Just $ Anf.mkVarV pos real_v
    
    can't_convert value =
      internalError "anfArguments: Can't convert value"

-- | Get the ANF type of a function.
--
-- The translation from binders to arrow types in this function matches
-- the translation from binders to binders in 'anfBindParameters'.
anfFunctionType :: FlatFun -> ToAnf AnfType
anfFunctionType ffun = anfCreateParameterMaps (ffunParams ffun) $ do
  addr_domain <- mapMaybeM convert_address (ffunParams ffun)
  val_domain <- mapM convert_value (ffunParams ffun)
  st_domain <- mapMaybeM convert_state (ffunParams ffun)
  effect <- liftM anfEffectUnion $ mapM get_effect (ffunParams ffun)
  (addr_range, val_range, st_range, ret_range) <-
    convert_return (ffunReturnType ffun)
  let AnfType anf_ret_ty = actionType effect ret_range
  return $ AnfType $ foldr ($) anf_ret_ty (addr_domain ++ maybeToList addr_range ++ val_domain ++ maybeToList val_range ++ st_domain ++ maybeToList st_range)
  where
    pos = getSourcePos (ffunInfo ffun)
    
    get_effect (Binder v ty d_mode) =
      case d_mode
      of IOVal -> return emptyEffect
         IOVal -> return emptyEffect
         InRef -> getEffectType v
         OutRef -> return emptyEffect

    convert_address (Binder v ty d_mode) =
      case d_mode
      of IOVal -> return Nothing
         IOClo -> return Nothing
         InRef -> address_parameter v
         OutRef -> address_parameter v
      
    convert_value (Binder v ty d_mode) =
      case d_mode
      of IOVal -> value_parameter v
         IOClo -> value_parameter v
         InRef -> pointer_parameter v
         OutRef -> pointer_parameter v

    convert_state (Binder v ty d_mode) =
      case d_mode
      of IOVal -> return Nothing
         IOClo -> return Nothing
         InRef -> return Nothing
         OutRef -> state_parameter v

    convert_return rt = do
      (anf_addr, anf_val, anf_st, anf_rt) <- convertClosureReturn rt return
      let make_function_type param rng = 
            Gluon.FunE (Gluon.mkSynInfo pos ObjectLevel) False param rng
      return (fmap make_function_type anf_addr,
              fmap make_function_type anf_val,
              fmap make_function_type anf_st,
              anf_rt)

    -- Address parameters are always used dependently
    address_parameter v = do
      real_v <- getValueVariable v
      AnfType real_t <- getValueType v
      return $ Just $ \rng -> Gluon.mkFunE pos False real_v real_t rng

    -- Value parameters may or may not be used dependently
    value_parameter v = do
      real_v <- getValueVariable v
      AnfType real_t <- getValueType v
      return $ \rng -> if rng `Gluon.mentions` real_v
                       then Gluon.mkFunE pos False real_v real_t rng
                       else Gluon.mkArrowE pos False real_t rng
    
    -- Pointer parameters are never used dependently
    pointer_parameter v = do
      AnfType real_t <- getPointerType v
      return $ \rng -> Gluon.mkArrowE pos False real_t rng
      
    -- State parameters are never used dependently
    state_parameter v = do
      AnfType real_t <- getUndefStateType v
      return $ Just $ \rng -> Gluon.mkArrowE pos False real_t rng

anfProc :: FlatFun -> ToAnf (Anf.Proc Rec)
anfProc ffun = hideState $
  -- Convert function parameters and make a local parameter mapping
  anfBindParameters (ffunParams ffun) $ \params -> do
    -- Convert effect type
    AnfType et <- anfEffectType (ffunEffect ffun)
    
    -- Get return type
    AnfType rt <-
      case returnMode $ ffunReturn ffun
      of IOVal -> convertType $ returnType $ ffunReturn ffun
         IOClo -> convertType $ returnType $ ffunReturn ffun
         OutRef -> case return_variable
                   of Just v -> getStateType v
                      Nothing -> internalError "anfProc"

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
        is_return_parameter (Binder _ _ OutRef) = True
        is_return_parameter _ = False

    pos = getSourcePos (ffunInfo ffun)

anfCreateParameterMaps :: [RBinder DataMode] -> ToAnf a -> ToAnf a
anfCreateParameterMaps params k =
  foldr ($) k $ map anfCreateParameterMap params
               
-- | Create variable elaboration information for a parameter.
-- Skip pointer and state parameters; handle them when the address 
-- parameter is encountered.
anfCreateParameterMap :: RBinder DataMode -> ToAnf a -> ToAnf a
anfCreateParameterMap (Binder v ty data_mode) k =
      case data_mode
      of IOVal -> withValueVariable v ty k
         IOClo -> withValueVariable v ty k
         InRef -> withReferenceVariable v ty k
         OutRef -> withReferenceVariable v ty $ withStateVariable v k

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
    addr_params <- mapMaybeM convert_address params
    val_params <- mapMaybeM convert_value params
    st_params <- mapMaybeM convert_state params
    let all_params = addr_params ++ val_params ++ st_params
    k all_params
  where

    convert_address (Binder v ty d_mode) =
      case d_mode
      of IOVal -> return Nothing
         IOClo -> return Nothing
         InRef -> address_parameter v
         OutRef -> address_parameter v
    
    convert_value (Binder v ty d_mode) =
      case d_mode
      of IOVal -> value_parameter v
         IOClo -> value_parameter v
         InRef -> pointer_parameter v
         OutRef -> pointer_parameter v

    convert_state (Binder v ty d_mode) =
      case d_mode
      of IOVal -> return Nothing
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
      real_v <- getStateVariable v
      AnfType real_t <- getUndefStateType v
      return $ Just $ Binder real_v real_t ()

-- | Compute the effect type corresponding to this effect.    
anfEffectType :: Effect -> ToAnf AnfType
anfEffectType eff = do
  types <- mapM getEffectType' $ effectVars eff
  return $ AnfType $ foldr
    Gluon.Core.Builtins.Effect.sconj
    Gluon.Core.Builtins.Effect.empty
    (map fromAnfType types)

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
      withClosureVariableAnf v ty k

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
       args' <- anfArguments pos args
       return $ Anf.CallS anf_info $ Anf.AppV anf_info op' args'
     LetS {fexpBinder = Binder v ty _, fexpRhs = rhs, fexpBody = body} -> do
       rhs' <- anfStmt rhs
       (anf_v, anf_ty, body') <- withValueVariable v ty $ do 
         anf_v <- getValueVariable v
         AnfType anf_ty <- getValueType v
         body' <- anfStmt body
         return (anf_v, anf_ty, body')
       
       return $ Anf.LetS anf_info (Binder anf_v anf_ty ()) rhs' body'
     EvalS {fexpRhs = rhs, fexpBody = body} ->
       case fexpReturn rhs
       of VariableReturn _ v -> do
            rhs' <- anfStmt rhs
            state_v <- getStateVariableX "evalS" v
            AnfType state_ty <- getStateType v
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
anfReading pos _ return_info var body = do
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
                                        , Anf.mkExpV (fromAnfType obj_type)
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
  -- Convert the local object's type to its ANF equivalent
  obj_type <- convertType ty

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
                                      , Anf.mkExpV (fromAnfType obj_type)
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
                     , Binder local_st (fromAnfType input_st_type) ()
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
    value_return sf_ty = do 
      anf_ty <- convertType sf_ty
      k [] (StmtValueReturn anf_ty)
    
    -- If returning a state variable, then set up the environment,
    -- create a parameter, and indicate that it shall be returned.
    variable_return _ v = withStateVariable v $ do
      -- Create binder and return type of this variable
      AnfType param_type <- getUndefStateType v
      input_state_var <- getStateVariableX "anfGetStmtReturnParameter" v
      let binder = Binder input_state_var param_type ()
       
      return_type <- getStateType v

      -- Run the main computation
      k [binder] (StmtStateReturn return_type v)

-- | The return specification for a procedure created by 'anfStmtToProc'.
-- This specifies what ANF data type to return and what data it contains.
data StmtReturn =
    StmtValueReturn AnfType       -- ^ The return value of the statement
  | StmtStateReturn AnfType !Var  -- ^ A state variable
  | StmtTupleReturn [StmtReturn]  -- ^ A tuple of things

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
                     -> ToAnf (AnfType, Anf.RStm)

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
  stmt_result_var <- Gluon.newAnonymousVariable ObjectLevel
  AnfType anf_return_type <- convertType $ returnType ret
  let result_binder = Binder stmt_result_var anf_return_type ()
   
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
    make_return_value stmt_result_var return_spec = do
      (val, ty) <- mrv return_spec
      return (val, AnfType ty)
      where
        -- Return the statement's result
        mrv (StmtValueReturn ty) =
          return (Gluon.mkVarE stmt_pos stmt_result_var, fromAnfType ty)
        
        -- Consume and return a state variable
        mrv (StmtStateReturn _ state_v) = do
          v <- getStateVariableX "buildStmtReturnValue" state_v
          ty <- getStateType state_v
          consumeStateVariable state_v
          return (Gluon.mkVarE stmt_pos v, fromAnfType ty)
        
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
      AnfType effect_type <- anfEffectType $ fexpEffect stm

      -- Create body
      body <- anfStmt stm
      
      -- Construct the return expression
      (AnfType return_type, body') <-
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
  -- Use 'Int -> Int' as a dummy return type here
  anfBindParameters params $ \params' -> do
    body' <- anfStmt body
    return $ Anf.Alt (sfToAnfCon con) params' body'

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
  return (sfToAnfCon con, proc)
  where
    alternative_parameters k =
      -- Pass state in and out if required 
      anfGetStmtReturnParameter body $ \stmt_params stmt_ret ->
      -- Make each object field be a function parameter
      anfBindParameters params $ \anf_params -> do
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