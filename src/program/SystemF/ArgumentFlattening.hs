{-| The argument flattening transformation makes parameter passing more
    efficient by changing the format in which function arguments are passed.

Functions are replaced by a worker/wrapper pair.  The worker function
takes arguments in a flattened form, repacks them, and runs the function body.
The wrapper function takes arguments
in the original, packed form, and unpacks them for the worker.

After argument unpacking, the compiler will inline wrapper functions where
possible to eliminate argument packing in callers, and perform case elimination
to eliminate repacking inside workers.
-}

{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}
module SystemF.ArgumentFlattening(flattenArguments, flattenLocals)
where

import Prelude hiding (mapM)

import Control.Monad.Reader hiding(mapM)
import qualified Data.IntMap as IntMap
import Data.List
import Data.Maybe
import Data.Traversable
import qualified Data.Set as Set
import Debug.Trace
  
import Common.Error
import Common.Identifier
import Common.Supply
import Builtins.Builtins
import SystemF.Demand
import SystemF.Floating
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import SystemF.ReprDict
import Type.Compare
import Type.Environment
import Type.Eval
import Type.Rename
import Type.Type
import Globals
import GlobalVar

-- | Reader environment used during argument flattening and local variable
--   flattening.
data AFLVEnv a =
  AFLVEnv
  { afVarSupply :: {-# UNPACK #-}!(IdentSupply Var)
  , afTypeEnv :: TypeEnv
  , afDictEnv :: MkDictEnv
  , afIntIndexEnv :: IntIndexEnv
  , afOther :: a
  }

-- | During local variable flattening, keep track of the mapping between
--   local variables and their unpacked form
type LocalVarEnv = IntMap.IntMap WrapRet

-- | The monad for argument and local variable flattening
newtype AFMonad e a =
  AF {unAF :: ReaderT (AFLVEnv e) IO a} deriving(Monad, MonadIO)

-- | The argument flattening monad
type AF = AFMonad ()

-- | The local variable flattening monad
type LF = AFMonad LocalVarEnv

instance Supplies (AFMonad e) (Ident Var) where
  fresh = AF $ ReaderT $ \env -> supplyValue $ afVarSupply env

liftFreshVarAF :: FreshVarM a -> AFMonad e a
liftFreshVarAF m = AF $ ReaderT $ \env -> runFreshVarM (afVarSupply env) m

instance ReprDictMonad (AFMonad e) where
  getVarIDs = AF $ asks afVarSupply
  getTypeEnv = AF $ asks afTypeEnv
  getDictEnv = AF $ asks afDictEnv
  getIntIndexEnv = AF $ asks afIntIndexEnv
  localDictEnv f m =
    AF $ local (\env -> env {afDictEnv = f $ afDictEnv env}) $ unAF m
  localIntIndexEnv f m =
    AF $ local (\env -> env {afIntIndexEnv = f $ afIntIndexEnv env}) $ unAF m

unifyTypeWithPatternAF :: [Var]   -- ^ Free variables in expected type
                       -> Type    -- ^ Expected type
                       -> Type    -- ^ Given type
                       -> AFMonad e (Maybe Substitution)
unifyTypeWithPatternAF fvs etype gtype = AF $ ReaderT $ \env ->
  unifyTypeWithPattern (afVarSupply env) (afTypeEnv env) fvs etype gtype

assumeTyPat :: TyPatM -> AFMonad e a -> AFMonad e a
assumeTyPat (TyPatM tyvar kind) m = AF $ local insert_type $ unAF m
  where
    insert_type env =
      env {afTypeEnv = insertType tyvar (ValRT ::: kind) $ afTypeEnv env}

assumeTyPats :: [TyPatM] -> AFMonad e a -> AFMonad e a
assumeTyPats typats m = foldr assumeTyPat m typats

assumePat :: PatM -> AFMonad e a -> AFMonad e a
assumePat pat m = AF $ local insert_type $ unAF $ saveReprDictPattern pat m
  where
    pat_var = patMVar' pat
    insert_type =
      case pat
      of MemVarP {} -> \env ->
           env {afTypeEnv = insertType pat_var (patMReturnType pat) $ afTypeEnv env}
         MemWildP {} -> id
         LocalVarP {} -> internalError "assumePat"

assumePats :: [PatM] -> AFMonad e a -> AFMonad e a
assumePats pats m = foldr assumePat m pats

withUnpackedLocalVariable :: WrapRet -> LF a -> LF a
withUnpackedLocalVariable wrapped_local m 
  | isIdRet wrapped_local = m
  | WrapRet pat _ wr <- wrapped_local =
      let var_id = fromIdent $ varID $ patMVar' pat
          ins env = env {afOther = IntMap.insert var_id wrapped_local
                                   $ afOther env}
      in AF $ local ins $ unAF m

lookupUnpackedLocalVariable :: Var -> LF (Maybe WrapRet)
lookupUnpackedLocalVariable v = AF $ asks (lookup_var . afOther)
  where
    lookup_var m = IntMap.lookup (fromIdent $ varID v) m

deleteUnpackedLocalVariable :: Var -> LF a -> LF a
deleteUnpackedLocalVariable v m = AF $ local delete_var $ unAF m
  where
    delete_var env =
      env {afOther = IntMap.delete (fromIdent $ varID v) $ afOther env}

-------------------------------------------------------------------------------
-- Argument flattening and code generation, driven by function parameter types 

-- | What is being flattened.  The decision of whether to flatten is made
--   differently depending on what is being flattened.
--
--   'ReturnField' is a field of a return value or local variable that can be
--   at least partially flattened.
data What = Parameter | Return | Local | ReturnField deriving(Eq)

fieldWhat :: What -> What

-- Flattened parameters follow the same flattening rules as parameters
fieldWhat Parameter = Parameter

-- Other data types place restrictions on what can go into a field
fieldWhat Return = ReturnField
fieldWhat Local = ReturnField
fieldWhat ReturnField = ReturnField

-- | Is the type constructor's natural representation 'Value'?
naturalValueTyCon :: TypeEnv -> Var -> Bool
naturalValueTyCon tenv con =
  case lookupDataType con tenv
  of Just dtype -> dataTypeRepresentation dtype == Value
     Nothing -> False

naturalValueTyConAF :: Var -> AFMonad e Bool
naturalValueTyConAF con = do
  tenv <- getTypeEnv
  return $ naturalValueTyCon tenv con

-- | If the parameter is a type constructor that has a single data constructor,
--   return its type and data constructors
fromSingletonTyCon :: TypeEnv -> Var -> Maybe (DataType, DataConType)
fromSingletonTyCon tenv ty_op =
  case lookupDataType ty_op tenv
  of Nothing -> Nothing
     Just data_type ->
       case dataTypeDataConstructors data_type
       of [con] ->
            case lookupDataCon con tenv
            of Just dcon_type -> Just (data_type, dcon_type)
               Nothing -> internalError "fromSingletonTyCon"
          _ -> Nothing

-- | Argument flattening information attached to a variable binder
data WrapPat = WrapPat !PatM !WrapPat'
  
isIdWrapper (WrapPat _ (IdWP _)) = True
isIdWrapper _ = False

-- | How to unwrap a function parameter 
data WrapPat' =
    -- | Parameter is unchanged.  If it's passed by reference, a
    --   reprentation dictionary is attached so we know how to copy it.
    IdWP !(Maybe ExpM)

    -- | Parameter value is deconstructed.  The existential types and fields
    --   are passed as individual parameters.
    --
    --   Other than in parameters, existential types and non-value fields 
    --   are not permitted.
  | DeconWP !DeconRepr !Var [TypM] [TyPatM] [WrapPat]

    -- | Parameter value is loaded (either by value or boxed) into a new
    --   variable.  Also, save the type's representation dictionary.
  | LoadWP !Repr ExpM !Var

    -- | Parameter value or field is dead, and is not passed at all.
    --
    --   This mode may not be used for a return value or local variable.
    --   Nonetheless it may be used for a field of a return value or
    --   local variable.
  | DeadWP ExpM

-- | True if all unpacked fields of the pattern are values
unpacksToAValue :: ReturnType -> WrapPat' -> Bool
unpacksToAValue (rrepr ::: _) wpat =
  case wpat
  of IdWP _              -> case rrepr
                            of {ValRT -> True; _ -> False}
     -- Deconstructed patterns must have no existentials and only
     -- acceptable fields
     DeconWP _ _ _ [] fs -> all unpacks' fs
     DeconWP _ _ _ _  _  -> False
     LoadWP Value _ _    -> True
     LoadWP _     _ _    -> False
     DeadWP _            -> False
  where
    unpacks' (WrapPat pat wp) = unpacksToAValue (patMReturnType pat) wp

-- | How to unwrap a function's return parameter.  If the function doesn't 
--   write into its destination (that is, there's no return parameter), we
--   make no attempt to unwrap the return value.
--
--   In some cases, the unpacked value needs to be assigned to a temporary 
--   variable.  A temporary variable is included here for that purpose.
--   If the unwrapping is a 'LoadWP', then 
data WrapRet = WrapRet !PatM !Var !WrapPat'
             | NoWrapRet        -- ^ Function doesn't have a return parameter

-- | True if the wrapper specification says not to change the function's
--   return value.
isIdRet :: WrapRet -> Bool
isIdRet NoWrapRet = True
isIdRet (WrapRet _ _ (IdWP _)) = True
isIdRet _ = False

{-
data WrapRet' =
    -- | Return value is unchanged
    IdWR

    -- | Return value is stored into a temporary variable after returning.
  | StoreWR !Repr ExpM
    
    -- | Fields of the return value are passed as an unboxed tuple.
    --   Keep track of the original return data contructor so that it
    --   can be reboxed.
    --   Existential types are not allowed in the return data constructor.
    --
    --   The dictionary for this type is also saved.
  | UnboxedWR !ExpM !Var [TypM] [WrapPat]-}

-- | Representation of an object that should be deconstructed.
--   If it is passed by reference, its representation dictionary is needed
--   so it can be locally allocated.
data DeconRepr = DeconValue | DeconBoxed | DeconReferenced ExpM

-- | Wrap a sequence of patterns.  Variables bound by earlier patterns are
--   available in the scope of later patterns.
wrapPatterns :: What -> [PatM] -> AFMonad e [WrapPat]
wrapPatterns what (pat:pats) = do
  wrap_pat <- wrapPattern what pat
  wrap_pats <- assumePat pat $ wrapPatterns what pats
  return (wrap_pat : wrap_pats)

wrapPatterns _ [] = return []

-- | Decide how to pass one of the original function's parameters to the 
--   worker.
wrapPattern :: What -> PatM -> AFMonad e WrapPat
wrapPattern what pat = do
  wrapping <- wrapPattern' what pat (specificity $ patMDmd pat)
  return $ WrapPat pat wrapping

wrapPattern' :: What -> PatM -> Specificity -> AFMonad e WrapPat'
wrapPattern' what pat pattern_specificity =
  case pat
  of MemVarP {} -> do
       -- Rename existential type variables so that they don't produce
       -- name conflicts after generating code from the demand type
       spc <- freshen pattern_specificity
       wrap_var_pattern spc
     MemWildP {} -> dead
     LocalVarP {} ->
       internalError "wrapPattern: Unexpected pattern"
  where
    -- No use information is available
    wrap_var_pattern Used =
      case what
      of Return ->
           case fromVarApp $ patMType pat
           of Just (con, args) -> do
                loadable <- naturalValueTyConAF con
                if loadable
                  then loaded Value (patMType pat)
                  else unchanged
              Nothing -> unchanged
         _ -> unchanged
    
    -- The variable will be loaded from memory.  We always want to flatten it.
    wrap_var_pattern (Loaded repr ty _) = loaded repr ty

    -- The variable is dead.
    -- If it's a parameter or a field of a local variable, eliminate it.
    wrap_var_pattern Unused =
      case what
      of Parameter -> dead
         ReturnField -> dead
         _ -> unchanged

    -- The variable is deconstructed.  We always want to flatten it.
    -- However, we are limited in what we can flatten in return values and 
    -- local variables; if flattening is impossible, leave it unchanged.
    wrap_var_pattern (Decond con ty_args ex_types spcs) = do
      tenv <- getTypeEnv
      case lookupDataConWithType con tenv of
        Just (data_type, dcon_type) -> do
          mx <- deconPattern what data_type dcon_type con ty_args ex_types spcs
          case mx of
            Nothing -> unchanged
            Just x -> return x
        Nothing ->
          internalError "wrapPattern: Deconstructed unknown type"

    wrap_var_pattern Inspected =
      -- Is this a data type with a single constructor,
      -- or a loadable data type?
      let ty = patMType pat
      in case fromVarApp ty
         of Just (ty_op, ty_args) -> do
              tenv <- getTypeEnv
              case fromSingletonTyCon tenv ty_op of
                Just (data_type, dcon_type) -> do
                  mx <- deconSingletonPattern what data_type dcon_type ty_args
                  case mx of
                    Nothing -> unchanged
                    Just x  -> return x
                Nothing ->
                  if naturalValueTyCon tenv ty_op
                  then loaded Value ty
                  else unchanged
            Nothing -> unchanged

    unchanged =
      case patMRepr pat
      of ReadPT -> do
           dict <- withReprDict (patMType pat) return
           return $ IdWP (Just dict)
         _ -> return $ IdWP Nothing

    dead = do
      dict <- withReprDict (patMType pat) return
      return $ DeadWP dict

    loaded repr ty = do
      loaded_var <- newAnonymousVar ObjectLevel
      dict <- withReprDict ty return
      return $ LoadWP repr dict loaded_var

-- | Deconstruct a pattern variable, given the deconstruction demand that was
--   placed on it
deconPattern :: What
             -> DataType
             -> DataConType
             -> Var             -- ^ Constuctor to deconstruct
             -> [Type]          -- ^ Type arguments
             -> [(Var, Type)]   -- ^ Existential types
             -> [Specificity]   -- ^ Demand on fields
             -> AFMonad e (Maybe WrapPat')
deconPattern what data_type dcon_type con ty_args ex_types spcs
  | what /= Parameter && not (null ex_types) =
      -- Cannot deconstruct existential types in this position
      return Nothing

  | otherwise = do
  let ex_pats = [TyPatM v t | (v, t) <- ex_types]
      data_con_args = ty_args ++ map (VarT . fst) ex_types
      (field_rtypes, instantiated_rtype) =
        instantiateDataConTypeWithExistentials dcon_type data_con_args
  
  when (length spcs /= length field_rtypes) $
    internalError "dconPattern: Inconsistent number of parameters"
  
  -- Create patterns and decide how to further deconstruct each field
  m_fields <- deconPatternFields what ex_pats (zip field_rtypes spcs)
  case m_fields of
    Nothing -> return Nothing
    Just fields -> do
      -- Determine the pattern's representation
      repr <- instantiatedReprDict instantiated_rtype

      return $ Just $ DeconWP repr con (map TypM ty_args) ex_pats fields
  where
    -- Decide whether the unwrapped field is allowed here.
    -- In non-parameter positions, the unwrapped field must be representable
    -- as a value.
    acceptable_field =
      case what
      of Parameter -> \_            -> True
         _         -> \(rtype, fld) -> unpacksToAValue rtype fld

instantiatedReprDict :: ReturnType -> AFMonad e DeconRepr
instantiatedReprDict (ValRT ::: _) = return DeconValue
instantiatedReprDict (BoxRT ::: _) = return DeconBoxed
instantiatedReprDict (ReadRT ::: ty) =
  liftM DeconReferenced $ withReprDict ty return

-- | Deconstruct a singleton pattern, given the data type constructor and
--   its arguments.  The proper arguments to the data constructor are
--   determined by instantiating the constructor's type, then unifying it
--   with the pattern type.
deconSingletonPattern :: What
                      -> DataType
                      -> DataConType
                      -> [Type]
                      -> AFMonad e (Maybe WrapPat')
deconSingletonPattern what data_type dcon_type type_arguments 
  | what /= Parameter && num_existential_types /= 0 =
      -- Cannot deconstruct existential types in this position
      return Nothing

  | otherwise = do
      -- Instantiate the data constructor with fresh type variables
      inst_a_types <- new_variables num_universal_types
      inst_e_types <- new_variables num_existential_types
      let (ex_params, fields, inst_repr ::: inst_type) =
            instantiateDataConType dcon_type (map VarT inst_a_types) inst_e_types
  
      -- Unify with the actual type
      let actual_type = varApp (dataConTyCon dcon_type) type_arguments
          ex_types = [TyPatM v ty | ValPT (Just v) ::: ty <- ex_params]
      m_u_subst <- unifyTypeWithPatternAF inst_a_types inst_type actual_type
      u_subst <- case m_u_subst
                 of Just s -> return s
                    Nothing -> internalError "deconSingletonPattern"

      -- Apply substitution to the type arguments
      let actual_a_types = map instantiate_var inst_a_types
            where
              instantiate_var v =
                case substituteVar v u_subst
                of Just t -> t
                   Nothing -> internalError "deconSingletonPattern"

      -- Process the data type's fields.
      -- We have no information about the demand, so assume 'Used'.
      let actual_fields = map (substituteBinding u_subst) fields
      m_field_wrappers <-
        deconPatternFields what ex_types (zip actual_fields $ repeat Used)
      case m_field_wrappers of
        Nothing -> return Nothing
        Just field_wrappers -> do
          -- Construct the return value
          repr <- instantiatedReprDict (inst_repr ::: actual_type)
          let ty_args = map TypM actual_a_types
          return $ Just $
            DeconWP repr (dataConCon dcon_type) ty_args ex_types field_wrappers
  where
    new_variables n = replicateM n (newAnonymousVar TypeLevel)
    num_universal_types = length $ dataConPatternParams dcon_type
    num_existential_types = length $ dataConPatternExTypes dcon_type

-- | Wrap the fields of a deconstructeded pattern variable.
deconPatternFields :: What      -- ^ How the enclosing object is used
                   -> [TyPatM]  -- ^ Existential types
                   -> [(ReturnType, Specificity)] -- ^ Fields
                   -> AFMonad e (Maybe [WrapPat])
deconPatternFields what ex_pats fields = do
  fields' <- assumeTyPats ex_pats $ mapM decon_field fields
  return $
    if all acceptable_field fields' then Just fields' else Nothing
  where
    decon_field (rrepr ::: rtype, spc) = do
      pat_var <- newAnonymousVar ObjectLevel
      let pattern =
            setPatMDmd (Dmd bottom spc) $
            memVarP pat_var (returnReprToParamRepr rrepr ::: rtype)
      wrapPattern (fieldWhat what) pattern

    -- Decide whether the unwrapped field is allowed here.
    -- In non-parameter positions, the unwrapped field must be representable
    -- as a value.
    acceptable_field =
      case what
      of Parameter -> \_ -> True
         _ -> \(WrapPat pat fld) -> unpacksToAValue (patMReturnType pat) fld

-- | Generate code to unwrap a parameter.  The code takes the original, 
--   wrapper parameter and exposes the worker parameters via let or
--   case statements.
unwrapPattern :: WrapPat -> Context
unwrapPattern (WrapPat pat wrap_spec) =
  case wrap_spec
  of IdWP _ -> []

     DeconWP dc_repr con ty_args ex_types fields ->
       unwrapDeconPat scrutinee dc_repr con ty_args ex_types fields

     LoadWP Value _ dst_var ->
       let pattern = memVarP dst_var (ValPT Nothing ::: patMType pat)
           load_exp = ExpM $ AppE defaultExpInfo load_op [TypM $ patMType pat]
                      [scrutinee]
       in [contextItem $ LetCtx defaultExpInfo pattern load_exp]
  
     LoadWP Boxed _ dst_var ->
       let pattern = memVarP dst_var (BoxPT ::: patMType pat)
           load_exp = ExpM $ AppE defaultExpInfo loadBox_op [TypM $ patMType pat]
                      [scrutinee]
       in [contextItem $ LetCtx defaultExpInfo pattern load_exp]

     DeadWP _ -> []
  where
    -- The unwrapping code extracts values from the variable defined
    -- in the original pattern
    scrutinee = ExpM $ VarE defaultExpInfo (patMVar' pat)
    load_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_load)
    loadBox_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_loadBox)

-- | Unwrap a deconstructed pattern.  Produce a case statement.
unwrapDeconPat scrutinee dc_repr con ty_args ex_types fields =
  let field_contexts = map unwrapPattern fields
      ctx = contextItem $ CaseCtx defaultExpInfo scrutinee
            con ty_args ex_types [pat | WrapPat pat _ <- fields]
  in concat field_contexts ++ [ctx]

-- | Generate code to rewrap a parameter.  Given the unwrapped values,
--   produce the original parameter value.
rewrapPattern :: WrapPat -> (Context, ExpM)
rewrapPattern (WrapPat pat wrap_spec) =
  case wrap_spec
  of IdWP mdict ->
       let copy_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_copy)
           param_exp =
             -- If this is a read parameter, then we need to copy it
             case patMRepr pat
             of ValPT _ -> pattern_var_exp
                BoxPT   -> pattern_var_exp
                ReadPT  ->
                  let Just dict = mdict
                  in ExpM $ AppE defaultExpInfo copy_op [TypM $ patMType pat]
                     [dict, pattern_var_exp]
       in ([], param_exp)
     
     DeconWP dc_repr con ty_args ex_types fields ->
       (rewrapDeconPat pat dc_repr con ty_args ex_types fields,
        pattern_var_exp)
     
     LoadWP repr dict dst_var ->
       -- Undo a load by storing the variable 
       --
       -- > let pat_var = store(dst_var, pat_var)
       let pattern = localVarP (patMVar' pat) (patMType pat) dict
           store = case repr
                   of Value -> store_op
                      Boxed -> storeBox_op
           store_exp = ExpM $ AppE defaultExpInfo store
                       [TypM $ patMType pat]
                       [ExpM $ VarE defaultExpInfo dst_var, pattern_var_exp]
       in ([contextItem $ LetCtx defaultExpInfo pattern store_exp],
           pattern_var_exp)

     DeadWP dict ->
       -- This variable is not used, so its value is unimportant.
       -- Materialize a value.
       let op =
             case patMRepr pat
             of ValPT Nothing -> internalError "rewrapPattern: Not implemented"
                BoxPT -> deadBox_op
                ReadPT -> deadRef_op
           exp = ExpM $ AppE defaultExpInfo op [TypM $ patMType pat] []
       in ([contextItem $ LetCtx defaultExpInfo pat exp], pattern_var_exp)
  where
    pattern_var_exp = ExpM $ VarE defaultExpInfo (patMVar' pat)
    store_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_store)
    storeBox_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_storeBox)
    deadBox_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_deadBox)
    deadRef_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_deadRef)

rewrapDeconPat pat dc_repr con ty_args ex_types fields =
  -- Undo a case statement by constructing a value
  let (field_contexts, field_exprs) = unzip $ map rewrapPattern fields
      expr = ExpM $ AppE defaultExpInfo (ExpM $ VarE defaultExpInfo con)
             (ty_args ++ [TypM $ VarT v | TyPatM v _ <- ex_types])
             (field_exprs ++ return_expr)
      pattern =
        -- Construct a pattern to bind the reconstructed value
        case dc_repr
        of DeconValue -> memVarP (patMVar' pat) (patMParamType pat)
           DeconBoxed -> memVarP (patMVar' pat) (patMParamType pat)
           DeconReferenced dict ->
             localVarP (patMVar' pat) (patMType pat) dict

      return_expr =
        -- If binding to a local variable, the variable is an output parameter
        case dc_repr
        of DeconReferenced _ -> [ExpM $ VarE defaultExpInfo $ patMVar' pat]
           _ -> []
             
      ctx = contextItem $ LetCtx defaultExpInfo pattern expr
  in ctx : concat field_contexts

-- | Generate code to rewrap a return value.  Given the unwrapped values,
--   produce a writer or write to the given destination
rewrapReturnField :: Maybe ExpM -> WrapPat -> ExpM
rewrapReturnField mdst (WrapPat pat wrap_spec) =
  case wrap_spec
  of IdWP mdict ->
       let copy_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_copy)
           param_exp =
             -- If this is a read parameter, then we need to copy it
             case patMRepr pat
             of ValPT _ -> pattern_var_exp
                BoxPT   -> pattern_var_exp
                ReadPT  ->
                  let Just dict = mdict
                  in ExpM $ AppE defaultExpInfo copy_op [TypM $ patMType pat]
                     (dict : maybeToList mdst)
       in param_exp
     
     DeconWP dc_repr con ty_args ex_types fields ->
       rewrapDeconReturn mdst pat dc_repr con ty_args ex_types fields
     
     LoadWP repr dict dst_var ->
       -- Undo a load by storing the variable 
       --
       -- > store(dst_var, dst)
       let pattern = localVarP (patMVar' pat) (patMType pat) dict
           store = case repr
                   of Value -> store_op
                      Boxed -> storeBox_op
           store_exp = ExpM $ AppE defaultExpInfo store
                       [TypM $ patMType pat]
                       (ExpM (VarE defaultExpInfo dst_var) : maybeToList mdst)
       in store_exp

     DeadWP _ ->
       internalError "rewrapReturnField: Not implemented"
  where
    pattern_var_exp = ExpM $ VarE defaultExpInfo (patMVar' pat)
    store_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_store)
    storeBox_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_storeBox)

rewrapDeconReturn mdst pat dc_repr con ty_args ex_types fields =
  -- Undo a case statement by constructing a value
  let field_exprs = map (rewrapReturnField Nothing) fields
      expr = ExpM $ AppE defaultExpInfo (ExpM $ VarE defaultExpInfo con)
             (ty_args ++ [TypM $ VarT v | TyPatM v _ <- ex_types])
             (field_exprs ++ maybeToList mdst)
  in expr

-- | Get the function arguments to pass to the worker function for a given
--   wrapper argument
unwrappedArgument :: WrapPat -> ([TypM], [ExpM])
unwrappedArgument (WrapPat pat wrapper) =
  case wrapper
  of IdWP _ -> ([], [var_exp $ patMVar' pat])
     DeconWP _ _ _ ex_types fields ->
       let (ty_args, val_args) = unwrappedArguments fields
           ex_args = [TypM $ VarT v | TyPatM v _ <- ex_types]
       in (ex_args ++ ty_args, val_args)
     LoadWP _ _ v -> ([], [var_exp v])
     DeadWP _ -> ([], [])
  where
    var_exp v = ExpM (VarE defaultExpInfo v)

unwrappedArguments :: [WrapPat] -> ([TypM], [ExpM])
unwrappedArguments pats =
  let (ty_args, val_args) = unzip $ map unwrappedArgument pats
  in (concat ty_args, concat val_args)
     
-- | Get the function parameters of the worker function
unwrappedParameter :: WrapPat -> ([TyPatM], [PatM])
unwrappedParameter (WrapPat pat wrapper) =
  case wrapper
  of IdWP _ -> ([], [pat])
     DeconWP _ _ _ ex_types fields ->
       let (ty_params, val_params) = unwrappedParameters fields
       in (ex_types ++ ty_params, val_params)
     LoadWP Value _ v -> ([], [memVarP v (ValPT Nothing ::: patMType pat)])
     LoadWP Boxed _ v -> ([], [memVarP v (BoxPT ::: patMType pat)])
     DeadWP _ -> ([], [])

unwrappedParameters :: [WrapPat] -> ([TyPatM], [PatM])
unwrappedParameters pats =
  let (ty_args, val_args) = unzip $ map unwrappedParameter pats
  in (concat ty_args, concat val_args)

-- | Get the return type of the unwrapped return value.
-- Returns 'Nothing' if there's no unwrapped return value.
unwrappedReturnType :: WrapRet -> Maybe RetM
unwrappedReturnType NoWrapRet =
  Nothing

unwrappedReturnType (WrapRet _ _ (IdWP _)) =
  Nothing

unwrappedReturnType (WrapRet pat _ (LoadWP Value _ _)) =
  Just $ RetM $ ValRT ::: patMType pat

unwrappedReturnType (WrapRet pat _ (DeconWP _ _ _ _ fields)) =
  let ([], unboxed_tuple_params) = unwrappedParameters fields
      unboxed_tuple_types = map patMType unboxed_tuple_params
      con = unboxedTupleTypeCon $ length unboxed_tuple_params
  in Just $ RetM $ ValRT ::: varApp con unboxed_tuple_types

unwrappedReturnType (WrapRet pat _ (DeadWP _)) =
  internalError "unwrappedReturnType"

-- | Given a return parameter, determine how to wrap the return value
wrapRet :: PatM -> AFMonad e WrapRet
wrapRet pat@(MemVarP pat_var (OutPT ::: pat_type) _) = do
  wrapper <- wrapPattern' Return pat Used

  -- If the wrapper is 'LoadWP', then use the return variable that has already
  -- been created.  Otherwise create a new one.
  retvar <- case wrapper
            of LoadWP _ _ v -> return v
               _ -> newClonedVar pat_var
  return $ WrapRet pat retvar wrapper

wrapRet _ = internalError "wrapRet: Unexpected parameter representation"

{-
wrapRetType :: Type -> AF WrapRet'
wrapRetType pat_type =
  case fromVarApp pat_type
  of Just (ty_op, ty_args) -> do
       tenv <- getTypeEnv
       case fromSingletonTyCon tenv ty_op of
         Just (data_type, dcon_type) ->
           -- This data type has a single constructor with no existential
           -- variables
           deconSingletonReturn data_type dcon_type ty_args
         _ -> case lookupDataType ty_op tenv
              of Just dtype | dataTypeRepresentation dtype == Value -> do
                   -- This data type can be loaded
                   dict <- withReprDict pat_type return
                   return $ StoreWR Value dict
                 _ -> return IdWR
     Nothing -> return IdWR

deconSingletonReturn data_type dcon_type ty_args
  | not $ null $ dataConPatternExTypes dcon_type =
      -- Cannot deconstruct if it has existential types
      return IdWR
  | otherwise = do
      -- Instantiate the data constructor with fresh type variables
      inst_a_types <- replicateM num_universal_types $ newAnonymousVar TypeLevel
      let ([], fields, inst_repr ::: inst_type) =
            instantiateDataConType dcon_type (map VarT inst_a_types) []
  
      -- Unify with the actual type
      let actual_type = varApp (dataConTyCon dcon_type) ty_args
      m_u_subst <- unifyTypeWithPatternAF inst_a_types inst_type actual_type
      u_subst <- case m_u_subst
                 of Just s -> return s
                    Nothing -> internalError "deconSingletonReturn"

      -- Apply substitution to the type arguments
      let actual_a_types = map instantiate_var inst_a_types
            where
              instantiate_var v =
                case substituteVar v u_subst
                of Just t -> t
                   Nothing -> internalError "deconSingletonReturn"

      -- Wrap the fields
      field_wrappers <- mapM wrap_field [returnReprToParamRepr rrepr ::: rtype
                                        | rrepr ::: rtype <- fields]
      case sequence field_wrappers of
        Nothing -> return IdWR
        Just wrappers -> do
          dict <- withReprDict actual_type return
          return $ UnboxedWR dict (dataConCon dcon_type)
                   (map TypM actual_a_types) wrappers
  where
    num_universal_types = length $ dataConPatternParams dcon_type

    -- Do not need to unpack value returns
    wrap_field (ValPT _ ::: ty) = do
      pat_var <- newAnonymousVar ObjectLevel
      return $ Just $
        WrapPat (memVarP pat_var (ValPT Nothing ::: ty)) (IdWP Nothing)
    
    -- Cannot unpack boxed returns
    wrap_field (BoxPT ::: _) = return Nothing
      
    -- Try to unpack reference returns
    wrap_field (ReadPT ::: ty) = do
      pat_var <- newAnonymousVar ObjectLevel
      wrapper@(WrapPat _ wp) <-
        wrapPattern ReturnField (memVarP pat_var (ReadPT ::: ty))
      case wp of
        LoadWP Value _ _ -> return $ Just wrapper
        _ -> return Nothing
-}

-- | Determine whether the variable appears in the expression
checkForVariable :: Var -> ExpM -> Bool
checkForVariable v e = v `Set.member` freeVariables e

-- | Apply the transformation to each expression in tail position.
--   Look through let, letfun, and case statements.
mapOverTailExprs :: (ExpM -> AFMonad e ExpM) -> ExpM -> AFMonad e ExpM
mapOverTailExprs f expression =
  case fromExpM expression
  of LetE inf binder rhs body ->
       -- FIXME: add local var to environment
       liftM (ExpM . LetE inf binder rhs) $ mapOverTailExprs f body
     LetfunE inf defs body ->
       -- FIXME: add local vars to environment
       liftM (ExpM . LetfunE inf defs) $ mapOverTailExprs f body
     CaseE inf scr alts -> do
       -- FIXME: Add locals to environment
       alts' <- mapM map_alt alts
       return $ ExpM $ CaseE inf scr alts'
     _ -> f expression
  where
    map_alt (AltM alt) = do
      body <- mapOverTailExprs f $ altBody alt
      return $ AltM (alt {altBody = body})

-- | Generate code to unwrap a return parameter.  The code is put into the
--   worker function to turn the original return value into an unwrapped
--   return value.
unwrapReturn :: WrapRet -> ExpM -> AFMonad e ExpM
unwrapReturn NoWrapRet worker_body = return worker_body

unwrapReturn (WrapRet rparam _ (IdWP _)) worker_body = return worker_body

-- Save a return value to a temporary variable.  Load and return it.

unwrapReturn (WrapRet rparam _ (LoadWP Value dict _)) worker_body =
  mapOverTailExprs unwrap_return worker_body
  where
    unwrap_return tail_expr =
      let binder = localVarP (patMVar' rparam) (patMType rparam) dict
          load_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_load)
          load_exp = ExpM $ AppE defaultExpInfo load_op
                     [TypM $ patMType rparam]
                     [ExpM $ VarE defaultExpInfo (patMVar' rparam)]
      in return $ ExpM $ LetE defaultExpInfo binder tail_expr load_exp

unwrapReturn (WrapRet rparam _ (LoadWP Boxed dict _)) worker_body =
  mapOverTailExprs unwrap_return worker_body
  where
    unwrap_return tail_expr =
      let binder = memVarP (patMVar' rparam) (BoxPT ::: patMType rparam)
          load_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_loadBox)
          load_exp = ExpM $ AppE defaultExpInfo load_op
                     [TypM $ patMType rparam]
                     [ExpM $ VarE defaultExpInfo (patMVar' rparam)]
      in return $ ExpM $ LetE defaultExpInfo binder tail_expr load_exp

-- Unwrap a data type with a single constructor.
--
-- > local rparam = worker_body
-- > in case rparam
-- > of C t1 ... tM x1 ... xN.
-- >      case x1 of ....
-- >      case x2 of ....
-- >      unboxedTupleK t1 ... tK y1 ... yK

unwrapReturn (WrapRet rparam _ (DeconWP _ con ty_args [] fields)) worker_body = 
  mapOverTailExprs unwrap_return worker_body
  where
    unwrap_return :: ExpM -> AFMonad e ExpM
    unwrap_return tail_expr = do
      tenv <- getTypeEnv
      let Just data_con = lookupDataCon con tenv
      dict <- withReprDict (varApp (dataConTyCon data_con) $ map fromTypM ty_args) return
      let -- unwrap each each field
          unwrap_context = concatMap unwrapPattern fields
          
          -- Create the unboxed value
          ([], unwrapped_args) = unwrappedArguments fields
          unwrapped_types = case unwrappedParameters fields
                            of ([], params) -> map (TypM . patMType) params
          unboxed_con =
            ExpM $ VarE defaultExpInfo (unboxedTupleCon $ length unwrapped_args)
          unboxed_app =
            ExpM $ AppE defaultExpInfo unboxed_con unwrapped_types unwrapped_args

          -- Deconstruct the original value
          scrutinee = ExpM $ VarE defaultExpInfo (patMVar' rparam)
          case_stm = ExpM $ CaseE defaultExpInfo scrutinee
                     [AltM $ Alt { altConstructor = con
                                 , altTyArgs = ty_args
                                 , altExTypes = []
                                 , altParams = [pat | WrapPat pat _ <- fields]
                                 , altBody = applyContext unwrap_context $
                                             unboxed_app}]

          -- Bind the original return value
          wrapped_binder = localVarP (patMVar' rparam) (patMType rparam) dict
      return $ ExpM $ LetE defaultExpInfo wrapped_binder tail_expr case_stm

unwrapReturn (WrapRet rparam _ (DeadWP _)) worker_body =
  internalError "unwrapReturn: Not implemented"

-- | Generate code to rewrap a return parameter.  The code is placed into a
--   wrapper function following a call to the worker.
--
--   If the parameter gets unwrapped, then the given expression (which is a   
--   call to the worker function) returns an unboxed return value.  The
--   unboxed return value will be written into the return variable.
--
--   When rewrapping a return value to pass to a call to 'copy', we short-cut
--   the call to 'copy' and write directly into the destination.  The
--   destination pointer is given by @override_dst@.
rewrapReturn :: Maybe ExpM -> WrapRet -> ExpM -> AFMonad e ExpM
rewrapReturn _ NoWrapRet worker_call = return worker_call

rewrapReturn _ (WrapRet rparam _ (IdWP _)) worker_call = return worker_call

-- Store a value into the return variable

rewrapReturn override_dst (WrapRet rparam _ (LoadWP Value dict _)) worker_call =
  mapOverTailExprs rewrap_return worker_call
  where
    rewrap_return tail_expr =
      let store_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_store)
          dst = case override_dst
                of Just e -> e
                   Nothing -> ExpM $ VarE defaultExpInfo (patMVar' rparam)
          store_exp = ExpM $ AppE defaultExpInfo store_op
                      [TypM $ patMType rparam] [tail_expr, dst]
      in return $ store_exp

-- Rewrap a data type with a single constructor.
-- Starting with an unboxed tuple, produce a value in the original return type.
--
-- > case worker_call
-- > of unboxedTupleN t1 ... tN x1 ... xN.
-- >      let y1 = (rewrap some of x1 ... xN)
-- >      ...
-- >      let yM = (rewrap some of x1 ... xN)
-- >      con ty_args y1 ... yM rparam
--
rewrapReturn override_dst (WrapRet rparam _ (DeconWP _ con ty_args [] fields)) worker_call =
  mapOverTailExprs rewrap_boxed_return worker_call
  where
    rewrap_boxed_return tail_expr =
      let -- Apply the constructor to the rewrapped 
          con_exp = ExpM $ VarE defaultExpInfo con
          retvar_exp =
            case override_dst
            of Just e -> e
               Nothing -> ExpM $ VarE defaultExpInfo (patMVar' rparam)
          field_output_exps = map (rewrapReturnField Nothing) fields
                              -- [ExpM $ VarE defaultExpInfo (patMVar' pat)
                              --  | WrapPat pat _ <- fields]
          build_return_data =
            ExpM $ AppE defaultExpInfo con_exp ty_args
            (field_output_exps ++ [retvar_exp])
            
          -- Match the worker's return value against an unboxed tuple
          ([], unboxed_tuple_params) = unwrappedParameters fields
          unboxed_tuple_types = map patMType unboxed_tuple_params
          unboxed_tuple_size = length unboxed_tuple_params
          unboxed_alt = AltM $
            Alt { altConstructor = unboxedTupleCon unboxed_tuple_size
                , altTyArgs = map TypM unboxed_tuple_types
                , altExTypes = []
                , altParams = unboxed_tuple_params
                , altBody = build_return_data}

      in return $ ExpM $ CaseE defaultExpInfo tail_expr [unboxed_alt]

-- | Given a function's parameters and return type, determine how
--   to wrap the function.  Return the conversion specifications, the 
--   worker function's parameters, and the worker function's return type.
wrapFunctionType :: [TyPatM] -> [PatM] -> RetM
                 -> AF ([WrapPat], Maybe PatM, WrapRet, [TyPatM], [PatM], RetM)
wrapFunctionType ty_params params ret = do
  let (in_params, out_param) =
        -- Separate the output parameter from the other parameters
        case patMParamType (last params)
        of OutPT ::: _ -> (init params, Just $ last params)
           _ -> (params, Nothing)
  
  -- Compute how to convert parameters
  wrap_params <- wrapPatterns Parameter in_params
  wrap_ret <- case out_param
              of Nothing -> return NoWrapRet
                 Just p -> wrapRet p

  -- Get the new parameters
  let (p_ty_params, p_params) = unwrappedParameters wrap_params
      out_param =
        case wrap_ret
        of NoWrapRet -> Nothing               -- No return parameter
           WrapRet pat _ (IdWP _) -> Just pat -- Unchanged
           WrapRet pat _ _ -> Nothing         -- Eliminated return parameter
      
      ty_params' = ty_params ++ p_ty_params
      params' = p_params ++ maybeToList out_param
      ret' = fromMaybe ret $ unwrappedReturnType wrap_ret
  return (wrap_params, out_param, wrap_ret, ty_params', params', ret')

-- | Given a let-pattern binding, determine if the bound variable should be
--   replaced by an unpacked variable.  Return a specification of how to
--   unwrap it.
wrapLocalPattern :: PatM -> AFMonad e (Maybe WrapRet)
wrapLocalPattern (MemVarP {}) = return Nothing
wrapLocalPattern (MemWildP {}) = return Nothing
wrapLocalPattern pat@(LocalVarP var ty dict uses) = do
  newvar <- newClonedVar var
  wp <- wrapPattern' Local (memVarP var (ReadPT ::: ty)) (specificity uses)
  return $ Just $ WrapRet pat newvar wp

-- | Get the pattern used to bind an unwrapped local variable.
--   This should only be called on local variable that are being unwrapped.
unwrappedLocalPattern :: WrapRet -> PatM
unwrappedLocalPattern (WrapRet pat uw_var (DeconWP _ _ _ _ fields)) =
  let ([], unboxed_tuple_params) = unwrappedParameters fields
      unboxed_tuple_types = map patMType unboxed_tuple_params
      con = unboxedTupleTypeCon $ length unboxed_tuple_params
      ty = varApp con unboxed_tuple_types
  in memVarP uw_var (ValPT Nothing ::: ty)

unwrappedLocalPattern (WrapRet pat uw_var (LoadWP Value _ _)) =
  memVarP uw_var (ValPT Nothing ::: patMType pat)

unwrappedLocalPattern (WrapRet pat uw_var (LoadWP Boxed _ _)) =
  memVarP uw_var (BoxPT ::: patMType pat)

unwrappedLocalPattern (WrapRet pat uw_var (DeadWP _)) = 
  internalError "unwrappedLocalPattern: Unexpected pattern"

-------------------------------------------------------------------------------
-- Argument flattening transformation

-- | Flatten the function arguments.  The original function name
--   becomes the name of the wrapper function.  A new function is created as
--   the worker function, containing the original function body.
--
--   If flattening would not change the function arguments, then the function
--   body is transformed and a single definition is returned.  Otherwise,
--   the worker is returned, followed by the wrapper.
flattenFunctionArguments :: Def Mem -> AF (Maybe (Def Mem), Def Mem)
flattenFunctionArguments def =
  let fun_name = definiendum def
      FunM fun = definiens def
      ty_params = funTyParams fun
      params = funParams fun
      ret = funReturn fun
  in assumeTyPats ty_params $ assumePats params $ do
    (wrap_pats, wrap_rpat, wrap_ret, work_ty_params, work_params, work_ret) <-
      wrapFunctionType ty_params params ret
    
    -- Flatten functions inside the function body
    fun_body <- flattenInExp $ funBody fun
    let fun' = fun {funBody = fun_body}

    -- Construct wrapper, if it's beneficial
    if all isIdWrapper wrap_pats && isIdRet wrap_ret
      then do
        return (Nothing, mkDef fun_name (FunM fun'))
      else do
        worker <-
          mkWorkerFunction work_ty_params work_params work_ret
          wrap_pats wrap_ret fun_name (funInfo fun) fun_body
        wrapper <-
          mkWrapperFunction ty_params params ret
          wrap_pats wrap_rpat wrap_ret fun_name ret (definiendum worker)
        return (Just worker, wrapper)

mkWorkerFunction :: [TyPatM] -> [PatM] -> RetM
                 -> [WrapPat] -> WrapRet -> Var -> ExpInfo -> ExpM
                 -> AF (Def Mem)
mkWorkerFunction ty_params params ret wrap_pats wrap_ret wrapper_name inf body = do
  -- Create a new variable for the worker
  worker_name <- newClonedVar wrapper_name
  
  -- Unwrap the return value
  body1 <- unwrapReturn wrap_ret body

  -- Re-wrap the unwrapped arguments
  let wrap_context = concatMap (fst . rewrapPattern) wrap_pats
      wrapped_body = applyContext wrap_context body1
      wrap_fn = FunM $ Fun inf ty_params params ret wrapped_body

  return $ mkDef worker_name wrap_fn

mkWrapperFunction :: [TyPatM] -> [PatM] -> RetM
                  -> [WrapPat] -> Maybe PatM -> WrapRet -> Var
                  -> RetM -> Var -> AF (Def Mem)
mkWrapperFunction original_ty_params original_params original_ret 
                  wrap_pats wrap_rpat wrap_ret wrapper_name
                  worker_ret worker_name = do
  let unwrap_context = concatMap unwrapPattern wrap_pats
      
      -- Create a call to the worker
      (call_ty_args, call_args) = unwrappedArguments wrap_pats
      return_arg = case wrap_rpat
                   of Nothing -> []
                      Just pat -> [ExpM $ VarE defaultExpInfo (patMVar' pat)]
      orig_ty_args = [TypM t | TyPatM _ t <- original_ty_params]
      call = ExpM $ AppE defaultExpInfo (ExpM $ VarE defaultExpInfo worker_name)
             (orig_ty_args ++ call_ty_args) (call_args ++ return_arg)
  
  -- Rewrap the return value
  call1 <- rewrapReturn Nothing wrap_ret call
      
     -- Create the wrapper function
  let wrapper_body = applyContext unwrap_context call1
      wrapper_fun = FunM $ Fun defaultExpInfo
                    original_ty_params original_params original_ret
                    wrapper_body
  return $ mkWrapperDef wrapper_name wrapper_fun

-- | Perform flattening in the body of a function, but don't change the
--   function's arguments
flattenInFun :: FunM -> AF FunM
flattenInFun (FunM f) =
  assumeTyPats (funTyParams f) $ assumePats (funParams f) $ do
    fun_body <- flattenInExp $ funBody f
    return $ FunM $ f {funBody = fun_body}

flattenInGroup :: DefGroup (Def Mem) -> AF [DefGroup (Def Mem)]
flattenInGroup (NonRec def) = do
  (m_worker, wrapper) <- flattenFunctionArguments def
  -- Wrapper can reference worker, but not vice versa; produce two groups
  return $ case m_worker
           of Nothing -> [NonRec wrapper]
              Just w  -> [NonRec w, NonRec wrapper]

flattenInGroup (Rec defs) = do
  flattened <- mapM flattenFunctionArguments defs
  return [Rec $ catMaybes $ concat [[m_worker, Just wrapper]
                                   | (m_worker, wrapper) <- flattened]]

flattenInExp :: ExpM -> AF ExpM
flattenInExp expression =
  case fromExpM expression
  of VarE {} -> return expression
     LitE {} -> return expression
     AppE inf op ty_args args -> do
       op' <- flattenInExp op
       args' <- mapM flattenInExp args
       return $ ExpM $ AppE inf op' ty_args args'
     LamE inf f -> do
       f' <- flattenInFun f
       return $ ExpM $ LamE inf f'
     LetE inf pat rhs body -> do
       rhs' <- flattenInExp rhs
       body' <- flattenInExp body
       return $ ExpM $ LetE inf pat rhs' body'
     LetfunE inf defs body -> do
       new_defs <- flattenInGroup defs
       body' <- flattenInExp body
       let mk_letfun d e = ExpM (LetfunE inf d e)
       return $ foldr mk_letfun body' new_defs
     CaseE inf scr alts -> do
       scr' <- flattenInExp scr
       alts' <- mapM flattenInAlt alts
       return $ ExpM $ CaseE inf scr' alts'

flattenInAlt :: AltM -> AF AltM
flattenInAlt (AltM alt) =
  assumeTyPats (altExTypes alt) $ assumePats (altParams alt) $ do
    body <- flattenInExp $ altBody alt
    return $ AltM $ alt {altBody = body}

flattenInExport :: Export Mem -> AF (Export Mem)
flattenInExport export = do
  f <- flattenInFun $ exportFunction export
  return $ export {exportFunction = f}

flattenModuleContents :: (Module Mem) -> AF (Module Mem)
flattenModuleContents (Module mod_name defss exports) = do
  defss' <- mapM flattenInGroup defss
  exports' <- mapM flattenInExport exports
  return $ Module mod_name (concat defss') exports'

flattenArguments :: Module Mem -> IO (Module Mem)
flattenArguments mod =
  withTheNewVarIdentSupply $ \id_supply -> do
    (dict_env, intindex_env) <- runFreshVarM id_supply createDictEnv
    type_env <- readInitGlobalVarIO the_memTypes
    let env = AFLVEnv id_supply type_env dict_env intindex_env ()
    runReaderT (unAF $ flattenModuleContents mod) env

-------------------------------------------------------------------------------
-- Local variable flattening transformation

-- | Perform local variable flattening on the body of a function
lvInFun :: FunM -> LF FunM
lvInFun (FunM f) =
  assumeTyPats (funTyParams f) $ assumePats (funParams f) $ do
    fun_body <- lvExp $ funBody f
    return $ FunM $ f {funBody = fun_body}

lvDef :: Def Mem -> LF (Def Mem)
lvDef def = mapMDefiniens lvInFun def

lvExp :: ExpM -> LF ExpM
lvExp expression = traceShow (pprExp expression) $
  case fromExpM expression
  of VarE _ v -> do
       -- It's an error to see an unpacked local variable here.
       -- Any appearances of an unpacked local variable should have been
       -- transformed by the App or Case rules.
       m_unpacking <- lookupUnpackedLocalVariable v
       when (isJust m_unpacking) $
         internalError "lvExp: Unexpected unpacked variable"
       return expression
       -- return expression
     LitE {} -> return expression
     AppE inf op ty_args args -> lvApp inf op ty_args args
     LamE inf f -> do
       f' <- lvInFun f
       return $ ExpM $ LamE inf f'
     LetE inf pat rhs body -> lvLet inf pat rhs body
     LetfunE inf defs body -> do
       new_defs <- mapM lvDef defs
       body' <- lvExp body
       return $ ExpM $ LetfunE inf new_defs body'
     CaseE inf scr alts -> lvCase inf scr alts

lvApp inf op ty_args args =
  case op
  of ExpM (VarE _ op_var)
       | op_var `isPyonBuiltin` the_copy ->
           -- If copying an unpacked variable, rewrap it.  The rewrapped value
           -- is returned directly without being further copied.
           case args
           of src_arg : other_args ->
                case src_arg
                of ExpM (VarE src_info src_var) -> do
                     m_unpacking <- lookupUnpackedLocalVariable src_var
                     case m_unpacking of
                       Just wrap_ret -> do_copy src_info wrap_ret other_args
                       Nothing -> do_app
                   _ -> do_app
              _ -> internalError "lvApp"
       | op_var `isPyonBuiltin` the_load ->
           -- If loading an unpacked variable, simply return the unpacked
           -- variable.
           case args
           of [src_arg] ->
                case src_arg
                of ExpM (VarE src_info src_var) -> do
                     m_unpacking <- lookupUnpackedLocalVariable src_var
                     case m_unpacking of
                       Just wrap_ret -> do_load wrap_ret
                       Nothing -> do_app
                   _ -> do_app
              _ -> internalError "lvApp"
       | op_var `isPyonBuiltin` the_loadBox ->
           -- If loading an unpacked variable, simply return the unpacked
           -- variable.
           case args
           of [src_arg] ->
                case src_arg
                of ExpM (VarE src_info src_var) -> do
                     m_unpacking <- lookupUnpackedLocalVariable src_var
                     case m_unpacking of
                       Just wrap_ret -> do_loadBox wrap_ret
                       Nothing -> do_app
                   _ -> do_app
              _ -> internalError "lvApp"
     _ -> do_app
  where
    do_app = do
      op' <- lvExp op
      args' <- mapM lvExp args
      return $ ExpM $ AppE inf op' ty_args args'

    do_copy src_info wrap_ret@(WrapRet original_param unpacked_var _) [] = do
      let uv_exp = ExpM $ VarE src_info unpacked_var
      -- Create a lambda expression taking the destination as a
      -- parameter
      return_exp <- rewrapReturn Nothing wrap_ret uv_exp
      let fun = FunM $
                Fun { funInfo = inf 
                    , funTyParams = [] 
                    , funParams = [original_param] 
                    , funReturn = RetM $
                                  SideEffectRT ::: patMType original_param
                    , funBody = return_exp}
      return $ ExpM $ LamE inf fun
      
    do_copy src_info wrap_ret@(WrapRet original_param unpacked_var _) [arg] = do
      let uv_exp = ExpM $ VarE src_info unpacked_var
      arg' <- lvExp arg
      rewrapReturn (Just arg') wrap_ret uv_exp

    do_load wrap_ret@(WrapRet _ unpacked_var _) =
      -- Return the unpacked variable, which is the same as the loaded value
      -- of the original variable
      return $ ExpM $ VarE inf unpacked_var

    do_loadBox wrap_ret@(WrapRet _ unpacked_var _) =
      -- Return the unpacked variable, which is the same as the loaded value
      -- of the original variable
      return $ ExpM $ VarE inf unpacked_var

lvLet :: ExpInfo -> PatM -> ExpM -> ExpM -> LF ExpM
lvLet inf binder rhs body = do
  binder' <- wrapLocalPattern binder
  case binder' of
    Just wrapped_pat | not $ isIdRet wrapped_pat -> do
      -- First recursively transform RHS.
      -- Then unwrap the local value where it's defined in the RHS
      rhs' <- unwrapReturn wrapped_pat =<< lvExp rhs

      -- Continue transforming local variables in the body.  Add a mapping
      -- to the environment so we can unpack the variable.
      body' <- withUnpackedLocalVariable wrapped_pat $ lvExp body
      return $ ExpM $ LetE inf (unwrappedLocalPattern wrapped_pat) rhs' body'
    _ -> do
      -- Don't unpack this variable
      rhs' <- lvExp rhs
      body' <- lvExp body
      return $ ExpM $ LetE inf binder rhs' body'

-- If the scrutinee was a transformed local variable, then
-- repack the variable just before the case statement, producing
--
-- > let original_variable = (recreate the original value)
-- > in case original_variable of ...
lvCase inf scr alts =
  case scr
  of ExpM (VarE scr_info scr_var) -> do
       m_unpacking <- lookupUnpackedLocalVariable scr_var
       case m_unpacking of
         -- This local variable must be deconstructed
         Just wrap_ret@(WrapRet pat unpacked_var (DeconWP (DeconReferenced dict) _ _ _ _)) -> do
           let uv_exp = ExpM $ VarE scr_info unpacked_var
           -- If the variable is referenced inside the expression,
           -- don't unwrap the inner occurrences
           case_expr <- deleteUnpackedLocalVariable scr_var $
                        do_case inf scr alts

           worker_expr <- rewrapReturn Nothing wrap_ret uv_exp
           return $ ExpM $ LetE inf (localVarP scr_var (patMType pat) dict)
             worker_expr case_expr
         Just _ -> internalError "lvExp: Unexpected unpacking transformation"
         Nothing -> do
           scr' <- lvExp scr
           do_case inf scr' alts
     _ -> do
       scr' <- lvExp scr
       do_case inf scr' alts
  where
    do_case inf scr' alts = do
      alts' <- mapM lvInAlt alts
      return $ ExpM $ CaseE inf scr' alts'
    
    find_alt con alts = find (\(AltM alt) -> con == altConstructor alt) alts

lvInAlt :: AltM -> LF AltM
lvInAlt (AltM alt) =
  assumeTyPats (altExTypes alt) $ assumePats (altParams alt) $ do
    body <- lvExp $ altBody alt
    return $ AltM $ alt {altBody = body}

lvInExport :: Export Mem -> LF (Export Mem)
lvInExport export = do
  f <- lvInFun $ exportFunction export
  return $ export {exportFunction = f}

lvModuleContents :: (Module Mem) -> LF (Module Mem)
lvModuleContents (Module mod_name defss exports) = do
  defss' <- mapM (mapM lvDef) defss
  exports' <- mapM lvInExport exports
  return $ Module mod_name defss' exports'

flattenLocals :: Module Mem -> IO (Module Mem)
flattenLocals mod =
  withTheNewVarIdentSupply $ \id_supply -> do
    (dict_env, intindex_env) <- runFreshVarM id_supply createDictEnv
    type_env <- readInitGlobalVarIO the_memTypes
    let env = AFLVEnv id_supply type_env dict_env intindex_env IntMap.empty
    runReaderT (unAF $ lvModuleContents mod) env
