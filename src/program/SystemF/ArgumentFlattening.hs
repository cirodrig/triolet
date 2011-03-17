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
module SystemF.ArgumentFlattening(flattenArguments)
where

import Control.Monad.Reader
import Data.Maybe
import qualified Data.Set as Set
  
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

-- | Reader environment used during argument flattening 
data AFEnv =
  AFEnv
  { afVarSupply :: {-# UNPACK #-}!(IdentSupply Var)
  , afTypeEnv :: TypeEnv
  , afDictEnv :: MkDictEnv
  , afIntIndexEnv :: IntIndexEnv
  }

-- | The monad for argument flattening
newtype AF a = AF {unAF :: ReaderT AFEnv IO a} deriving(Monad, MonadIO)

instance Supplies AF (Ident Var) where
  fresh = AF $ ReaderT $ \env -> supplyValue $ afVarSupply env

liftFreshVarAF :: FreshVarM a -> AF a
liftFreshVarAF m = AF $ ReaderT $ \env -> runFreshVarM (afVarSupply env) m

instance ReprDictMonad AF where
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
                       -> AF (Maybe Substitution)
unifyTypeWithPatternAF fvs etype gtype = AF $ ReaderT $ \env ->
  unifyTypeWithPattern (afVarSupply env) (afTypeEnv env) fvs etype gtype

assumeTyPat :: TyPatM -> AF a -> AF a
assumeTyPat (TyPatM tyvar kind) m = AF $ local insert_type $ unAF m
  where
    insert_type env =
      env {afTypeEnv = insertType tyvar (ValRT ::: kind) $ afTypeEnv env}

assumeTyPats :: [TyPatM] -> AF a -> AF a
assumeTyPats typats m = foldr assumeTyPat m typats

assumePat :: PatM -> AF a -> AF a
assumePat pat m = AF $ local insert_type $ unAF $ saveReprDictPattern pat m
  where
    pat_var = patMVar' pat
    insert_type =
      case pat
      of MemVarP {} -> \env ->
           env {afTypeEnv = insertType pat_var (patMReturnType pat) $ afTypeEnv env}
         MemWildP {} -> id
         LocalVarP {} -> internalError "assumePat"

assumePats :: [PatM] -> AF a -> AF a
assumePats pats m = foldr assumePat m pats

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

naturalValueTyConAF :: Var -> AF Bool
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
  | DeconWP !DeconRepr !Var [TypM] [TyPatM] [WrapPat]

    -- | Parameter value is loaded (either by value or boxed) into a new
    --   variable.  Also, save the type's representation dictionary.
  | LoadWP !Repr ExpM !Var

    -- | Parameter value is dead, and is not passed at all
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
data WrapRet = WrapRet !PatM !WrapRet'
             | NoWrapRet        -- ^ Function doesn't have a return parameter

-- | True if the wrapper specification says not to change the function's
--   return value.
isIdRet :: WrapRet -> Bool
isIdRet NoWrapRet = True
isIdRet (WrapRet _ IdWR) = True
isIdRet _ = False

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
  | UnboxedWR !ExpM !Var [TypM] [WrapPat]

-- | Representation of an object that should be deconstructed.
--   If it is passed by reference, its representation dictionary is needed
--   so it can be locally allocated.
data DeconRepr = DeconValue | DeconBoxed | DeconReferenced ExpM

-- | Wrap a sequence of patterns.  Variables bound by earlier patterns are
--   available in the scope of later patterns.
wrapPatterns :: What -> [PatM] -> AF [WrapPat]
wrapPatterns what (pat:pats) = do
  wrap_pat <- wrapPattern what pat
  wrap_pats <- assumePat pat $ wrapPatterns what pats
  return (wrap_pat : wrap_pats)

wrapPatterns _ [] = return []

-- | Decide how to pass one of the original function's parameters to the 
--   worker.
wrapPattern :: What -> PatM -> AF WrapPat
wrapPattern what pat = do
  wrapping <- wrapPattern' what pat (specificity $ patMDmd pat)
  return $ WrapPat pat wrapping

wrapPattern' :: What -> PatM -> Specificity -> AF WrapPat'
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
      -- Is this a data type with a single constructor?
      case fromVarApp $ patMType pat
      of Just (ty_op, ty_args) -> do
           tenv <- getTypeEnv
           case fromSingletonTyCon tenv ty_op of
             Nothing -> unchanged
             Just (data_type, dcon_type) -> do
               mx <- deconSingletonPattern what data_type dcon_type ty_args
               case mx of
                 Nothing -> unchanged
                 Just x  -> return x
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
             -> AF (Maybe WrapPat')
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

instantiatedReprDict :: ReturnType -> AF DeconRepr
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
                      -> AF (Maybe WrapPat')
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
                   -> AF (Maybe [WrapPat])
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

unwrappedReturnType (WrapRet _ IdWR) =
  Nothing

unwrappedReturnType (WrapRet pat (StoreWR Value _)) =
  Just $ RetM $ ValRT ::: patMType pat

unwrappedReturnType (WrapRet pat (UnboxedWR _ _ _ fields)) =
  let ([], unboxed_tuple_params) = unwrappedParameters fields
      unboxed_tuple_types = map patMType unboxed_tuple_params
      con = unboxedTupleCon $ length unboxed_tuple_params
  in Just $ RetM $ ValRT ::: varApp con unboxed_tuple_types

-- | Given a return parameter, determine how to wrap the return value
wrapRet :: PatM -> AF WrapRet
wrapRet pat@(MemVarP pat_var (OutPT ::: pat_type) _) = do
  wrapper <- wrapRetType pat_type
  return $ WrapRet pat wrapper

wrapRet _ = internalError "wrapRet: Unexpected parameter representation"

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

-- | Determine whether the variable appears in the expression
checkForVariable :: Var -> ExpM -> Bool
checkForVariable v e = v `Set.member` freeVariables e

-- | Apply the transformation to each expression in tail position.
--   Look through let, letfun, and case statements.
mapOverTailExprs :: (ExpM -> AF ExpM) -> ExpM -> AF ExpM
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
unwrapReturn :: WrapRet -> ExpM -> AF ExpM
unwrapReturn NoWrapRet worker_body = return worker_body

unwrapReturn (WrapRet rparam IdWR) worker_body = return worker_body

-- Save a return value to a temporary variable.  Load and return it.

unwrapReturn (WrapRet rparam (StoreWR Value dict)) worker_body =
  mapOverTailExprs unwrap_return worker_body
  where
    unwrap_return tail_expr =
      let binder = localVarP (patMVar' rparam) (patMType rparam) dict
          load_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_load)
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

unwrapReturn (WrapRet rparam (UnboxedWR dict con ty_args fields)) worker_body = 
  mapOverTailExprs unwrap_return worker_body
  where
    unwrap_return :: ExpM -> AF ExpM
    unwrap_return tail_expr =
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
                                 , altBody = unboxed_app}]

          -- Bind the original return value
          wrapped_binder = localVarP (patMVar' rparam) (patMType rparam) dict
      in return $ ExpM $ LetE defaultExpInfo wrapped_binder tail_expr case_stm

-- | Generate code to rewrap a return parameter.  The code is placed into a
--   wrapper function following a call to the worker.
--
--   If the parameter gets unwrapped, then the given expression (which is a   
--   call to the worker function) returns an unboxed return value.  The
--   unboxed return value will be written into the return variable.
rewrapReturn :: WrapRet -> ExpM -> AF ExpM
rewrapReturn NoWrapRet worker_call = return worker_call

rewrapReturn (WrapRet rparam IdWR) worker_call = return worker_call

-- Store a value into the return variable

rewrapReturn (WrapRet rparam (StoreWR Value dict)) worker_call =
  mapOverTailExprs rewrap_return worker_call
  where
    rewrap_return tail_expr =
      let store_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_store)
          store_exp = ExpM $ AppE defaultExpInfo store_op
                      [TypM $ patMType rparam]
                      [tail_expr, ExpM $ VarE defaultExpInfo (patMVar' rparam)]
      in return store_exp

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
rewrapReturn (WrapRet rparam (UnboxedWR _ con ty_args fields)) worker_call =
  mapOverTailExprs rewrap_boxed_return worker_call
  where
    rewrap_boxed_return tail_expr =
      let wrap_context = concatMap (fst . rewrapPattern) fields
          
          -- Apply the constructor to the rewrapped 
          con_exp = ExpM $ VarE defaultExpInfo con
          retvar_exp = ExpM $ VarE defaultExpInfo (patMVar' rparam)
          field_output_exps = [ExpM $ VarE defaultExpInfo (patMVar' pat)
                              | WrapPat pat _ <- fields]
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
                , altBody = applyContext wrap_context build_return_data}

      in return $ ExpM $ CaseE defaultExpInfo tail_expr [unboxed_alt]

-- | Given a function's parameters and return type, determine how
--   to wrap the function.  Return the conversion specifications, the 
--   worker function's parameters, and the worker function's return type.
wrapFunctionType :: [TyPatM] -> [PatM] -> RetM
                 -> AF ([WrapPat], WrapRet, [TyPatM], [PatM], RetM)
wrapFunctionType ty_params params ret = do
  let (in_params, out_param) =
        -- Separate the output parameter from the other parameters
        case patMParamType (last params)
        of OutPT ::: _ -> (init params, Just $ last params)
           _ -> (params, Nothing)
  
  -- Compute how to convert parameters
  wrap_params <- wrapPatterns Parameter params
  wrap_ret <- case out_param
              of Nothing -> return NoWrapRet
                 Just p -> wrapRet p

  -- Get the new parameters
  let (p_ty_params, p_params) = unwrappedParameters wrap_params
      out_param =
        case wrap_ret
        of NoWrapRet -> Nothing               -- No return parameter
           WrapRet pat IdWR -> Just pat       -- Unchanged
           WrapRet pat _ -> Nothing           -- Eliminated return parameter
      
      ty_params' = ty_params ++ p_ty_params
      params' = p_params ++ maybeToList out_param
      ret' = fromMaybe ret $ unwrappedReturnType wrap_ret
  return (wrap_params, wrap_ret, ty_params', params', ret')

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
flattenFunctionArguments (Def fun_name (FunM fun)) =
  let ty_params = funTyParams fun
      params = funParams fun
      ret = funReturn fun
  in assumeTyPats ty_params $ assumePats params $ do
    (wrap_pats, wrap_ret, work_ty_params, work_params, work_ret) <-
      wrapFunctionType ty_params params ret
    
    -- Flatten functions inside the function body
    fun_body <- flattenInExp $ funBody fun
    let fun' = fun {funBody = fun_body}

    -- Construct wrapper, if it's beneficial
    if all isIdWrapper wrap_pats && isIdRet wrap_ret
      then do
        return (Nothing, Def fun_name (FunM fun'))
      else do
        worker@(Def worker_name _) <-
          mkWorkerFunction work_ty_params work_params work_ret
          wrap_pats wrap_ret fun_name (funInfo fun) fun_body
        wrapper <-
          mkWrapperFunction ty_params wrap_pats wrap_ret fun_name ret worker_name
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

  return $ Def worker_name wrap_fn

mkWrapperFunction :: [TyPatM] -> [WrapPat] -> WrapRet -> Var -> RetM -> Var
                  -> AF (Def Mem)
mkWrapperFunction original_ty_params wrap_pats wrap_ret wrapper_name worker_ret worker_name = do
  let unwrap_context = concatMap unwrapPattern wrap_pats
      
      -- Create a call to the worker
      (call_ty_args, call_args) = unwrappedArguments wrap_pats
      orig_ty_args = [TypM t | TyPatM _ t <- original_ty_params]
      call = ExpM $ AppE defaultExpInfo (ExpM $ VarE defaultExpInfo worker_name)
             (orig_ty_args ++ call_ty_args) call_args
  
  -- Rewrap the return value
  call1 <- rewrapReturn wrap_ret call
      
     -- Create the wrapper function
  let wrapper_body = applyContext unwrap_context call1
      wrapper_fun = FunM $ Fun defaultExpInfo original_ty_params
                    [pat | WrapPat pat _ <- wrap_pats] worker_ret wrapper_body
  return $ Def wrapper_name wrapper_fun

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
    let env = AFEnv id_supply type_env dict_env intindex_env
    runReaderT (unAF $ flattenModuleContents mod) env