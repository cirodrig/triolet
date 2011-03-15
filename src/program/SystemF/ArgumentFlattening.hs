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

-- | Representation of an object that should be deconstructed.
--   If it is passed by reference, its representation dictionary is needed
--   so it can be locally allocated.
data DeconRepr = DeconValue | DeconBoxed | DeconReferenced ExpM

-- | Wrap a sequence of patterns.  Variables bound by earlier patterns are
--   available in the scope of later patterns.
wrapPatterns :: [PatM] -> AF [WrapPat]
wrapPatterns (pat:pats) = do
  wrap_pat <- wrapPattern pat
  wrap_pats <- assumePat pat $ wrapPatterns pats
  return (wrap_pat : wrap_pats)

wrapPatterns [] = return []

-- | Decide how to pass one of the original function's parameters to the 
--   worker.
wrapPattern :: PatM -> AF WrapPat
wrapPattern pat = do
  wrapping <- wrapPattern' pat (specificity $ patMDmd pat)
  return $ WrapPat pat wrapping

wrapPattern' :: PatM -> Specificity -> AF WrapPat'
wrapPattern' pat pattern_specificity =
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
    wrap_var_pattern Used = unchanged
    wrap_var_pattern (Loaded repr ty _) = loaded repr ty
    wrap_var_pattern Unused = dead

    wrap_var_pattern (Decond con ty_args ex_types spcs) = do
      tenv <- getTypeEnv
      case lookupDataConWithType con tenv of
        Just (data_type, dcon_type) ->
          deconPattern data_type dcon_type con ty_args ex_types spcs
        Nothing ->
          internalError "wrapPattern: Deconstructed unknown type"

    wrap_var_pattern Inspected =
      -- Is this a data type with a single constructor?
      case fromVarApp $ patMType pat
      of Just (ty_op, ty_args) -> do
           tenv <- getTypeEnv
           case lookupDataType ty_op tenv of
             Nothing -> unchanged
             Just data_type ->
               case dataTypeDataConstructors data_type
               of [con] ->
                    case lookupDataCon con tenv
                    of Just dcon_type ->
                         deconSingletonPattern data_type dcon_type ty_args
                       _ -> internalError "wrapPattern"
                  _ -> unchanged -- Not a singleton type
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
deconPattern :: DataType
             -> DataConType
             -> Var             -- ^ Constuctor to deconstruct
             -> [Type]          -- ^ Type arguments
             -> [(Var, Type)]   -- ^ Existential types
             -> [Specificity]   -- ^ Demand on fields
             -> AF WrapPat'
deconPattern data_type dcon_type con ty_args ex_types spcs = do
  let ex_pats = [TyPatM v t | (v, t) <- ex_types]
      data_con_args = ty_args ++ map (VarT . fst) ex_types
      (field_rtypes, instantiated_rtype) =
        instantiateDataConTypeWithExistentials dcon_type data_con_args
  
  when (length spcs /= length field_rtypes) $
    internalError "dconPattern: Inconsistent number of parameters"
  
  -- Create patterns and decide how to further deconstruct each field
  fields <-
    assumeTyPats ex_pats $
    forM (zip field_rtypes spcs) $ \(rrepr ::: rtype, spc) -> do
      pat_var <- newAnonymousVar ObjectLevel
      let pattern = memVarP pat_var (returnReprToParamRepr rrepr ::: rtype)
      wrapping <- wrapPattern' pattern spc
      return $ WrapPat pattern wrapping

  -- Determine the pattern's representation
  repr <- instantiatedReprDict instantiated_rtype
      
  return $ DeconWP repr con (map TypM ty_args) ex_pats fields

instantiatedReprDict :: ReturnType -> AF DeconRepr
instantiatedReprDict (ValRT ::: _) = return DeconValue
instantiatedReprDict (BoxRT ::: _) = return DeconBoxed
instantiatedReprDict (ReadRT ::: ty) =
  liftM DeconReferenced $ withReprDict ty return

-- | Deconstruct a singleton pattern, given the data type constructor and
--   its arguments.  The proper arguments to the data constructor are
--   determined by instantiating the constructor's type, then unifying it
--   with the pattern type.
deconSingletonPattern :: DataType
                      -> DataConType
                      -> [Type]
                      -> AF WrapPat'
deconSingletonPattern data_type dcon_type type_arguments = do
  -- Instantiate the data constructor with fresh type variables
  inst_a_types <- replicateM num_universal_types $ newAnonymousVar TypeLevel
  inst_e_types <- replicateM num_existential_types $ newAnonymousVar TypeLevel
  let (ex_params, fields, inst_repr ::: inst_type) =
        instantiateDataConType dcon_type (map VarT inst_a_types) inst_e_types
  
  -- Unify with the actual type
  let actual_type = varApp (dataConTyCon dcon_type) type_arguments
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
  field_wrappers <- forM actual_fields $ \(rrepr ::: rtype) -> do
    field_var <- newAnonymousVar ObjectLevel
    let pattern = memVarP field_var (returnReprToParamRepr rrepr ::: rtype)
    wrapPattern pattern

  -- Construct the return value
  repr <- instantiatedReprDict (inst_repr ::: actual_type)
  let ty_args = map TypM actual_a_types
      ex_types = [TyPatM v ty | ValPT (Just v) ::: ty <- ex_params]
  return $ DeconWP repr (dataConCon dcon_type) ty_args ex_types field_wrappers
  where
    num_universal_types = length $ dataConPatternParams dcon_type
    num_existential_types = length $ dataConPatternExTypes dcon_type

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
    wrap_pats <- wrapPatterns params
    
    -- Flatten functions inside the function body
    fun_body <- flattenInExp $ funBody fun
    let fun' = fun {funBody = fun_body}

    -- Construct wrapper, if it's beneficial
    if all isIdWrapper wrap_pats
      then do
        return (Nothing, Def fun_name (FunM fun'))
      else do
        worker@(Def worker_name _) <-
          mkWorkerFunction ty_params wrap_pats fun_name (FunM fun')
        wrapper <-
          mkWrapperFunction ty_params wrap_pats fun_name ret worker_name
        return (Just worker, wrapper)

mkWorkerFunction :: [TyPatM] -> [WrapPat] -> Var -> FunM -> AF (Def Mem)
mkWorkerFunction original_ty_params wrap_pats wrapper_name (FunM original_fun) = do
  -- Create a new variable for the worker
  worker_name <- newClonedVar wrapper_name
  
  -- Re-wrap the unwrapped arguments
  let wrap_context = concatMap (fst . rewrapPattern) wrap_pats
      wrapped_body = applyContext wrap_context $ funBody original_fun
      (ty_params, val_params) = unwrappedParameters wrap_pats
      
      wrap_fn = FunM $ Fun (funInfo original_fun)
                (original_ty_params ++ ty_params) val_params
                (funReturn original_fun) wrapped_body

  return $ Def worker_name wrap_fn

mkWrapperFunction :: [TyPatM] -> [WrapPat] -> Var -> RetM -> Var -> AF (Def Mem)
mkWrapperFunction original_ty_params wrap_pats wrapper_name worker_ret worker_name =
  let unwrap_context = concatMap unwrapPattern wrap_pats
      
      -- Create a call to the worker
      (call_ty_args, call_args) = unwrappedArguments wrap_pats
      orig_ty_args = [TypM t | TyPatM _ t <- original_ty_params]
      call = ExpM $ AppE defaultExpInfo (ExpM $ VarE defaultExpInfo worker_name)
             (orig_ty_args ++ call_ty_args) call_args
      
      -- Create the wrapper function
      wrapper_body = applyContext unwrap_context call
      wrapper_fun = FunM $ Fun defaultExpInfo original_ty_params
                    [pat | WrapPat pat _ <- wrap_pats] worker_ret wrapper_body
  in return $ Def wrapper_name wrapper_fun

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