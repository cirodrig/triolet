{-| Generation of low-level code from memory IR.
-}

{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, Rank2Types #-}
module SystemF.Lowering.Lowering2(lowerModule)
where

import Control.Monad
import Control.Monad.Trans
import qualified Data.IntMap as IntMap
import Data.List
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Label
import Common.Supply
import Builtins.Builtins
import LowLevel.Build
import qualified LowLevel.Builtins as LL
import qualified LowLevel.Intrinsics as LL
import qualified LowLevel.Syntax as LL
import qualified LowLevel.CodeTypes as LL
import qualified LowLevel.Records as LL
import qualified LowLevel.Print as LL
import SystemF.Lowering.Datatypes2
import SystemF.Lowering.Marshaling
import SystemF.Lowering.LowerMonad
import qualified SystemF.DictEnv as DictEnv
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import SystemF.TypecheckMem
import Type.Environment
import Type.Eval
import Type.Type
import Type.Var
import Globals
import GlobalVar
import Export

withMany :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c
withMany f xs k = go xs k
  where
    go (x:xs) k = f x $ \y -> go xs $ \ys -> k (y:ys)
    go []     k = k []

-- | Called by 'assumeVar' and related functions.  If the type is a
--   Repr dictionary passed as a boxed pointer or an IndexedInt passed as
--   a value, record the dictionary in the environment.
--   Otherwise don't change the environment.
assumeSingletonValue :: ReturnType -> LL.Var -> Lower a -> Lower a
assumeSingletonValue (repr ::: ty) bound_var m =
  case repr
  of BoxRT
       | Just (con, [arg]) <- fromVarApp ty,
         con `isPyonBuiltin` the_Repr ->
           assumeReprDict arg (LL.VarV bound_var) m
     ValRT
       | Just (con, [arg]) <- fromVarApp ty,
         con `isPyonBuiltin` the_IndexedInt ->
           assumeIndexedInt arg (LL.VarV bound_var) m
     _ -> m

assumeVarG :: Var -> ReturnType -> (LL.Var -> GenLower a) -> GenLower a
assumeVarG v return_type k = liftT1 (assumeVar v return_type) k

-- | Create a lowered variable corresponding to the given variable, and
--   add it to the environment so it can be looked up.
--   If it's a Repr dictionary, add that to the environment also.
assumeVar :: Var -> ReturnType -> (LL.Var -> Lower a) -> Lower a
assumeVar v rt k = do
  rtype <- lowerReturnType rt 
  case rtype of
    Just t -> assumeVariableWithType v t $ \ll_var ->
      assumeSingletonValue rt ll_var (k ll_var)
    Nothing -> internalError "assumeVar: Unexpected representation"

-- | Create a local, dynamically allocated variable for a let expression.
--   The variable points to some uninitialized memory of the correct type for
--   its size.
assumeLocalVar :: Var           -- ^ The variable name
               -> LL.Val        -- ^ The variable size (unsigned native int)
               -> (LL.Var -> GenLower a) -- ^ Code using the variable
               -> GenLower a
assumeLocalVar v v_size k =
  liftT1 (assumeVariableWithType v (LL.PrimType LL.PointerType)) $ \ll_var -> do
    allocateHeapMemAs v_size ll_var
    x <- k ll_var
    deallocateHeapMem (LL.VarV ll_var)
    return x

-- | Create an anonymous variable for a wildcard pattern. 
assumeWildVar :: ReturnType -> (LL.Var -> Lower a) -> Lower a
assumeWildVar rt k = do
  rtype <- lowerReturnType rt 
  case rtype of
    Just ty -> LL.newAnonymousVar ty >>= k
    Nothing -> internalError "assumeWildVar: Unexpected representation"

-- | Code can return a value, or \"return\" by producing a side effect
data RetVal = RetVal !LL.Val | NoVal

fromRetVal (RetVal v) = v
fromRetVal NoVal = internalError "fromRetVal"

listToRetVal :: [LL.Val] -> RetVal
listToRetVal [] = NoVal
listToRetVal [val] = RetVal val
listToRetVal _ = internalError "listToRetVal"

retValToList :: RetVal -> [LL.Val]
retValToList NoVal = []
retValToList (RetVal val) = [val]

-------------------------------------------------------------------------------
-- Data types

-- | Compile a data constructor.  If the data constructor takes no   
--   arguments, the constructor value is returned; otherwise a function 
--   is returned.  All type arguments must be provided.
compileConstructor :: Var -> DataConType -> [Type] -> GenLower RetVal
compileConstructor con con_type ty_args = lift $ do
  let (field_types, result_type) =
        instantiateDataConTypeWithExistentials con_type ty_args
  layout <- getAlgLayout result_type
  fmap RetVal $ algebraicIntro layout con

compileStore store_type value address = do
  layout <- lift $ getLayout (ValRT ::: store_type)
  dat <- lowerExpToVal value
  ptr <- lowerExpToVal address
  storeValue layout dat ptr
  return NoVal

compileStoreFunction store_type value = do
  addr_param <- LL.newAnonymousVar (LL.PrimType LL.PointerType)
  body <- execBuild [] $ do
    layout <- lift $ getLayout (ValRT ::: store_type)
    dat <- lowerExpToVal value
    storeValue layout dat (LL.VarV addr_param)
    return $ LL.ReturnE $ LL.ValA []
  let fun = LL.closureFun [addr_param] [] body
  return $ RetVal $ LL.LamV fun

compileLoad load_type address = do
  layout <- lift $ getLayout (ValRT ::: load_type)
  ptr <- lowerExpToVal address
  fmap RetVal $ loadValue layout ptr

compileCase :: ReturnType       -- ^ Case statement result type
            -> ReturnType       -- ^ Scrutinee type
            -> LL.Val
            -> [(Var, [RetVal] -> GenLower RetVal)]
            -> GenLower RetVal
compileCase result_type scrutinee_type scrutinee_val branches = do
  layout <- lift $ getAlgLayout scrutinee_type
  rtypes <- lift $ lowerReturnTypeList result_type
  rparams <- lift $ mapM LL.newAnonymousVar rtypes
  getContinuation True rparams $ \cont ->
    algebraicElim layout scrutinee_val $
    map (elim_branch rparams cont) branches
  return $ case rparams
           of []  -> NoVal
              [v] -> RetVal (LL.VarV v)
  where
    elim_branch rparams cont (con, mk_branch) = (con, mk_branch')
      where
        mk_branch' args = do
          -- Generate code
          result <- mk_branch (map RetVal args)
          
          -- Assign return values
          case (result, rparams) of
            (NoVal, [])      -> return ()
            (RetVal v, [rv]) -> bindAtom1 rv $ LL.ValA [v]

          -- Execute the continuation
          return cont

-------------------------------------------------------------------------------
-- Lowering

bindPatterns pats m = foldr (uncurry bindPattern) m pats

-- | Bind a pattern-bound variable to the result of some code
bindPattern :: PatM -> RetVal -> GenLower a -> GenLower a
bindPattern _ NoVal _ = internalError "bindPattern: Nothing to bind"

bindPattern (MemVarP v (repr ::: ty) _) (RetVal value) m = do
  assumeVarG v (paramReprToReturnRepr repr ::: ty) $ \ll_var -> do
    bindAtom1 ll_var (LL.ValA [value])
    m

bindPattern (MemWildP _) value m = m

-- | Lower a type that is passed as an argument to an expression.
--   In most cases, the type becomes a unit value.
lowerTypeToVal :: TypTM -> GenLower LL.Val
lowerTypeToVal _ = return $ LL.LitV LL.UnitL

lowerExpToVal :: ExpTM -> GenLower LL.Val
lowerExpToVal expression = do
  rv <- lowerExp expression
  case rv of RetVal val -> return val
             NoVal -> internalError "lowerExpToVal"

lowerExp :: ExpTM -> GenLower RetVal
lowerExp (ExpTM (RTypeAnn return_type expression)) =
  case expression
  of VarE _ v -> lowerVar return_type v
     LitE _ l -> lowerLit return_type l
     
     -- Special-case handling of load and store functions
     AppE _ (ExpTM (RTypeAnn _ (VarE _ op))) ty_args args 
       | op `isPyonBuiltin` the_store ->
           case (ty_args, args)
           of ([TypTM (RTypeAnn _ store_type)], [value, address]) ->
                compileStore store_type value address
              ([TypTM (RTypeAnn _ store_type)], [value]) ->
                lift $ compileStoreFunction store_type value
              _ -> internalError "lowerExp: Wrong number of arguments to store"
       | op `isPyonBuiltin` the_load ->
           case (ty_args, args)
           of ([TypTM (RTypeAnn _ load_type)], [address]) ->
                compileLoad load_type address
              _ -> internalError "loadExp: Wrong number of arguments to load"
     AppE _ op ty_args args -> lowerApp return_type op ty_args args
     LamE _ f -> lift $ lowerLam return_type f
     LetE _ binder rhs body -> lowerLet return_type binder rhs body
     LetfunE _ defs body -> lowerLetrec return_type defs body
     CaseE _ scr alts -> lowerCase return_type scr alts
     ExceptE _ _ -> lowerExcept return_type

lowerVar _ v =
  case LL.lowerIntrinsicOp v
  of Just lower_var -> lift $ fmap RetVal lower_var
     Nothing -> do
       tenv <- lift getTypeEnv
       case lookupDataCon v tenv of
         Just data_con ->
           -- A constructor with no type arguments.
           -- Constructors taking type arguments should be
           -- processed by 'lowerApp'.
           compileConstructor v data_con []
         Nothing -> lift $ do ll_v <- lookupVar v
                              return $ RetVal (LL.VarV ll_v)

lowerLit _ lit =
  case lit
  of IntL n ty ->
       case fromVarApp ty
       of Just (con, [])
            | con `isPyonBuiltin` the_int ->
              return $ RetVal (LL.LitV $ LL.IntL LL.Signed LL.pyonIntSize n)
     FloatL n ty ->
       case fromVarApp ty
       of Just (con, [])
            | con `isPyonBuiltin` the_float ->
              return $ RetVal (LL.LitV $ LL.FloatL LL.pyonFloatSize n)

lowerApp rt op ty_args args = do
  tenv <- lift getTypeEnv
  
  -- The operator is either a function or a data constructor
  case op of
    ExpTM (RTypeAnn _ (VarE _ op_var)) 
      | Just op_data_con <- lookupDataCon op_var tenv ->
          lower_data_constructor tenv op_var op_data_con
    _ -> lower_function tenv
  where
    lower_data_constructor tenv op_var op_data_con = do
      let argument_types = [t | TypTM (RTypeAnn _ t) <- ty_args]
      op'     <- compileConstructor op_var op_data_con argument_types
      args'   <- mapM lowerExpToVal args
      returns <- lift $ lowerReturnTypeList rt
      retvals <- emitAtom returns $ LL.closureCallA (fromRetVal op') args'
      return $ listToRetVal retvals

    lower_function tenv = do
      op'      <- lowerExpToVal op
      ty_args' <- mapM lowerTypeToVal ty_args
      args'    <- mapM lowerExpToVal args
      returns  <- lift $ lowerReturnTypeList rt
      retvals  <- emitAtom returns $ LL.closureCallA op' (ty_args' ++ args')
      return $ listToRetVal retvals

lowerLam _ f = do
  f' <- lowerFun f
  return $ RetVal (LL.LamV f')

lowerLet _ binder rhs body =
  case binder
  of TypedMemVarP {} -> do
       rhs_code <- lowerExp rhs
       bindPattern (fromPatTM binder) rhs_code $ lowerExp body

     TypedLocalVarP v ty repr_dict -> do
       -- Get the size of the local variable's data
       dict_val <- lowerExpToVal repr_dict
       local_size <- selectPassConvSize dict_val
       
       -- Allocate local memory, then generate the rhs and body code
       assumeLocalVar v local_size $ \ll_var -> do
         -- The lowered RHS should not return anything
         result <- lowerExp rhs
         let debug_rhs_type = case rhs of ExpTM (RTypeAnn rtype _) -> rtype
         case result of NoVal -> return ()
                        _ -> internalError "lowerLet"
         
         -- If it's a dictionary variable, add it to the environment while
         -- generating code of the body.
         -- Force all body code to be generated here.
         liftT (assumeSingletonValue (ReadRT ::: ty) ll_var) $
           lowerExp body

     TypedMemWildP {} ->
       internalError "lowerLet"

lowerLetrec _ defs body =
  lowerDefGroupG defs $ \defs' -> do
    emitLetrec defs'
    lowerExp body

lowerCase return_type scr alts = do
  let ExpTM (RTypeAnn scrutinee_type _) = scr
  scr_val <- lowerExpToVal scr
  compileCase return_type scrutinee_type scr_val (map lowerAlt alts)

lowerAlt (AltTM (RTypeAnn return_type alt)) =
  (altConstructor alt, lowerAltBody return_type alt)

lowerAltBody return_type alt field_values =
  -- Type arguments are ignored
  -- Bind the field values and generate the body
  let params = map fromPatTM $ altParams alt
  in bindPatterns (zip params field_values) $ lowerExp $ altBody alt

lowerExcept return_type = do
  -- Call exit() and return a value, which is never used
  -- The call is commented out because we perform unsafe code reordering.
  -- Fix it!
  -- emitAtom0 $ LL.primCallA (LL.VarV (LL.llBuiltin LL.the_prim_exit))
  --  [nativeIntV (-1)]
  return_value
  where
    -- Create a value of the correct low-level type.  Since this code is dead,
    -- the value is never used.
    return_value =
      case return_type
      of ReadRT ::: _ -> fmap RetVal $
                         return_ll_value (LL.PrimType LL.PointerType)
         OutRT ::: _ -> fmap RetVal $
                        return_ll_value (LL.PrimType LL.PointerType)
         BoxRT ::: _ -> fmap RetVal $
                        return_ll_value (LL.PrimType LL.OwnedType)
         ValRT ::: rtype -> do
           layout <- lift $ getLayout return_type
           case layout of
             ValLayout vtype -> fmap RetVal $ return_ll_value vtype
             MemLayout _ -> internalError "lowerExcept"
         SideEffectRT ::: _ -> return NoVal

    -- Return a value of the desired type.  The actual value is unimportant
    -- because we're generating dead code.
    return_ll_value (LL.PrimType pt) =
      case pt
      of LL.PointerType -> return $ LL.LitV LL.NullL
         LL.OwnedType -> emitAtom1 (LL.PrimType LL.OwnedType) $
                         LL.PrimA LL.PrimCastToOwned [LL.LitV LL.NullL]
         LL.UnitType -> return $ LL.LitV LL.UnitL
         LL.BoolType -> return $ LL.LitV (LL.BoolL False)
         LL.IntType sgn sz -> return $ LL.LitV (LL.IntL sgn sz 0)
         LL.FloatType sz -> return $ LL.LitV (LL.FloatL sz 0)

    return_ll_value (LL.RecordType recd) = do
      fields <- mapM (return_ll_value . to_value_type . LL.fieldType) $ 
                LL.recordFields recd
      return $ LL.RecV recd fields
      where
        to_value_type (LL.PrimField pt) = LL.PrimType pt
        to_value_type (LL.RecordField rt) = LL.RecordType rt

lowerFun :: FunTM -> Lower LL.Fun
lowerFun (FunTM (RTypeAnn _ fun)) =
  withMany lower_type_param (funTyParams fun) $ \ty_params ->
  withMany lower_param (funParams fun) $ \params -> do
    returns <- lowerReturnTypeList $ fromRetTM $ funReturn fun
    genClosureFun (ty_params ++ params) returns $ lower_body (funBody fun)
  where
    -- Types are passed, but not used.  Lower them to the unit value.
    lower_type_param (TyPatTM a kind) k = do
      param_var <- LL.newAnonymousVar (LL.PrimType LL.UnitType)
      assumeType a (fromTypTM kind) $ k param_var 
      
    lower_param (TypedMemVarP v (param_repr ::: ty)) k =
      assumeVar v (paramReprToReturnRepr param_repr ::: ty) k

    lower_param (TypedMemWildP (param_repr ::: ty)) k =
      assumeWildVar (paramReprToReturnRepr param_repr ::: ty) k

    lower_param (TypedLocalVarP {}) _ =
      internalError "lowerFun: Unexpected local variable"
    
    lower_body body = do
      ret_val <- lowerExp body
      return (LL.ReturnE $ LL.ValA $ retValToList ret_val)

-- | Lower a definition group.
lowerDefGroup :: DefGroup (Def (Typed Mem))
              -> (LL.Group LL.FunDef -> Lower a)
              -> Lower a
lowerDefGroup defgroup k = 
  case defgroup
  of NonRec def -> do
       -- Lower the function before adding the variable to the environment
       f' <- lowerFun $ definiens def
       assume_variable def $ \v' -> k (LL.NonRec (LL.Def v' f'))
     Rec defs ->
       -- Add all variables to the environment, then lower
       assume_variables defs $ \vs' -> do
         fs' <- mapM (lowerFun . definiens) defs
         k $ LL.Rec $ zipWith LL.Def vs' fs'
  where
    assume_variables defs k = withMany assume_variable defs k

    assume_variable (Def v _ (FunTM (RTypeAnn return_type _))) k =
      assumeVar v return_type k

lowerDefGroupG :: DefGroup (Def (Typed Mem))
               -> (LL.Group LL.FunDef -> GenLower a)
               -> GenLower a
lowerDefGroupG defs = liftT1 (lowerDefGroup defs)

lowerExport :: ModuleName
            -> Export (Typed Mem)
            -> Lower (LL.FunDef, (LL.Var, ExportSig))
lowerExport module_name (Export pos (ExportSpec lang exported_name) fun) = do
  fun' <- lowerFun fun
  fun_def <- case lang of CCall -> define_c_fun fun'
  return (fun_def, (LL.definiendum fun_def, export_sig))
  where
    fun_type = case fun of FunTM (RTypeAnn (BoxRT ::: fun_type) _) -> fun_type
    export_sig = getCExportSig fun_type

    define_c_fun fun = do
      -- Generate marshalling code
      wrapped_fun <- createCMarshalingFunction export_sig fun

      -- Create function name.  Function is exported with the given name.
      let label = externPyonLabel module_name exported_name (Just exported_name)
      v <- LL.newExternalVar label (LL.PrimType LL.PointerType)
      return $ LL.Def v wrapped_fun

lowerModuleCode :: ModuleName 
                -> [DefGroup (Def (Typed Mem))]
                -> [Export (Typed Mem)]
                -> Lower ([LL.Group LL.FunDef], [(LL.Var, ExportSig)])
lowerModuleCode module_name defss exports = lower_definitions defss
  where
    lower_definitions (defs:defss) =
      lowerDefGroup defs $ \defs' -> do
        (defss', export_sigs) <- lower_definitions defss
        return (defs' : defss', export_sigs)

    lower_definitions [] = do
      ll_exports <- mapM (lowerExport module_name) exports
      let (functions, signatures) = unzip ll_exports
      return ([LL.Rec functions], signatures)

lowerModule :: Module (Typed Mem) -> IO LL.Module
lowerModule (Module mod_name globals exports) = do
  (ll_functions, ll_export_sigs) <-
    withTheNewVarIdentSupply $ \var_supply ->
    withTheLLVarIdentSupply $ \ll_var_supply -> do
      global_types <- readInitGlobalVarIO the_memTypes
      global_map <- readInitGlobalVarIO the_loweringMap
      env <- initializeLowerEnv var_supply ll_var_supply global_types global_map
      runLowering env $ lowerModuleCode mod_name globals exports

  ll_name_supply <- newLocalIDSupply  

  return $ LL.Module { LL.moduleModuleName = mod_name
                     , LL.moduleNameSupply = ll_name_supply
                     , LL.moduleImports = LL.allBuiltinImports
                     , LL.moduleGlobals = map (fmap LL.GlobalFunDef) 
                                          ll_functions
                     , LL.moduleExports = ll_export_sigs}

