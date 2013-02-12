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
assumeSingletonValue :: Type -> LL.Var -> Lower a -> Lower a
assumeSingletonValue ty bound_var m =
  case fromVarApp ty
  of Just (con, [arg])
       | con `isCoreBuiltin` The_Repr ->
           assumeReprDict arg (LL.VarV bound_var) m
       | con `isCoreBuiltin` The_FIInt ->
           assumeIndexedInt arg (LL.VarV bound_var) m
     _ -> m

assumeVarG :: Bool -> Var -> Type -> (LL.Var -> GenLower a) -> GenLower a
assumeVarG is_exported v ty k = liftT1 (assumeVar is_exported v ty) k

-- | Create a lowered variable corresponding to the given variable, and
--   add it to the environment so it can be looked up.
--   If it's a Repr dictionary, add that to the environment also.
assumeVar :: Bool -> Var -> Type -> (LL.Var -> Lower a) -> Lower a
assumeVar is_exported v rt k = do
  tenv <- getTypeEnv
  rtype <- lowerType tenv rt 
  case rtype of
    Just t -> assumeVariableWithType is_exported v rt t $ \ll_var ->
      assumeSingletonValue rt ll_var (k ll_var)
    Nothing -> internalError "assumeVar: Unexpected representation"

assumeTyParam :: TypeEnvMonad m => TyPat -> m a -> m a
assumeTyParam (TyPat b) m = assumeBinder b m

assumeTyParams ps m = foldr assumeTyParam m ps

{-
-- | Create a local, dynamically allocated variable for a let expression.
--   The variable points to some uninitialized memory of the correct type for
--   its size.
assumeLocalVar :: Var           -- ^ The variable name
               -> LL.Val        -- ^ The variable size (unsigned native int)
               -> LL.Val        -- ^ The variable pointerlessness (bool)
               -> (LL.Var -> GenLower a) -- ^ Code using the variable
               -> GenLower a
assumeLocalVar v v_size is_pointerless k =
  liftT1 (assumeVariableWithType v (LL.PrimType LL.PointerType)) $ \ll_var -> do
    allocateHeapMemAs v_size is_pointerless ll_var
    x <- k ll_var
    deallocateHeapMem (LL.VarV ll_var)
    return x-}

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
compileConstructor :: LayoutCon -> Type -> [LL.Val] -> GenLower RetVal
compileConstructor con data_type args = do
  tenv <- lift getTypeEnv
  layout <- lift $ getAlgLayout tenv data_type
  fmap RetVal $ algebraicIntro layout con args

compileCase :: Type             -- ^ Case statement result type
            -> Type             -- ^ Scrutinee type
            -> LL.Val           -- ^ Scrutinee value
            -> [(LayoutCon, [RetVal] -> GenLower RetVal)]
            -> GenLower RetVal
compileCase result_type scrutinee_type scrutinee_val branches = do
  tenv <- lift getTypeEnv
  layout <- lift $ getAlgLayout tenv scrutinee_type
  rtypes <- lift $ lowerType tenv result_type
  rparams <- lift $ mapM LL.newAnonymousVar (maybeToList rtypes)
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

bindPattern (PatM (v ::: ty) _) (RetVal value) m = do
  assumeVarG False v ty $ \ll_var -> do
    bindAtom1 ll_var (LL.ValA [value])
    m

-- | Lower an expression to a constant value, without generating any code.
lowerConstantExp :: Maybe Label -> ExpM -> Lower (LL.Val, [LL.GlobalDef], Bool)
lowerConstantExp m_name expression =
  case fromExpM expression
  of VarE _ v -> do val <- lowerNonIntrinsicVar v
                    return (val, [], True)
     LitE _ l -> return (lowerLit l, [], True)
     ConE _ con args -> do
       -- Compute the constructed value's type
       result_type <- getConType con
       tenv <- getTypeEnv
       layout <- getAlgLayout tenv result_type

       -- Create a static value
       let layout_con = layoutCon $ summarizeConstructor con
       lowered_args <- mapM (lowerConstantExp Nothing) args
       let (arg_vals, arg_defss, _) = unzip3 lowered_args
       (con_value, con_defs, is_value) <-
         staticObject m_name layout layout_con arg_vals
       return (con_value, concat arg_defss ++ con_defs, is_value)

lowerExpToVal :: ExpM -> GenLower LL.Val
lowerExpToVal expression = do
  rv <- lowerExp expression
  case rv of RetVal val -> return val
             NoVal -> internalError "lowerExpToVal"

lowerExp :: ExpM -> GenLower RetVal
lowerExp expression =
  case fromExpM expression
  of VarE _ v -> lowerVar v
     LitE _ l -> return $ RetVal $ lowerLit l
     ConE _ con args -> lowerCon con args
     AppE _ op ty_args args -> do
       ty <- lift $ inferExpType expression
       lowerApp ty op ty_args args
     LamE _ f -> lowerLam f
     LetE _ binder rhs body -> lowerLet binder rhs body
     LetfunE _ defs body -> lowerLetrec defs body
     CaseE _ scr alts -> do 
       ty <- lift $ inferExpType expression
       lowerCase ty scr alts
     ExceptE _ ty -> lowerExcept ty
     -- Coercions are lowered to a no-op
     CoerceE _ _ _ e -> lowerExp e
     ArrayE _ ty es -> lowerArray ty es

lowerVar v =
  case LL.lowerIntrinsicOp v
  of Just lower_var -> do xs <- lower_var []
                          return $ listToRetVal xs
     Nothing -> lift $ liftM RetVal $ lowerNonIntrinsicVar v
  
lowerNonIntrinsicVar v = do
  ll_v <- lookupVar v
  return $ LL.VarV ll_v

lowerLit :: Lit -> LL.Val
lowerLit lit =
  case lit
  of IntL n ty ->
       case fromVarApp ty
       of Just (con, [])
            | con == intV ->
              LL.LitV $ LL.IntL LL.Signed LL.trioletIntSize n
     FloatL n ty ->
       case fromVarApp ty
       of Just (con, [])
            | con == floatV ->
              LL.LitV $ LL.FloatL LL.trioletFloatSize n

-- | Lower a data constructor application.  Generate code to construct a value.

-- Lower arguments, then pack the result values into a record value
lowerCon con args = do
  result_type <- lift (getConType con)
  arg_values <- mapM lowerExpToVal args
  let layout_con = layoutCon $ summarizeConstructor con
  compileConstructor layout_con result_type arg_values

getConType (TupleCon ty_args) = do
  tenv <- getTypeEnv
  let arg_kinds = map (toBaseKind . typeKind tenv) ty_args
  return $ typeApp (UTupleT arg_kinds) ty_args

getConType (VarCon op ty_args ex_types) = do
  tenv <- getTypeEnv
  let Just op_data_con = lookupDataCon op tenv
  (_, result_type) <-
    instantiateDataConTypeWithExistentials
    op_data_con (ty_args ++ ex_types)
  return result_type

{-  let record_type = LL.constStaticRecord $
                    map (LL.valueToFieldType . LL.valType) arg_values
  tuple_val <- emitAtom1 (LL.RecordType record_type) $
               LL.PackA record_type arg_values-}

-- | Lower an application term.
--
--   Data constructor applications are lowered using 'compileConstructor'.
--   Function applications (with value arguments)
--   are lowered to a function call.
--
--   Type applications are erased, so if there are  with no arguments are 
lowerApp :: Type -> ExpM -> [Type] -> [ExpM] -> GenLower RetVal

lowerApp rt (ExpM (VarE _ op_var)) ty_args args
  | Just mk_code <- LL.lowerIntrinsicOp op_var = do
      -- Lower the intrinsic operation
      xs <- mk_code =<< mapM lowerExpToVal args
      return $ listToRetVal xs

lowerApp rt op ty_args args = do
  -- Lower the operator expression
  op' <- lowerExp op

  -- If function arguments were given, then generate a function call
  if null args then return op' else do
    args'   <- mapM lowerExpToVal args
    tenv    <- lift getTypeEnv
    returns <- lift $ lowerType tenv rt
    retvals <- emitAtom (maybeToList returns) $
               LL.closureCallA (fromRetVal op') args'
    return $ listToRetVal retvals

lowerLam f = do
  f' <- emitLambda =<< lift (lowerFun f)
  return $ RetVal (LL.VarV f')

lowerLet binder rhs body = do
  rhs_code <- lowerExp rhs
  bindPattern binder rhs_code $ lowerExp body

lowerLetrec defs body =
  lowerDefGroupG defs $ \defs' -> do
    emitLetrec defs'
    lowerExp body

lowerCase return_type scr alts = do
  scrutinee_type <- lift $ inferExpType scr
  scr_val <- lowerExpToVal scr
  compileCase return_type scrutinee_type scr_val (map lowerAlt alts)

lowerAlt (AltM alt) =
  let con = layoutCon $ summarizeDeconstructor $ altCon alt
  in (con, lowerAltBody alt)

lowerAltBody alt field_values =
  -- Bind the field values and generate the body
  let params = altParams alt
  in assumeBinders (deConExTypes (altCon alt)) $
     bindPatterns (zip params field_values) $
     lowerExp $ altBody alt

lowerExcept return_type = do
  -- Throw an exception
  emitThrow (nativeIntV (-1))

  -- Return a value.  The return value is dead code, but is expected by the
  -- lowering process.
  tenv <- lift getTypeEnv
  lowered_type <- lift $ lowerType tenv return_type
  case lowered_type of
    Nothing -> return NoVal
    Just vt -> fmap RetVal $ return_ll_value vt
  where
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

lowerArray :: Type -> [ExpM] -> GenLower RetVal
lowerArray ty es = do
  -- Create an initializer function
  val <- genLambda [LL.PrimType LL.PointerType] [LL.PrimType LL.UnitType] $ \[ret_param] -> do
    -- Compute the size of one array element, including padding
    elt_layout <- lift $ getLayout ty
    (elt_size, elt_alignment) <- layoutSize elt_layout
    
    -- Add padding to size of array elements
    i_size <- primCastZ (LL.PrimType LL.nativeIntType) elt_size
    i_padded_size <- addRecordPadding i_size elt_alignment
    padded_size <- primCastZ (LL.PrimType LL.nativeWordType) i_padded_size

    -- Write the array
    write_array_elements padded_size ret_param es
  return $ RetVal val
  where
    -- Write all array elements to the appropriate offsets
    write_array_elements size ptr (e:es) = do
      -- Write e
      RetVal f <- lowerExp e
      emitAtom1 (LL.PrimType LL.PointerType) $ LL.closureCallA f [ptr]

      -- Get pointer to next array element
      ptr' <- primAddP ptr size
      write_array_elements size ptr' es

    write_array_elements _ _ [] = return [LL.LitV LL.UnitL]

lowerFun :: FunM -> Lower LL.Fun
lowerFun (FunM fun) =
  assumeTyParams (funTyParams fun) $
  withMany lower_param (funParams fun) $ \params -> do
    tenv <- getTypeEnv
    returns <- lowerType tenv $ funReturn fun
    genClosureFun params (maybeToList returns) $ lower_body (funBody fun)
  where
    lower_param pat k = assumeVar False (patMVar pat) (patMType pat) k
    
    lower_body body = do
      ret_val <- lowerExp body
      return (LL.ReturnE $ LL.ValA $ retValToList ret_val)

lowerDefGroupG :: DefGroup (FDef Mem)
               -> (LL.Group LL.FunDef -> GenLower a)
               -> GenLower a
lowerDefGroupG defs = liftT1 (lowerDefGroup defs)

-- | Lower a local definition group.
lowerDefGroup :: DefGroup (FDef Mem)
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

    assume_variable (Def v annotation f) k
      -- Local functions cannot be exported
      | defAnnExported annotation =
          internalError "lowerDefGroup: Cannot export a local function"
      | otherwise =
          assumeVar False v (functionType f) k

lowerEntity :: Maybe Label -> Ent Mem -> Lower (LL.Var -> [LL.GlobalDef])
lowerEntity _ (FunEnt f) = do
  f' <- lowerFun f
  return (\ll_var -> [LL.GlobalFunDef (LL.Def ll_var f')])

lowerEntity lab (DataEnt d) = do
  (const_value, extra_defs, is_value) <- lowerConstantExp lab (constExp d)
  let global_def ll_var =
        LL.GlobalDataDef (LL.Def ll_var (LL.StaticData const_value))
  return $! if is_value
            then \_ -> extra_defs
            else \ll_var -> extra_defs ++ [global_def ll_var]

-- | Lower a global definition group.
--   The definitions and a list of exported functions are returned.
lowerGlobalDefGroup :: DefGroup (GDef Mem)
                    -> (LL.Group LL.GlobalDef -> [(LL.Var, ExportSig)] -> Lower a)
                    -> Lower a
lowerGlobalDefGroup defgroup k =
  case defgroup
  of NonRec def -> do
       -- Lower the entity before adding the variable to the environment
       let name = varName $ definiendum def
       mk_entity <- lowerEntity name $ definiens def
       assume_variable def $ \(v', m_export) ->
         k (LL.Rec (mk_entity v')) (maybeToList m_export)
     Rec defs ->
       -- Add all variables to the environment, then lower
       assume_variables defs $ \lowered -> do
         let (vs', m_exports) = unzip lowered
             exports = catMaybes m_exports
         entities <- forM (zip vs' defs) $ \(v', def) ->
           let name = varName $ definiendum def
           in liftM ($ v') $ lowerEntity name $ definiens def
         k (LL.Rec $ concat entities) exports
  where
    assume_variables defs k = withMany assume_variable defs k

    assume_variable (Def v annotation ent) k =
      -- Decide whether the function is exported
      let is_exported = defAnnExported annotation
          
          -- If exported, add it to the export list
          k' v
            | is_exported = k (v, Nothing)
            | otherwise = k (v, Just (v, TrioletExportSig))

          ty = case ent
               of FunEnt f  -> functionType f
                  DataEnt d -> constType d
      in assumeVar is_exported v ty k'

lowerExport :: ModuleName
            -> Export Mem
            -> Lower (LL.FunDef, (LL.Var, ExportSig))
lowerExport module_name (Export pos (ExportSpec lang exported_name) fun) = do
  fun' <- lowerFun fun
  tenv <- getTypeEnv
  
  -- Create exported function
  (fun_def, export_sig) <-
    case lang
    of CCall     -> define_c_fun tenv fun'
       CPlusPlus -> define_cxx_fun tenv fun'
  return (fun_def, (LL.definiendum fun_def, export_sig))
  where
    fun_type = functionType fun

    define_c_fun tenv fun = do
      -- Create export signature
      c_export_sig <- liftTypeEvalM $ getCExportSig fun_type

      -- Generate marshalling code
      wrapped_fun <- createCMarshalingFunction c_export_sig fun

      -- Create function name.  Function is exported with the given name.
      let label = externLabel module_name exported_name (Just exported_name)
      v <- LL.newExternalVar label (LL.PrimType LL.PointerType)
      return (LL.Def v wrapped_fun, CExportSig c_export_sig)

    define_cxx_fun tenv fun = do
      -- Create export signature
      cxx_export_sig <- liftTypeEvalM $ getCxxExportSig exported_name fun_type

      -- Generate marshalling code
      wrapped_fun <- createCxxMarshalingFunction cxx_export_sig fun

      -- Create a function name.  This isn't the name the user sees.
      -- The function with this name will be put into object code.  It will
      -- be called from some automatically generated C++ source code.
      let label = plainLabel module_name exported_name
      v <- LL.newExternalVar label (LL.PrimType LL.PointerType)
      return (LL.Def v wrapped_fun, CXXExportSig cxx_export_sig)

lowerModuleCode :: ModuleName 
                -> [DefGroup (GDef Mem)]
                -> [Export Mem]
                -> Lower ([LL.Group LL.GlobalDef], [(LL.Var, ExportSig)])
lowerModuleCode module_name defss exports = lower_definitions defss
  where
    lower_definitions (defs:defss) =
      lowerGlobalDefGroup defs $ \defs' exported_defs -> do
        (defss', export_sigs) <- lower_definitions defss
        return (defs' : defss', exported_defs ++ export_sigs)

    lower_definitions [] = do
      ll_exports <- mapM (lowerExport module_name) exports
      let (functions, signatures) = unzip ll_exports
      return ([LL.Rec (map LL.GlobalFunDef functions)], signatures)

lowerModule :: Module Mem -> IO LL.Module
lowerModule (Module { modName = mod_name
                    , modImports = imports
                    , modDefs = globals
                    , modExports = exports}) = do
  (ll_functions, ll_export_sigs) <-
    withTheNewVarIdentSupply $ \var_supply ->
    withTheLLVarIdentSupply $ \ll_var_supply -> do
      global_types <- readInitGlobalVarIO the_memTypes
      global_map <- readInitGlobalVarIO the_loweringMap
      env <- initializeLowerEnv var_supply ll_var_supply global_types global_map
      
      let all_defs = if False
                     then Rec imports : globals -- DEBUG: also lower imports
                     else globals
      runLowering env $ lowerModuleCode mod_name all_defs exports

  ll_name_supply <- newLocalIDSupply  

  return $ LL.Module { LL.moduleModuleName = mod_name
                     , LL.moduleNameSupply = ll_name_supply
                     , LL.moduleImports = LL.allBuiltinImports
                     , LL.moduleGlobals = ll_functions
                     , LL.moduleExports = ll_export_sigs}

