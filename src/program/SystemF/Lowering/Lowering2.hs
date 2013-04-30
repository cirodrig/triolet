{-| Generation of low-level code from memory IR.
-}

{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, Rank2Types #-}
module SystemF.Lowering.Lowering2(lowerModule)
where

import Prelude hiding(mapM, sequence)

import Control.Monad hiding(forM, mapM, sequence)
import Control.Monad.Trans
import qualified Data.IntMap as IntMap
import Data.List
import Data.Maybe
import Data.Traversable
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Label
import Common.MonadLogic
import Common.Supply
import Builtins.Builtins
import LowLevel.Build
import qualified LowLevel.Builtins as LL
import qualified LowLevel.Intrinsics as LL
import qualified LowLevel.Syntax as LL
import qualified LowLevel.CodeTypes as LL
import qualified LowLevel.Records as LL
import qualified LowLevel.Print as LL
import SystemF.Datatypes.Code hiding(runGen, SizeAlign, arraySize, unpackSizeAlign, addRecordPadding)
import SystemF.Datatypes.DynamicTypeInfo
import SystemF.Datatypes.InfoCall
import SystemF.Datatypes.Structure
import SystemF.Datatypes.Size
import SystemF.Datatypes.Layout
import SystemF.Datatypes.Util
--import SystemF.Lowering.Datatypes2
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

{-
-- | Compute the low-level representation of a variable or temporary value
--   that may be stored in a variable.  The type must be computable statically.
lowerType :: KindedType -> Lower LL.ValueType
lowerType (KindedType BoxK _)  = return $ LL.PrimType LL.OwnedType
lowerType (KindedType BareK _) = return $ LL.PrimType LL.PointerType
lowerType (KindedType ValK ty) = do
  -- Layout must be computable without relying on dynamic type information
  layout <- lowerAndGenerateNothing $
            computeLayout emptyTypeInfo ValK =<< computeStructure ty
  return $! layoutValueType layout

lowerType' :: Type -> Lower LL.ValueType
lowerType' ty = do
  k <- typeBaseKind ty
  lowerType $ KindedType k ty
-}

{-
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
-}

assumeVarG :: Bool -> Var -> Type -> (LL.Var -> GenLower a) -> GenLower a
assumeVarG is_exported v ty k = liftT1 (assumeVar is_exported v ty) k

-- | Create a lowered variable corresponding to the given variable, and
--   add it to the environment so it can be looked up.
--   If it's a Repr dictionary, add that to the environment also.
assumeVar :: Bool -> Var -> Type -> (LL.Var -> Lower a) -> Lower a
assumeVar is_exported v rt k = do
  rtype <- lowerLowerType rt
  assumeVariableWithType is_exported v rt rtype k

assumeTyParam :: TypeEnvMonad m => TyPat -> m a -> m a
assumeTyParam (TyPat b) m = assumeBinder b m

assumeTyParams ps m = foldr assumeTyParam m ps

-------------------------------------------------------------------------------
-- Data types

{-
-- | Compile a data constructor.  If the data constructor takes no   
--   arguments, the constructor value is returned; otherwise a function 
--   is returned.  All type arguments must be provided.
compileConstructor :: LayoutCon -> Type -> [LL.Val] -> GenLower RetVal
compileConstructor con data_type args = do
  layout <- lift $ getAlgLayout data_type
  fmap RetVal $ algebraicIntro layout con args

compileCase :: Type             -- ^ Case statement result type
            -> Type             -- ^ Scrutinee type
            -> LL.Val           -- ^ Scrutinee value
            -> [(LayoutCon, [RetVal] -> GenLower RetVal)]
            -> GenLower RetVal
compileCase result_type scrutinee_type scrutinee_val branches = do
  tenv <- lift getTypeEnv
  layout <- lift $ getAlgLayout scrutinee_type
  rtypes <- lift $ lowerType result_type
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
-}

-------------------------------------------------------------------------------
-- Lowering

bindPatterns pats m = foldr (uncurry bindPattern) m pats

-- | Bind a pattern-bound variable to the result of some code
bindPattern :: PatM -> LL.Val -> GenLower a -> GenLower a
bindPattern (PatM (v ::: ty) _) value m = do
  assumeVarG False v ty $ \ll_var -> do
    bindAtom1 ll_var (LL.ValA [value])
    m

bindPatternMaybe :: Maybe PatM -> Maybe LL.Val -> GenLower a -> GenLower a
bindPatternMaybe Nothing Nothing m = m
bindPatternMaybe (Just p) (Just v) m = bindPattern p v m

-- | Lower an expression to a constant value.
--   TODO: Generate a lazy term.
lowerConstantExp :: ExpM -> Lower (LL.Val, [LL.GlobalDef], Bool)
lowerConstantExp expression =
  internalError "lowerConstantExp: Not implemented"
{-
  case fromExpM expression
  of VarE _ v -> do val <- lowerNonIntrinsicVar v
                    return (val, [], True)
     LitE _ l -> return (lowerLit l, [], True)
     ConE _ con _ m_tyob args -> do
       -- Compute the constructed value's type and layout
       (_, result_type) <- conType con

       dyn_info <- case con
                   of VarCon op ty_args _ -> setupDynTypeInfo undefined
       s <- computeStructure result_type
       layout <- getAlgLayout result_type

       -- Create a static value
       let layout_con = layoutCon $ summarizeConstructor con
       lowered_args <- mapM (lowerConstantExp Nothing) args
       let (arg_vals, arg_defss, _) = unzip3 lowered_args
       (con_value, con_defs, is_value) <-
         staticObject m_name layout layout_con arg_vals
       return (con_value, concat arg_defss ++ con_defs, is_value)
-}

lowerExp :: ExpM -> GenLower LL.Val
lowerExp expression =
  case fromExpM expression
  of VarE _ v -> lowerVar v
     LitE _ l -> return $ lowerLit l
     ConE _ con sps ty_ob args -> lowerCon con sps ty_ob args
     AppE _ op ty_args args -> do
       ty <- lift $ inferExpType expression
       lowerApp ty op ty_args args
     LamE _ f -> lowerLam f
     LetE _ binder rhs body -> lowerLet binder rhs body
     LetfunE _ defs body -> lowerLetrec defs body
     CaseE _ scr sps alts -> do 
       ty <- lift . lowerLowerType =<< inferExpType expression
       lowerCase ty scr sps alts
     ExceptE _ ty -> lowerExcept ty
     -- Coercions are lowered to a no-op
     CoerceE _ _ _ e -> lowerExp e
     ArrayE _ ty es -> lowerArray ty es

lowerVar v =
  case LL.lowerIntrinsicOp v
  of Just lower_var -> lower_var []
     Nothing -> lift $ lowerNonIntrinsicVar v
  
lowerNonIntrinsicVar v = liftM LL.VarV $ lookupVar v

lowerLit :: Lit -> LL.Val
lowerLit lit =
  case lit
  of IntL n ty ->
       case fromVarApp ty
       of Just (con, [])
            | con == intV ->
              LL.LitV $ LL.IntL LL.Signed LL.trioletIntSize n
            | con == uintV ->
              LL.LitV $ LL.IntL LL.Unsigned LL.trioletIntSize n
     FloatL n ty ->
       case fromVarApp ty
       of Just (con, [])
            | con == floatV ->
              LL.LitV $ LL.FloatL LL.trioletFloatSize n

-- | Lower a data constructor application.  Generate code to construct a value.

-- Lower arguments, then pack the result values into a record value
lowerCon (VarCon op ty_args ex_types) sps ty_ob args = do
  -- Lower the arguments
  sps' <- mapM lowerExp sps
  ty_ob' <- mapM lowerExp ty_ob
  args' <- mapM lowerExp args

  -- Create a constructor term 
  Just op_data_con <- lookupDataCon op
  let data_type = dataConType op_data_con
      con_index = dataConIndex op_data_con
  return_type <- getReturnTypes
  lowerAndGenerateCode $ genConstructor data_type ty_args con_index sps' ty_ob' args'

lowerCon (TupleCon ty_args) [] Nothing args = do
  args' <- mapM lowerExp args

  -- Create a tuple value
  field_types <- lift $ mapM lowerLowerType ty_args
  packRecord (LL.constStaticRecord $ map LL.valueToFieldType field_types) args'

-- | Lower an application term.
--
--   Data constructor applications are lowered using 'compileConstructor'.
--   Function applications (with value arguments)
--   are lowered to a function call.
--
--   Type applications are erased, so if there are  with no arguments are 
lowerApp :: Type -> ExpM -> [Type] -> [ExpM] -> GenLower LL.Val

lowerApp rt (ExpM (VarE _ op_var)) ty_args args
  | Just mk_code <- LL.lowerIntrinsicOp op_var = do
      -- Lower the intrinsic operation
      mk_code =<< mapM lowerExp args

lowerApp rt op ty_args args = do
  -- Lower the operator expression
  op' <- lowerExp op

  -- If function arguments were given, then generate a function call
  if null args then return op' else do
    args'   <- mapM lowerExp args
    returns <- lift $ lowerLowerType rt
    emitAtom1 returns $ LL.closureCallA op' args'

lowerLam f = do
  f' <- emitLambda $ \v -> lowerFun v f
  return $ LL.VarV f'

lowerLet binder rhs body = do
  rhs_code <- lowerExp rhs
  bindPattern binder rhs_code $ lowerExp body

lowerLetrec defs body =
  lowerDefGroupG defs $ \defs' -> do
    emitLetrec defs'
    lowerExp body

lowerCase return_type scr sps alts = do
  scrutinee_type <- lift $ reduceToWhnf =<< inferExpType scr
  scr_val <- lowerExp scr
  sps' <- mapM lowerExp sps
  case fromTypeApp scrutinee_type of
    (VarT op_var, args) ->
      lowerAlgDataCase return_type op_var args sps' scr_val alts
    (UTupleT ks, args) ->
      lowerTupleCase return_type args scr_val alts

lowerAlgDataCase return_type op_var args sps scr_val alts = do
  Just data_type <- lookupDataType op_var
  -- TODO: Clean up these two calls
  lower_alt_wrapped <- embedIntoGenM (lower_alt data_type)
  lowerAndGenerateCode $
    genCase data_type args sps return_type scr_val (\ i ty_ob field_values -> lower_alt_wrapped (i, ty_ob, field_values))
  where
    lower_alt data_type (i, ty_ob, field_values) =
      -- Find the alternative for index 'i'
      let con = dataTypeDataConstructors data_type !! i
          match_alt (AltM (Alt (VarDeCon op _ _) _ _ _)) = op == con
          Just alt = find match_alt alts
      in lowerAlt alt ty_ob field_values

lowerTupleCase return_type args scr_val alts = do
  let [AltM (Alt (TupleDeCon field_types) Nothing params body)] = alts
  lowered_field_types <- lift $ mapM lowerLowerType field_types

  -- Unpack a tuple
  field_vals <- unpackRecord2 (LL.constStaticRecord $ map LL.valueToFieldType lowered_field_types) scr_val
  bindPatterns (zip params field_vals) $ lowerExp body

lowerAlt (AltM (Alt decon ty_ob_param params body)) ty_ob field_values =
  assumeBinders (deConExTypes decon) $
  bindPatternMaybe ty_ob_param ty_ob $
  bindPatterns (zip params field_values) $
  lowerExp body

lowerAltBody alt field_values =
  -- Bind the field values and generate the body
  let params = altParams alt
  in assumeBinders (deConExTypes (altCon alt)) $
     bindPatterns (zip params field_values) $
     lowerExp $ altBody alt

lowerExcept :: Type -> GenLower LL.Val
lowerExcept return_type = do
  -- Throw an exception
  emitThrow (nativeIntV (-1))

  -- Return a value.  The return value is dead code, but is expected by the
  -- lowering process.
  lowered_type <- lift $ lowerLowerType return_type
  return_ll_value lowered_type
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

lowerArray :: Type -> [ExpM] -> GenLower LL.Val
lowerArray ty es = do
  -- Create an initializer function
  val <- genLambda [LL.PrimType LL.PointerType] [LL.PrimType LL.UnitType] $ \[ret_param] -> do
    -- Compute the size of one array element, including padding
    -- FIXME: Use a size parameter on array literals
    elt_size_exp <- liftTypeEvalM $ runMaybeGen $
                    constructConstantSizeParameter (KindedType BareK ty)
    elt_size <- unpackSizeAlign =<< lowerExp elt_size_exp
    
    -- Add padding to size of array elements.
    -- This is done by computing the size of a one-element array.
    SizeAlign padded_size _ <-
      lowerAndGenerateCode $ arraySize (nativeWordV 1) elt_size

    -- Write the array
    write_array_elements padded_size ret_param es
  return val
  where
    -- Write all array elements to the appropriate offsets
    write_array_elements size ptr (e:es) = do
      -- Element is given as an initializer; write it
      f <- lowerExp e
      emitAtom1 (LL.PrimType LL.UnitType) $ LL.closureCallA f [ptr]

      -- Get pointer to next array element
      ptr' <- primAddP ptr size
      write_array_elements size ptr' es

    write_array_elements _ _ [] = return [LL.LitV LL.UnitL]

lowerFun :: LL.Var -> FunM -> Lower LL.Fun
lowerFun fun_name (FunM fun) =
  assumeTyParams (funTyParams fun) $
  withMany lower_param (funParams fun) $ \params -> do
    return_type <- lowerLowerType $ funReturn fun
    body <- execBuild [return_type] $ lower_body (funBody fun)
    newClosureFun fun_name params [return_type] body
  where
    lower_param pat k = assumeVar False (patMVar pat) (patMType pat) k
    
    lower_body body = do
      ret_val <- lowerExp body
      return (LL.ReturnE $ LL.ValA [ret_val])

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
       let sf_var = definiendum def
           sf_type = functionType $ definiens def
       lowered_type <- lowerLowerType sf_type
       v' <- translateVariable False sf_var lowered_type
       f' <- lowerFun v' $ definiens def
       assumeTranslatedVariable sf_var v' sf_type $ do
         k (LL.NonRec (LL.Def v' f'))
     Rec defs ->
       -- Add all variables to the environment, then lower
       assume_variables defs $ \vs' -> do
         fs' <- sequence [lowerFun v' $ definiens d | (v', d) <- zip vs' defs]
         k $ LL.Rec $ zipWith LL.Def vs' fs'
  where
    assume_variables defs k = withMany assume_variable defs k

    assume_variable (Def v annotation f) k
      -- Local functions cannot be exported
      | defAnnExported annotation =
          internalError "lowerDefGroup: Cannot export a local function"
      | otherwise =
          assumeVar False v (functionType f) k

lowerEntity :: LL.Var -> Ent Mem -> Lower [LL.GlobalDef]
lowerEntity ll_var (FunEnt f) = do
  f' <- lowerFun ll_var f
  return [LL.GlobalFunDef (LL.Def ll_var f')]

lowerEntity ll_var (DataEnt d) = do
  (const_value, extra_defs, is_value) <- lowerConstantExp (constExp d)
  let global_def =
        LL.GlobalDataDef (LL.Def ll_var (LL.StaticData const_value))
  return $! if is_value
            then extra_defs
            else extra_defs ++ [global_def]

-- | Lower a global definition group.
--   The definitions and a list of exported functions are returned.
lowerGlobalDefGroup :: DefGroup (GDef Mem)
                    -> (LL.Group LL.GlobalDef -> [(LL.Var, ExportSig)] -> Lower a)
                    -> Lower a
lowerGlobalDefGroup defgroup k =
  case defgroup
  of NonRec def -> do
       -- Translate the variable without adding it to the environment
       let name = definiendum def
           ent = definiens def
           sf_type = entityType ent
       ty <- lowerLowerType sf_type
       v <- translateVariable True name ty

       -- Lower the definition
       defs' <- lowerEntity v ent

       -- Add to environment and continue
       assumeTranslatedVariable name v sf_type $
         let defgroup' = LL.Rec defs'
             new_exports = pick_exports [(v, def)]
         in k defgroup' new_exports

     Rec defs ->
       -- Add all variables to the environment, then lower
       assume_variables defs $ \vs' -> do
         entities <- zipWithM lowerEntity vs' (map definiens defs)
         let defgroup' = LL.Rec $ concat entities
             exports = pick_exports $ zip vs' defs
         k defgroup' exports
  where
    pick_exports xs = [(v, sig) | (v, d) <- xs, sig <- maybeToList $ export_sig d]
      where
        export_sig d
          | defAnnExported $ defAnnotation d = Just TrioletExportSig
          | otherwise                        = Nothing

    assume_variables defs k = withMany assume_variable defs k

    assume_variable (Def v annotation ent) k =
      assumeVar (defAnnExported annotation) v (entityType ent) k

lowerExport :: ModuleName
            -> Export Mem
            -> Lower (LL.FunDef, (LL.Var, ExportSig))
lowerExport module_name (Export pos (ExportSpec lang exported_name) fun) = do
  -- Lower the given function.  The lowered function will be part of the  
  -- exported function.
  exported_fun_name <- LL.newAnonymousVar (LL.PrimType LL.OwnedType)
  fun' <- lowerFun exported_fun_name fun
  let fun_def = LL.Def exported_fun_name fun'
  
  -- Create exported function
  (fun_def, export_sig) <-
    case lang
    of CCall     -> define_c_fun exported_fun_name fun_def
       CPlusPlus -> define_cxx_fun exported_fun_name fun_def
  return (fun_def, (LL.definiendum fun_def, export_sig))
  where
    fun_type = functionType fun

    define_c_fun exported_fun_name fun_def = do
      -- Create export signature
      c_export_sig <- liftTypeEvalM $ getCExportSig fun_type

      -- Generate marshalling code
      wrapped_fun <- createCMarshalingFunction c_export_sig fun_def

      -- Create function name.  Function is exported with the given name.
      let label = externLabel module_name exported_name (Just exported_name)
      v <- LL.newExternalVar label (LL.PrimType LL.PointerType)
      return (LL.Def v wrapped_fun, CExportSig c_export_sig)

    define_cxx_fun exported_fun_name fun_def = do
      -- Create export signature
      cxx_export_sig <- liftTypeEvalM $ getCxxExportSig exported_name fun_type

      -- Generate marshalling code
      wrapped_fun <- createCxxMarshalingFunction cxx_export_sig fun_def

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
      i_global_types <- readInitGlobalVarIO the_memTypes
      global_types <- thawTypeEnv i_global_types
      global_map <- readInitGlobalVarIO the_loweringMap
      env <- initializeLowerEnv ll_var_supply global_map
      
      let all_defs = if False
                     then Rec imports : globals -- DEBUG: also lower imports
                     else globals
      runTypeEvalM (runLowering env $ lowerModuleCode mod_name all_defs exports)
        var_supply global_types

  ll_name_supply <- newLocalIDSupply  

  return $ LL.Module { LL.moduleModuleName = mod_name
                     , LL.moduleNameSupply = ll_name_supply
                     , LL.moduleImports = LL.allBuiltinImports
                     , LL.moduleGlobals = ll_functions
                     , LL.moduleExports = ll_export_sigs}

