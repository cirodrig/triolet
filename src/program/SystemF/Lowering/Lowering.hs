{-| Generation of low-level code from memory IR.
-}

{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, Rank2Types #-}
module SystemF.Lowering.Lowering 
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
import SystemF.Lowering.Datatypes
import SystemF.Lowering.Marshaling
import SystemF.Lowering.LowerMonad
import qualified SystemF.DictEnv as DictEnv
import SystemF.Syntax
import SystemF.MemoryIR
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
--   Repr dictionary passed as a boxed pointer, record the dictionary
--   in the environment.  Otherwise don't change the environment.
assumeBoundReprDict :: ReturnType -> LL.Var -> Lower a -> Lower a
assumeBoundReprDict (repr ::: ty) bound_var m =
  case repr
  of BoxRT ->
       case fromVarApp ty
       of Just (con, [arg])
            | con `isPyonBuiltin` the_Repr ->
              assumeReprDict arg (LL.VarV bound_var) m
          _ -> m
     _ -> m

assumeVarG :: Var -> ReturnType -> (LL.Var -> GenLower a) -> GenLower a
assumeVarG v return_type k = liftT1 (assumeVar v return_type) k

-- | Create a lowered variable corresponding to the given variable, and
--   add it to the environment so it can be looked up.
--   If it's a Repr dictionary, add that to the environment also.
assumeVar :: Var -> ReturnType -> (LL.Var -> Lower a) -> Lower a
assumeVar v rt k = do
  tenv <- getTypeEnv
  rtype <- liftFreshVarM $ lowerReturnType tenv rt 
  case rtype of
    Just t -> assumeVariableWithType v t $ \ll_var ->
      assumeBoundReprDict rt ll_var (k ll_var)
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

-------------------------------------------------------------------------------
-- Code fragments

-- | A code fragment.
--
--   Most functions that generate code will output everything except the
--   last value or atom they want to generate.  The last bit is returned as
--   a code fragment.  Code fragments can be converted to a value or an atom
--   (the conversion will output more code if necessary).
--   This lets us produce denser code than if everything returned a value.
--
--   Atoms can be side-effecting functions that don't return anything; these
--   can't be converted to values since they don't have a return value.
data Code = ValCode !LL.Val | ExpCode [LL.ValueType] !LL.Atom

valCode :: LL.Val -> Code
valCode = ValCode

atomCode :: [LL.ValueType] -> LL.Atom -> Code
atomCode return_types atom = ExpCode return_types atom

asVal :: Code -> GenLower LL.Val
asVal (ValCode v) = return v
asVal (ExpCode tys atom) = do
  values <- emitAtom tys atom
  case values of
    [val] -> return val
    _ -> internalError "asVal"

asAtom :: Code -> GenLower LL.Atom
asAtom (ValCode v) = return $ LL.ValA [v]
asAtom (ExpCode _ atom) = return atom

-- | Completely output some code, and discard its return value
emitCode :: Code -> GenLower ()
emitCode (ValCode _) = return ()
emitCode (ExpCode tys atom) = emitAtom tys atom >> return () 

-- | Output the code.  Return a new code object containing the code's
-- return value.  This is useful for ensuring that code is generated where 
-- we want it.
generateCode :: Code -> GenLower Code
generateCode code@(ValCode _) = return code
generateCode (ExpCode [ty] atom) = do val <- emitAtom1 ty atom
                                      return (ValCode val)
generateCode (ExpCode tys atom) = do vals <- emitAtom tys atom
                                     return (ExpCode tys (LL.ValA vals))

codeType :: Code -> [LL.ValueType]
codeType (ValCode v) = [LL.valType v]
codeType (ExpCode tys _) = tys

-------------------------------------------------------------------------------
-- Data structure operations: store, load, deconstruct, and construct

-- | Compute the record layout of a boxed object.
--   The record will have one field for the header and one for the object
--   contents.
ownedLayoutRecord :: OwnedLayout -> GenLower LL.DynamicRecord
ownedLayoutRecord (Box layout) = do 
  contents_layout <- pointerLayoutRecordField layout
  createConstDynamicRecord [ LL.RecordField objectHeaderRecord'
                           , contents_layout]

-- | Compute the record type of a 'PointerLayout'
pointerLayoutRecord :: PointerLayout -> GenLower LL.DynamicRecord
pointerLayoutRecord layout =
  case layout
  of ValueReference _ -> internalError "pointerLayoutRecord: Not a record"
     ScalarReference _ -> internalError "pointerLayoutRecord: Not a record"
     IndirectReference _ -> singleton_record
     PolyReference _ -> singleton_record
     ProductReference _ layouts -> do
       fields <- mapM pointerLayoutRecordField layouts
       createMutableDynamicRecord fields
     SOPReference _ -> singleton_record
  where
    singleton_record = do
      -- Treat this as a record with one field
      field <- pointerLayoutRecordField layout
      createMutableDynamicRecord [field]

-- | Compute the field type of a 'PointerLayout' appearing in an object field
pointerLayoutRecordField :: PointerLayout -> GenLower LL.DynamicFieldType
pointerLayoutRecordField layout =
  case layout
  of ValueReference val ->
       return $ toDynamicFieldType $ LL.valueToFieldType $ valueLayoutType val
     ScalarReference val ->
       return $ toDynamicFieldType $ LL.valueToFieldType $ valueLayoutType val
     IndirectReference _ ->
       return $ LL.PrimField LL.PointerType
     PolyReference (PolyRepr ty) -> do
       -- Get the object's size and alignment from a Repr dictionary
       lookupReprDict ty $ \dict -> do
         size <- selectPassConvSize dict
         align <- selectPassConvAlignment dict
         return $ LL.BytesField size align
     ProductReference _ _ -> do
       rc <- pointerLayoutRecord layout
       return $ LL.RecordField rc
     SOPReference disjuncts -> do
       -- Calculate the size and alignment of the record
       (dj_size, dj_align) <- calc_disjuncts_size disjuncts
       
       -- Return an opaque data type
       return $ LL.BytesField dj_size dj_align
  where
    tag_word = LL.PrimField LL.nativeWordType
    
    -- Compute the size and alignment of a SOP type.  It's the maximum
    -- of the values for each disjunct.
    calc_disjuncts_size disjuncts =
      foldM accum_disjunct_size (nativeWordV 0, nativeWordV 1) disjuncts 
    
    accum_disjunct_size (size_acc, align_acc) (_, dj_layouts) = do
      -- Compute the record layout.  Include the tag word.
      fields <- mapM pointerLayoutRecordField dj_layouts
      rc <- createMutableDynamicRecord (tag_word : fields)
      size_acc' <- nativeMaxUZ size_acc (LL.recordSize rc)
      align_acc' <- nativeMaxUZ align_acc (LL.recordAlignment rc)
      return (size_acc', align_acc')

-- | Calculate the layout of a case scrutinee /or/ a data constructor result
--   that has the given type.
calculateScrutineeLayout :: ReturnType -> Lower Layout
calculateScrutineeLayout rt = do
  env <- getTypeEnv
  liftFreshVarM $ typeLayout env rt

-- | A case alternative generator, given the all the field values,
--   will generate the code of the case statement.  The code returns
--   the case statement's return value.
type GenAltBody = [Code] -> GenLower Code

-- | A code generator for a case statement.  
type GenCase = Code -> [(Var, GenAltBody)] -> GenLower Code

compileCase :: ReturnType -> Lower GenCase
compileCase scrutinee_type =
  calculateScrutineeLayout scrutinee_type >>= make_code
  where
    make_code :: Layout -> Lower GenCase
    make_code (ValueLayout value_layout) =
      return $!
      case value_layout
      of ScalarValue con LL.UnitType -> compileUnitValueCase con
         EnumValue ty disjuncts      -> compileEnumValueCase ty disjuncts
         RecordValue con layouts     ->
           case valueLayoutType value_layout
           of LL.RecordType rt -> compileRecordValueCase con rt

    make_code (OwnedLayout owned_layout@(Box pointer_layout)) =
      return $ \scrutinee alts -> do
        scr_val <- asVal scrutinee
        ll_record <- ownedLayoutRecord owned_layout
        let contents_field = ll_record LL.!!: 1
            LL.RecordField contents_record = LL.fieldType contents_field
        contents_ptr <- referenceField contents_field scr_val
        make_pointer_layout_code contents_record pointer_layout contents_ptr alts

    make_code (PointerLayout pointer_layout) =
      return $ \scrutinee alts -> do
        scr_val <- asVal scrutinee
        ll_record <- pointerLayoutRecord pointer_layout
        make_pointer_layout_code ll_record pointer_layout scr_val alts

    make_pointer_layout_code ll_record pointer_layout scrutinee alts =
      case pointer_layout of
        IndirectReference field_layout ->
          compileIndirectReferenceCase field_layout scrutinee alts
        ProductReference con layouts ->
          compileRecordPointerCase con ll_record layouts scrutinee alts
        SOPReference disjuncts ->
          compileRecordSOPCase ll_record disjuncts scrutinee alts
    
compileUnitValueCase con scrutinee [(alt_con, alt_body)]
  | con == alt_con = do
      asVal scrutinee -- Emit scrutinee code.  The result is ignored.
      alt_body []           -- Emit body code.

compileUnitValueCase _ _ _ = internalError "compileUnitValueCase"

-- The scrutinee is a record value.  Unpack its fields.
compileRecordValueCase con record_type scrutinee [(alt_con, alt_body)]
  | con == alt_con = do
      scrutinee_val <- asVal scrutinee
      record_fields <- unpackRecord record_type scrutinee_val
      alt_body $ map (valCode . LL.VarV) record_fields

compileEnumValueCase ty disjuncts scrutinee alternatives = do
  scr_val <- asVal scrutinee

  return_types <- getReturnTypes
  return_vars <- lift $ mapM LL.newAnonymousVar return_types
  getContinuation False return_vars $ \cont -> do
    let (alt_constructors, alt_bodies) = unzip alternatives

    -- Generate code of each alternative branch
    branches <- lift $ forM alt_bodies $ \mk_alt_body -> do
      execBuild return_types $ do
        emitCode =<< mk_alt_body []
        return cont

    -- Build the case statement
    let tags = map tag alt_constructors
    return $ LL.SwitchE scr_val (zip tags branches)

  -- Return the case statement's return values
  return $ atomCode return_types (LL.ValA $ map LL.VarV return_vars)
  where
    -- Find the tag assigned to a constructor 
    tag :: Var -> LL.Lit
    tag = \con -> case lookup con tag_table
                  of Just t -> t
                     Nothing -> internalError "compileCase: Missing tag"
      where
        tag_table = [(con, tag) | ((con, _), tag) <- zip disjuncts tags]
      
        tags 
          | ty == LL.BoolType = [LL.BoolL False, LL.BoolL True]
          | ty == LL.nativeWordType = map nativeWordL [0..]
          | otherwise = internalError "compileCase"

-- | Get a pointer to the contents of a boxed object.  Move past the header
--   and any alignment bytes.
getBoxedObjectContents field_layout scrutinee = do
  padding_size <-
    addRecordPadding header_size (LL.recordAlignment field_layout)
  primAddP scrutinee padding_size
  where
    header_size = nativeIntV $ LL.sizeOf LL.objectHeaderRecord

compileIndirectReferenceCase field_layout scrutinee [(alt_con, alt_body)] = do
  -- The scrutinee is a pointer to the pointer to the object.
  -- Get the pointer to the object.
  tmp_var <- lift $ LL.newAnonymousVar (LL.PrimType LL.PointerType)
  primLoadConst (LL.PrimType LL.PointerType) scrutinee tmp_var
  alt_body [valCode (LL.VarV tmp_var)]

compileRecordPointerCase con record_type layouts scrutinee [(alt_con, alt_body)] 
  | alt_con == con = do
      field_values <-
        zipWithM (loadCaseField scrutinee) (LL.recordFields record_type) layouts
      alt_body (map valCode field_values)

compileRecordSOPCase = internalError "compileRecordSOPCase: Not implemented"

loadCaseField :: LL.Val         -- ^ Pointer to scrutinee
              -> LL.DynamicField 
              -> PointerLayout
              -> GenLower LL.Val
loadCaseField scr_ptr field field_layout =
  case field_layout
  of ValueReference value_layout -> loadField field scr_ptr
     ScalarReference _ -> get_field_reference
     IndirectReference _ -> get_field_reference
     PolyReference (PolyRepr _) -> get_field_reference
     ProductReference _ _ -> get_field_reference
     SOPReference _ -> get_field_reference
  where
    get_field_reference = referenceField field scr_ptr

compileStore :: Type -> ExpTM -> ExpTM -> GenLower Code
compileStore store_type value address = do
  -- Determine layout of this value
  tenv <- lift getTypeEnv
  value_type <- lift $ liftFreshVarM $ lowerValueType tenv store_type

  -- Generate the value and store it
  arg_val <- asVal =<< lowerExp value
  dst_val <- asVal =<< lowerExp address
  let primop = LL.PrimStore LL.Mutable value_type
      atom = LL.PrimA primop [dst_val, nativeIntV 0, arg_val]
  return $ atomCode [] atom

compileLoad :: Type -> ExpTM -> GenLower Code
compileLoad load_type address = do
  -- Determine layout of this value
  tenv <- lift getTypeEnv
  value_type <- lift $ liftFreshVarM $ lowerValueType tenv load_type

  -- Load it
  src_val <- asVal =<< lowerExp address
  let primop = LL.PrimLoad LL.Mutable value_type
  let atom = LL.PrimA primop [src_val, nativeIntV 0]
  return $ atomCode [value_type] atom

-- | Compile a data constructor.  If the data constructor takes no   
--   arguments, the constructor value is returned; otherwise a function 
--   is returned.  All type arguments must be provided.
compileConstructor :: Var -> DataConType -> [Type] -> GenLower Code
compileConstructor con con_type ty_args = do
  (_, field_types, result_type) <-
    lift $ liftFreshVarM $
    instantiateDataConTypeWithFreshVariables con_type ty_args
  lift (calculateScrutineeLayout result_type) >>= make_code field_types
  where
  
    make_code :: [ReturnType] -> Layout -> GenLower Code
    make_code field_types (ValueLayout value_layout) =
      case value_layout
      of ScalarValue con LL.UnitType ->
           return $ valCode (LL.LitV LL.UnitL)
         EnumValue ty disjuncts ->
           compileEnumValueCtor con ty disjuncts
         RecordValue con layouts ->
           case valueLayoutType value_layout
           of LL.RecordType rt -> compileRecordValueCtor con rt field_types

    make_code field_types (OwnedLayout owned_layout@(Box pointer_layout)) = do
      -- Compute layout of this object
      ll_record <- ownedLayoutRecord owned_layout
      let contents_field = ll_record LL.!!: 1
          LL.RecordField contents_record = LL.fieldType contents_field

      -- Make the constructor function
      ctor_fun <-
        asVal =<< make_pointer_layout_code field_types contents_record pointer_layout
      
      -- Create a new object, using that constructor function to write its
      -- contents
      compileBoxCtor field_types ll_record pointer_layout ctor_fun

    make_code field_types (PointerLayout pointer_layout) = do
      ll_record <- pointerLayoutRecord pointer_layout
      make_pointer_layout_code field_types ll_record pointer_layout
    
    make_pointer_layout_code field_types ll_record pointer_layout =
      case pointer_layout of
        IndirectReference layouts ->
          compileIndirectCtor field_types layouts
        ProductReference con layouts ->
          compileRecordPointerCtor con ll_record field_types layouts
        SOPReference disjuncts ->
          compileRecordSOPCtor ll_record disjuncts

compileEnumValueCtor con ty disjuncts =
  case lookup con disjuncts
  of Just literal_value -> return $ valCode (LL.LitV literal_value)
     Nothing -> internalError "compileEnumValueCtor: No tag for constructor"

compileRecordValueCtor con rt field_types = lift $ do
  when (null field_types) $ internalError "compileRecordValueCtor"
  tenv <- getTypeEnv
  let record_fields = LL.recordFields rt
  
  -- Create a parameter for each field
  ll_param_types <-
    liftFreshVarM $ sequence [lowerValueType tenv ty | _ ::: ty <- field_types]
  params <- mapM LL.newAnonymousVar ll_param_types
  
  -- Build a record out of the parameers
  let record_expr = LL.ReturnE $ LL.PackA rt (map LL.VarV params)
      record_fun = LL.closureFun params [LL.RecordType rt] record_expr
  return $ valCode $ LL.LamV record_fun

compileBoxCtor field_types ll_record pointer_layout ctor_fun = lift $ do
  -- Create a boxed object and use 'ctor_fun' to initialize it.
  tenv <- getTypeEnv

  -- Create a parameter for each field
  let ll_param_types = map (constructorParameterType tenv) field_layouts
  params <- mapM LL.newAnonymousVar ll_param_types
  
  -- Create the function body.  The function returns an owned pointer.
  fun_body <- execBuild [LL.PrimType LL.OwnedType] $ do
    obj <- allocateHeapMem (LL.recordSize ll_record)
    -- FIXME: initialize object header
    obj_owned_ptr <- emitAtom1 (LL.PrimType LL.OwnedType) $
                     LL.PrimA LL.PrimCastToOwned [obj]

    contents_ptr <- referenceField (ll_record LL.!!: 1) obj_owned_ptr
    
    -- Use the constructor function to initialize the object's contents
    emitAtom0 $ LL.closureCallA ctor_fun (map LL.VarV params ++ [contents_ptr])
    return $ LL.ReturnE $ LL.ValA [obj_owned_ptr]
  
  let box_fun = LL.closureFun params [LL.PrimType LL.OwnedType] fun_body
  return $ valCode $ LL.LamV box_fun
  where
    -- Determine what parameters are expected by the constructor function
    field_layouts =
      case pointer_layout of
        IndirectReference layout -> [layout]
        ProductReference con layouts -> layouts
        SOPReference disjuncts ->
          internalError "SOPReference is not implemented"


compileIndirectCtor [field_type] field_layout = lift $ do
  -- Create a referenced object
  -- Create a parameter for the field.  The parameter is a function.
  param <- LL.newAnonymousVar (LL.PrimType LL.OwnedType)

  -- Take a pointer to the output address
  ret_param <- LL.newAnonymousVar (LL.PrimType LL.PointerType)
  let ret_ptr = LL.VarV ret_param

  function_body <- execBuild [] $ do
    -- Allocate memory for this object
    obj_record <- pointerLayoutRecord field_layout
    heap_ptr <- allocateHeapMem $ LL.recordSize obj_record

    -- Write the object
    emitAtom0 $ LL.closureCallA (LL.VarV param) [heap_ptr]
    
    -- Store the object pointer into the destination
    primStoreConst (LL.PrimType LL.PointerType) ret_ptr heap_ptr
    return $ LL.ReturnE $ LL.ValA []
  
  let function = LL.closureFun [param, ret_param] [] function_body
  return $ valCode (LL.LamV function)

compileRecordPointerCtor con record field_types field_layouts = lift $ do
  when (null field_types) $ internalError "compileRecordValueCtor"
  tenv <- getTypeEnv
  let record_fields = LL.recordFields record
  
  -- Create a parameter for each field
  let ll_param_types = map (constructorParameterType tenv) field_layouts
  params <- mapM LL.newAnonymousVar ll_param_types
  
  -- Create a parameter for the return value
  ret_param <- LL.newAnonymousVar (LL.PrimType LL.PointerType)
  let ret_ptr = LL.VarV ret_param
  
  function_body <- execBuild [] $ do
    -- Store each parameter
    mapM_ (store_param tenv ret_ptr) $
      zip4 params record_fields field_types field_layouts
    return $ LL.ReturnE $ LL.ValA []
  
  let function = LL.closureFun (params ++ [ret_param]) [] function_body
  return $ valCode (LL.LamV function)
  where
    -- Emit the code to store one parameter
    store_param :: TypeEnv -> LL.Val
                -> (LL.Var, LL.DynamicField, ReturnType, PointerLayout)
                -> GenLower ()
    store_param tenv ret_ptr (param, record_field, field_type, field_layout) =
      case field_layout
      of ValueReference val_layout -> do
           -- Store the value into the field
           let value_type = valueLayoutType val_layout
           storeField record_field ret_ptr (LL.VarV param)

         _ -> do
           -- Field is pass-by-reference.  The parameter is a function that
           -- will store into the field.
           dst_addr <- referenceField record_field ret_ptr
           emitAtom0 $ LL.closureCallA (LL.VarV param) [dst_addr]
      
-- Decide how to pass a parameter to a constructor function
constructorParameterType tenv field_layout =
  case field_layout
  of ValueReference val_layout -> valueLayoutType val_layout
     ScalarReference _ -> LL.PrimType LL.OwnedType
     IndirectReference _ -> LL.PrimType LL.OwnedType
     PolyReference _ -> LL.PrimType LL.OwnedType
     ProductReference _ _ -> LL.PrimType LL.OwnedType
     SOPReference _ -> LL.PrimType LL.OwnedType

compileRecordSOPCtor = internalError "compileRecordSOPCtor: Not implemented"

-------------------------------------------------------------------------------
-- Lowering for things other than case expressions

bindPatterns pats m = foldr (uncurry bindPattern) m pats

-- | Bind a pattern-bound variable to the result of some code
bindPattern :: PatM -> Code -> GenLower a -> GenLower a
bindPattern (MemVarP v (repr ::: ty)) value m = do
  assumeVarG v (paramReprToReturnRepr repr ::: ty) $ \ll_var -> do
    bindAtom1 ll_var =<< asAtom value
    m

-- | Lower a type that is passed as an argument to an expression.
--   In most cases, the type becomes a unit value.
lowerTypeValue :: TypTM -> GenLower Code
lowerTypeValue _ = return $ valCode (LL.LitV LL.UnitL)

lowerExp :: ExpTM -> GenLower Code
lowerExp (ExpTM (RTypeAnn return_type expression)) =
  case expression
  of VarE _ v -> lowerVar return_type v
     LitE _ l -> lowerLit return_type l
     
     -- Special-case handling of load and store functions
     AppE _ (ExpTM (RTypeAnn _ (VarE _ op))) ty_args args 
       | op `isPyonBuiltin` the_store ->
           case (ty_args, args)
           of ([TypTM (RTypeAnn _ store_type)], [_, value, address]) ->
                compileStore store_type value address
              _ -> internalError "lowerExp: Wrong number of arguments to store"
       | op `isPyonBuiltin` the_load ->
           case (ty_args, args)
           of ([TypTM (RTypeAnn _ load_type)], [_, address]) ->
                compileLoad load_type address
              _ -> internalError "loadExp: Wrong number of arguments to load"
     AppE _ op ty_args args -> lowerApp return_type op ty_args args
     LamE _ f -> lift $ lowerLam return_type f
     LetE _ binder rhs body -> lowerLet return_type binder rhs body
     LetrecE _ defs body -> lowerLetrec return_type defs body
     CaseE _ scr alts -> lowerCase return_type scr alts

lowerVar _ v =
  case LL.lowerIntrinsicOp v
  of Just lower_var -> lift $ fmap valCode lower_var
     Nothing -> do
       tenv <- lift getTypeEnv
       case lookupDataCon v tenv of
         Just data_con ->
           -- If the constructor takes type arguments, it should be
           -- processed by lowerApp.
           compileConstructor v data_con []
         Nothing -> lift $ do ll_v <- lookupVar v
                              return $ valCode (LL.VarV ll_v)

lowerLit _ lit =
  case lit
  of IntL n ty ->
       case fromVarApp ty
       of Just (con, [])
            | con `isPyonBuiltin` the_int ->
              return $ valCode (LL.LitV $ LL.IntL LL.Signed LL.pyonIntSize n)
     FloatL n ty ->
       case fromVarApp ty
       of Just (con, [])
            | con `isPyonBuiltin` the_float ->
              return $ valCode (LL.LitV $ LL.FloatL LL.pyonFloatSize n)

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
      op' <- asVal =<< compileConstructor op_var op_data_con argument_types
      args' <- mapM (asVal <=< lowerExp) args
      returns <- lift $ liftFreshVarM $ lowerFunctionReturn tenv rt
      return $ atomCode returns (LL.closureCallA op' args')

    lower_function tenv = do
      op' <- asVal =<< lowerExp op
      ty_args' <- mapM (asVal <=< lowerTypeValue) ty_args
      args' <- mapM (asVal <=< lowerExp) args
      returns <- lift $ liftFreshVarM $ lowerFunctionReturn tenv rt
      return $ atomCode returns (LL.closureCallA op' (ty_args' ++ args'))

lowerLam _ f = do
  f' <- lowerFun f
  return $ valCode (LL.LamV f')

lowerLet _ binder rhs body =
  case binder
  of TypedMemVarP {} -> do
       rhs_code <- lowerExp rhs
       bindPattern (fromPatTM binder) rhs_code $ lowerExp body

     TypedLocalVarP v ty repr_dict -> do
       -- Get the size of the local variable's data
       dict_val <- asVal =<< lowerExp repr_dict
       local_size <- selectPassConvSize dict_val
       
       -- Allocate local memory, then generate the rhs and body code
       assumeLocalVar v local_size $ \ll_var -> do
         emitAtom0 =<< asAtom =<< lowerExp rhs
         
         -- If it's a dictionary variable, add it to the environment while
         -- generating code of the body.
         -- Force all body code to be generated here.
         liftT (assumeBoundReprDict (ReadRT ::: ty) ll_var) $
           generateCode =<< lowerExp body

lowerLetrec _ defs body =
  lowerDefGroupG defs $ \defs' -> do
    emitLetrec defs'
    lowerExp body

lowerCase _ scr alts = do
  let ExpTM (RTypeAnn scrutinee_type _) = scr
  case_generator <- lift $ compileCase scrutinee_type

  scr_code <- lowerExp scr
  case_generator scr_code (map lowerAlt alts)

lowerAlt (AltTM (RTypeAnn return_type alt)) =
  (altConstructor alt, lowerAltBody return_type alt)

lowerAltBody return_type alt field_values =
  -- Type arguments are ignored
  -- Bind the field values and generate the body
  let params = map fromPatTM $ altParams alt
  in bindPatterns (zip params field_values) $ lowerExp $ altBody alt

lowerFun :: FunTM -> Lower LL.Fun
lowerFun (FunTM (RTypeAnn _ fun)) =
  withMany lower_type_param (funTyParams fun) $ \ty_params ->
  withMany lower_param (funParams fun) $ \params -> do
    tenv <- getTypeEnv
    returns <- liftFreshVarM $
               lowerFunctionReturn tenv $ fromRetTM $ funReturn fun
    genClosureFun (ty_params ++ params) returns $ lower_body (funBody fun)
  where
    -- Types are passed, but not used.  Lower them to the unit value.
    lower_type_param (TyPatTM a kind) k = do
      param_var <- LL.newAnonymousVar (LL.PrimType LL.UnitType)
      assumeType a (fromTypTM kind) $ k param_var 
      
    lower_param (TypedMemVarP v (param_repr ::: ty)) k =
      assumeVar v (paramReprToReturnRepr param_repr ::: ty) k

    lower_param (TypedLocalVarP {}) _ =
      internalError "lowerFun: Unexpected local variable"
    
    lower_body body = do
      atom <- asAtom =<< lowerExp body
      return (LL.ReturnE atom)

-- | Lower a function definition.  The function variable must already have
--   been translated.
lowerDef :: Def (Typed Mem) -> Lower LL.FunDef
lowerDef (Def v f) = do
  v' <- lookupVar v
  f' <- lowerFun f
  return (LL.Def v' f')

lowerDefGroup :: [Def (Typed Mem)] -> ([LL.FunDef] -> Lower a) -> Lower a
lowerDefGroup defs k = assume_variables $ k =<< mapM lowerDef defs
  where
    assume_variables m =
      foldr assume_variable m [(v, rt) | Def v (FunTM (RTypeAnn rt _)) <- defs]

    assume_variable (v, return_type) m = assumeVar v return_type $ \_ -> m

lowerDefGroupG :: [Def (Typed Mem)] -> ([LL.FunDef] -> GenLower a) -> GenLower a
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
                -> [[Def (Typed Mem)]] 
                -> [Export (Typed Mem)]
                -> Lower ([[LL.FunDef]], [(LL.Var, ExportSig)])
lowerModuleCode module_name defss exports = lower_definitions defss
  where
    lower_definitions (defs:defss) =
      lowerDefGroup defs $ \defs' -> do
        (defss', export_sigs) <- lowerModuleCode module_name defss exports
        return (defs' : defss', export_sigs)

    lower_definitions [] = do
      ll_exports <- mapM (lowerExport module_name) exports
      let (functions, signatures) = unzip ll_exports
      return ([functions], signatures)

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
                     , LL.moduleGlobals = map LL.GlobalFunDef $
                                          concat ll_functions
                     , LL.moduleExports = ll_export_sigs}

