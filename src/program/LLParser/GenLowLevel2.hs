{-| Turn the parser data structures into low-level code.
-}

{-# LANGUAGE ViewPatterns #-}
module LLParser.GenLowLevel2 where

import Control.Monad
import Control.Monad.Trans
import Data.Either
import qualified Data.IntMap as IntMap
import Data.List

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.Supply
import LLParser.AST
import LLParser.TypeInference
import LowLevel.Build
import LowLevel.Builtins
import LowLevel.FreshVar
import LowLevel.Types
import LowLevel.Record hiding(Field)
import qualified LowLevel.Syntax as LL
import Globals

data GenExpr = GenVal LL.Val
             | GenAtom [LL.ValueType] LL.Atom

asVal :: GenExpr -> G LL.Val
asVal (GenVal v) = return v
asVal (GenAtom [vtype] atom) = emitAtom1 vtype atom
asVal (GenAtom _ _) =
  internalError "asVal: Expression does not have one return value"

asAtom :: GenExpr -> G LL.Atom
asAtom (GenVal v) = return (LL.ValA [v])
asAtom (GenAtom _ atom) = return atom

returnType :: GenExpr -> [LL.ValueType]
returnType (GenVal val)  = [LL.valType val]
returnType (GenAtom t _) = t

data DynamicType =
  DynamicType
  { dynamicTypeSize :: LL.Val
  , dynamicTypeAlign :: LL.Val
  , dynamicTypeRecord :: Maybe DynamicRecord
  }

-- | Environment holding type synonyms
type TypeEnv = IntMap.IntMap DynamicType

emptyTypeEnv = IntMap.empty

insertTypeSynonym syn_id record m = IntMap.insert (fromIdent syn_id) record m

lookupTypeSynonym syn_id m =
  case IntMap.lookup (fromIdent syn_id) m
  of Just t -> t
     Nothing -> internalError "lookupTypeSynonym"

-------------------------------------------------------------------------------

type G a = Gen FreshVarM a

-- | Generate code for a type whose size and alignemnt are dynamically
--   computed
convertToDynamicFieldType :: TypeEnv -> Type Typed -> G DynamicFieldType
convertToDynamicFieldType tenv ty = 
  case ty
  of PrimT pt -> return $ PrimField pt
     RecordT (TypeSynonym type_id _) ->
       let ty' = lookupTypeSynonym type_id tenv
       in case dynamicTypeRecord ty'
          of Just dyn_record ->
               return $ RecordField dyn_record
             Nothing ->
               return $ BytesField (dynamicTypeSize ty') (dynamicTypeAlign ty')
     RecordT record -> do
       dyn_record <- convertToDynamicRecord tenv record
       return $ RecordField dyn_record
     BytesT size align -> do
       size_val <- asVal =<< genExpr tenv size
       align_val <- asVal =<< genExpr tenv align
       return $ BytesField size_val align_val
     AppT ty args ->
       -- Apply, then convert
       convertToDynamicFieldType tenv $ applyRecordType ty args

convertToDynamicRecord :: TypeEnv -> TypedRecord -> G DynamicRecord
convertToDynamicRecord tenv rec = 
  case rec
  of TypeSynonym type_id _ ->
       case dynamicTypeRecord $ lookupTypeSynonym type_id tenv
       of Just record -> return record
          Nothing     -> error "Expecting a record type"
     _ -> do
       field_types <- sequence [convertToDynamicFieldType tenv t
                               | FieldDef t _ <- typedRecordFields0 rec]
       createDynamicRecord field_types

genDynamicType :: TypeEnv -> Type Typed -> G DynamicType
genDynamicType tenv ty =
  case ty
  of PrimT pt ->
       let size = nativeWordV $ sizeOf pt
           align = nativeWordV $ alignOf pt
       in return $ DynamicType size align Nothing
     RecordT (TypeSynonym type_id _) -> do
       return $ lookupTypeSynonym type_id tenv
     RecordT rec -> do
       dynamic_rec <- convertToDynamicRecord tenv rec
       return $ DynamicType (recordSize dynamic_rec) (recordAlignment dynamic_rec) (Just dynamic_rec)
     BytesT size align -> do
       size_val <- asVal =<< genExpr tenv size
       align_val <- asVal =<< genExpr tenv size
       return $ DynamicType size_val align_val Nothing
     AppT ty args ->
       genDynamicType tenv $ applyRecordType ty args

-- | Generate code of an expression used to initialize global data.
genDataExpr :: Expr Typed -> FreshVarM LL.Val
genDataExpr expr =
  case expExp expr
  of VarE v -> return $ LL.VarV v
     IntLitE ty n
       | PrimT (IntType sgn sz) <- ty ->
           return $ LL.LitV (LL.IntL sgn sz n)
       | otherwise ->
           internalError "genExpr: Integer literal has non-integer type"
     FloatLitE ty n
       | PrimT (FloatType sz) <- ty ->
           return $ LL.LitV (LL.FloatL sz n)
       | otherwise ->
           internalError "genExpr: Float literal has non-floating type"
     BoolLitE b ->
       return $ LL.LitV (LL.BoolL b)
     NilLitE ->
       return $ LL.LitV LL.UnitL
     NullLitE ->
       return $ LL.LitV LL.NullL
     RecordE rec fields -> do
       let record = convertToStaticRecord rec
       fields' <- mapM genDataExpr fields
       return $ LL.RecV record fields'
     SizeofE ty ->
       let ty' = convertToValueType ty
           lit = mkIntLit (LL.PrimType nativeWordType) (fromIntegral $ sizeOf ty')
       in return $ LL.LitV lit
     AlignofE ty ->
       let ty' = convertToValueType ty
           lit = mkIntLit (LL.PrimType nativeWordType) (fromIntegral $ alignOf ty')
       in return $ LL.LitV lit

mkIntLit :: LL.ValueType -> Integer -> LL.Lit
mkIntLit ty n =
  case ty
  of LL.PrimType (IntType sgn sz) -> LL.IntL sgn sz n
     _ -> error "Invalid integer type"

mkFloatLit :: LL.ValueType -> Double -> LL.Lit
mkFloatLit ty n =
  case ty
  of LL.PrimType (FloatType sz) -> LL.FloatL sz n
     _ -> error "Invalid floating-point type"

mkWordVal :: Expr Typed -> LL.Val
mkWordVal expr =
  case expExp expr
  of IntLitE _ n -> nativeWordV n
     VarE v -> LL.VarV v

-- | Generate code to load or store a record field.  Return the field offset
--   and the type at which the field should be accessed.
genField :: TypeEnv -> Field Typed -> G (LL.Val, LL.ValueType)
genField tenv (Field base_type fnames cast_type) =
  get_field_offset (nativeWordV 0) base_type fnames
  where
    get_field_offset base_offset base_type (fname:fnames) =
      case base_type
      of RecordT (TypeSynonym type_id typed_type) ->
           case dynamicTypeRecord $ lookupTypeSynonym type_id tenv
           of Just dyn_rec -> 
                case typed_type
                of RecordT static_rec ->
                     get_dynamic_type_offset dyn_rec static_rec
              Nothing -> internalError "genField: Base type is not a record"
         RecordT rec -> do
           dyn_rec <- convertToDynamicRecord tenv rec
           get_dynamic_type_offset dyn_rec rec
         _ -> internalError "genField: Base type is not a record"
      where
        get_dynamic_type_offset dyn_rec rec =
          case findIndex (match_name fname) $ typedRecordFields0 rec
          of Just ix -> do
               let rfield = typedRecordFields0 rec !! ix
                   dfield = dyn_rec !!: ix
               offset <- primAddZ (LL.PrimType nativeWordType) base_offset (fieldOffset dfield)
               case fnames of
                 [] -> return_field_offset offset dfield
                 _  -> case rfield
                       of FieldDef next_rec _ ->
                            get_field_offset offset next_rec fnames
                          _ -> internalError "genField"
             Nothing ->
               internalError "genField"

    return_field_offset offset field =
      let ty = case cast_type
               of Just t -> convertToValueType t
                  Nothing -> case fieldType field
                             of PrimField pt -> LL.PrimType pt
                                RecordField r -> 
                                  LL.RecordType $ dynamicToStaticRecordType r
                                _ -> internalError "genField"
      in return (offset, ty)

    match_name want_name (FieldDef _ name) = name == want_name

-- | Convert to a static record type.  The type must not contain non-constant
--   expressions.  Throw an error if it doesn't satisfy these conditions.
dynamicToStaticRecordType :: DynamicRecord -> StaticRecord
dynamicToStaticRecordType = internalError "dynamicToStaticRecordType: not implemented"

-- | Generate code of an expression
genExpr :: TypeEnv -> Expr Typed -> G GenExpr
genExpr tenv expr =
  case expExp expr
  of VarE {} -> data_expr
     IntLitE {} -> data_expr
     FloatLitE {} -> data_expr
     BoolLitE {} -> data_expr
     NilLitE {} -> data_expr
     NullLitE {} -> data_expr
     RecordE record fs -> do
       fs' <- mapM (asVal <=< subexpr) fs
       let record_type = convertToStaticRecord record
           atom = LL.PackA record_type fs'
       return $ GenAtom [LL.RecordType record_type] atom
     FieldE base fld -> do
       addr <- asVal =<< subexpr base
       (offset, _) <- genField tenv fld
       let atom = LL.PrimA LL.PrimAddP [addr, offset]
       return $ GenAtom [LL.PrimType PointerType] atom
     LoadFieldE base fld -> do
       addr <- asVal =<< subexpr base
       (offset, ty) <- genField tenv fld
       let atom = LL.PrimA (LL.PrimLoad ty) [addr, offset]
       return $ GenAtom [ty] atom
     LoadE ty base -> do
       addr <- asVal =<< subexpr base
       let llty = convertToValueType ty
       let atom = LL.PrimA (LL.PrimLoad llty) [addr, nativeIntV 0]
       return $ GenAtom [llty] atom
     CallE returns op args -> do
       op' <- asVal =<< subexpr op
       args' <- mapM (asVal <=< subexpr) args
       let atom = LL.CallA op' args'
           return_types = map convertToValueType returns
       return $ GenAtom return_types atom
     PrimCallE returns op args -> do
       op' <- asVal =<< subexpr op
       args' <- mapM (asVal <=< subexpr) args
       let atom = LL.PrimCallA op' args'
           return_types = map convertToValueType returns
       return $ GenAtom return_types atom
     UnaryE op arg -> do
       arg' <- subexpr arg
       genUnaryOp op arg'
     BinaryE op l r -> do
       l' <- subexpr l
       r' <- subexpr r
       genBinaryOp op l' r'
     CastE e ty -> do
       e' <- subexpr e
       genCast (convertToValueType ty) e'
     SizeofE ty -> do
       let size =
             case ty
             of BytesT size _ -> mkWordVal size
                RecordT (TypeSynonym tid _) ->
                  dynamicTypeSize $ lookupTypeSynonym tid tenv
                _ -> nativeWordV $ sizeOf $ convertToValueType ty
       return $ GenVal size
     AlignofE ty -> do
       let align =
             case ty
             of BytesT _ align -> mkWordVal align
                RecordT (TypeSynonym tid _) ->
                  dynamicTypeAlign $ lookupTypeSynonym tid tenv
                _ -> nativeWordV $ alignOf $ convertToValueType ty
       return $ GenVal align
  where
    subexpr e = genExpr tenv e
    data_expr = lift $ fmap GenVal $ genDataExpr expr

genUnaryOp :: UnaryOp -> GenExpr -> G GenExpr
genUnaryOp op arg = 
  case op
  of NegateOp ->
       -- Create the expression [| 0 - arg |]
       case returnType arg
       of rt@[LL.PrimType (IntType sgn sz)] -> do
            arg_val <- asVal arg
            let operand = LL.LitV $ LL.IntL sgn sz 0
                op = LL.PrimSubZ sgn sz
                atom = LL.PrimA op [operand, arg_val]
            return $ GenAtom rt atom

genBinaryOp :: BinOp -> GenExpr -> GenExpr -> G GenExpr
genBinaryOp op l_arg r_arg = 
  case op
  of CmpEQOp -> comparison LL.CmpEQ
     CmpNEOp -> comparison LL.CmpNE
     CmpLTOp -> comparison LL.CmpLT
     CmpLEOp -> comparison LL.CmpLE
     CmpGTOp -> comparison LL.CmpGT
     CmpGEOp -> comparison LL.CmpGE
     AtomicAddOp -> atomic_int LL.PrimAAddZ
     PointerAddOp -> pointer_add
     AddOp -> arithmetic LL.PrimAddZ LL.PrimAddF
     SubOp -> arithmetic LL.PrimSubZ LL.PrimSubF
     MulOp -> arithmetic LL.PrimMulZ LL.PrimMulF
     ModOp -> arithmetic LL.PrimModZ LL.PrimModF
     _ -> internalError "mkBinary: Unhandled binary operator"
  where
    comparison cmp_op = do
      let operator =
            case returnType l_arg
            of [LL.PrimType (IntType sgn sz)] -> LL.PrimCmpZ sgn sz cmp_op
               [LL.PrimType PointerType] -> LL.PrimCmpP cmp_op
               _ -> internalError "Binary comparison not implemented for this type"
      l_val <- asVal l_arg
      r_val <- asVal r_arg
      let atom = LL.PrimA operator [l_val, r_val]
      return $ GenAtom [LL.PrimType BoolType] atom
    
    atomic_int atomic_op = do
      let operator =
            case returnType r_arg
            of [LL.PrimType (IntType sgn sz)] -> atomic_op sgn sz
      l_val <- asVal l_arg
      r_val <- asVal r_arg
      let atom = LL.PrimA operator [l_val, r_val]
      return $ GenAtom (returnType r_arg) atom

    pointer_add = do
      l_val <- asVal l_arg
      r_val <- asVal r_arg
      let atom = LL.PrimA LL.PrimAddP [l_val, r_val]
      return $ GenAtom [LL.PrimType PointerType] atom
    
    arithmetic int_op float_op = do
      l_val <- asVal l_arg
      r_val <- asVal r_arg
      let atom =
            case returnType l_arg
            of [LL.PrimType (IntType sgn sz)] ->
                 LL.PrimA (int_op sgn sz) [l_val, r_val]
               [LL.PrimType (FloatType sz)] ->
                 LL.PrimA (float_op sz) [l_val, r_val]
               _ -> internalError "Arithmetic operator not implemented for this type"
      return $ GenAtom (returnType l_arg) atom
    
genCast :: LL.ValueType -> GenExpr -> G GenExpr
genCast ty e =
  case (expected_type, given_type)
  of (OwnedType, OwnedType) -> success_id
     (OwnedType, PointerType) -> do
       val <- asVal e
       success $ LL.PrimA LL.PrimCastToOwned [val]
     (PointerType, OwnedType) -> do
       val <- asVal e
       success $ LL.PrimA LL.PrimCastFromOwned [val]
     (PointerType, PointerType) -> success_id
     (IntType e_sgn e_sz, IntType g_sgn g_sz)
       | e_sz == g_sz && e_sgn == g_sgn -> success_id
       | e_sz == g_sz -> do
         val <- asVal e
         success $ LL.PrimA (LL.PrimCastZ g_sgn e_sgn g_sz) [val]
     _ -> cannot
  where
    given_type =
      case returnType e
      of [LL.PrimType t] -> t
         _ -> internalError "genCast: Cannot cast from type"
    
    expected_type =
      case ty
      of LL.PrimType t -> t
         _ -> internalError "genCast: Cannot cast to type"

    success_id = return e
   
    success atom = return $ GenAtom [ty] atom
    
    cannot = internalError "genCast: Unexpected type cast"

genAtom :: TypeEnv -> Atom Typed -> G LL.Atom
-- If there's only one expression, make an atom
genAtom tenv (ValA [expr]) = asAtom =<< genExpr tenv expr

genAtom tenv (ValA exprs)
  | all ((1 ==) . length . exprType) exprs = do
      -- If there are many single-valued expressions,
      -- bind each to one value
      values <- mapM (asVal <=< genExpr tenv) exprs 
      return (LL.ValA values)
  | otherwise = do
      -- Create values for each expression, then
      -- concatenate them into an atom
      values <- forM exprs $ \expr -> do
        expr' <- genExpr tenv expr
        emitAtom (returnType expr') =<< asAtom expr'
      return (LL.ValA $ concat values)

-- | Generate code of a statement
genStmt :: TypeEnv -> Stmt Typed -> G LL.Stm
genStmt tenv stmt =
  case stmt
  of LetS lvals atom body -> do
       genLetAssignment tenv lvals atom
       genStmt tenv body
     LetrecS fdefs body -> do
       emitLetrec =<< lift (mapM (genFunctionDef tenv) fdefs)
       genStmt tenv body
     TypedefS (TypeSynonym type_id _) ty stmt -> do
       -- Compute specification of this type
       ty' <- genDynamicType tenv ty
       genStmt (insertTypeSynonym type_id ty' tenv) stmt
     IfS cond if_true if_false Nothing ->
       genTailIf tenv cond if_true if_false
     IfS cond if_true if_false (Just (lhs, continuation)) ->
       genMedialIf tenv cond if_true if_false lhs (genStmt tenv continuation)
     WhileS inits cond body Nothing ->
       genTailWhile tenv inits cond body
     WhileS inits cond body (Just (lhs, continuation)) -> 
       genMedialWhile tenv inits cond body lhs (genStmt tenv continuation)
     ReturnS atom -> do
       atom' <- genAtom tenv atom
       return (LL.ReturnE atom')

genStmtAtom :: TypeEnv -> Stmt Typed -> G LL.Atom
genStmtAtom tenv stmt =
  case stmt
  of LetS lvals atom body -> do
       genLetAssignment tenv lvals atom
       genStmtAtom tenv body
     LetrecS fdefs body -> do
       emitLetrec =<< lift (mapM (genFunctionDef tenv) fdefs)
       genStmtAtom tenv body
     IfS cond if_true if_false Nothing -> do
       -- Generate an if statement, then group its result values into an atom
       let return_types = map convertToValueType $ stmtType if_true
       return_vars <- lift $ mapM LL.newAnonymousVar return_types

       let lvals = map VarL return_vars
           return_atom = LL.ValA $ map LL.VarV return_vars
       genMedialIf tenv cond if_true if_false lvals (return return_atom)
     IfS cond if_true if_false (Just (lhs, continuation)) ->
       genMedialIf tenv cond if_true if_false lhs (genStmtAtom tenv continuation)

     WhileS inits cond body Nothing -> do
       -- Generate a while statement, then group its result values into an atom
       let return_types =
             map convertToValueType [t | (Parameter t _, _) <- inits]
       return_vars <- lift $ mapM LL.newAnonymousVar return_types
       
       let lvals = map VarL return_vars
           return_atom = LL.ValA $ map LL.VarV return_vars
       genMedialWhile tenv inits cond body lvals (return return_atom)

     WhileS inits cond body (Just (lhs, continuation)) ->
       genMedialWhile tenv inits cond body lhs (genStmtAtom tenv continuation)

     ReturnS atom -> do
       genAtom tenv atom

-- | Create code of an assignment 
genLetAssignment :: TypeEnv -> [LValue Typed] -> Atom Typed -> G ()
genLetAssignment tenv lvals atom = do
  rhs <- genAtom tenv atom
  genLValues tenv lvals rhs (map convertToValueType $ atomType atom)

-- | Generate a while expression in tail poisition
genTailWhile :: TypeEnv -> [(Parameter Typed, Expr Typed)] -> Expr Typed
             -> Stmt Typed
             -> G LL.Stm
genTailWhile tenv inits cond body = do
  while_var <- lift $ LL.newAnonymousVar (LL.PrimType PointerType)
  
  -- When done, return the loop-carried variables
  let cont = return $ LL.ReturnE $ LL.ValA [LL.VarV v | (Parameter _ v, _) <- inits]
  genWhileFunction tenv while_var inits cond body cont
  initializers <- mapM (asVal <=< genExpr tenv) (map snd inits)
  return $ LL.ReturnE $ LL.PrimCallA (LL.VarV while_var) initializers

genMedialWhile :: TypeEnv -> [(Parameter Typed, Expr Typed)] -> Expr Typed
               -> Stmt Typed -> [LValue Typed] -> G a -> G a
genMedialWhile tenv inits cond body lhs mk_cont = do
  let param_vars = [v | (Parameter _ v, _) <- inits]
      param_types = map LL.varType param_vars
  while_var <- lift $ LL.newAnonymousVar (LL.PrimType PointerType)
  
  -- Turn the continuation into a function so we can call it.
  getContinuation True param_vars $ \cont -> do
    -- Generate the while function
    genWhileFunction tenv while_var inits cond body (return cont)
    
    -- Call the while function
    initializers <- mapM (asVal <=< genExpr tenv) (map snd inits)
    return $ LL.ReturnE $ LL.PrimCallA (LL.VarV while_var) initializers 

  -- Generate the continuation
  genLValues tenv lhs (LL.ValA $ map LL.VarV param_vars) param_types
  mk_cont

-- | Generate a function for a while statment.
--
-- > letrec f (p1 ... pN) -> (t1 ... tN) {
-- >   if (cond) {
-- >     tmp1 ... tmpN = body;
-- >     f (tmp1 ... tmpN);
-- >   } else {
-- >     cont (tmp1 ... tmpN);
-- >   };
genWhileFunction :: TypeEnv
                 -> LL.Var -> [(Parameter Typed, Expr Typed)] -> Expr Typed
                 -> Stmt Typed -> G LL.Stm -> G ()
genWhileFunction tenv while_var params cond body cont = do
  let param_vars = [v | (Parameter _ v, _) <- params]
      return_types = [convertToValueType t | (Parameter t _, _) <- params]

  function_body <- lift $ execBuild return_types $ do
    -- When condition fails, run the continuation
    let false_path = cont
    
    -- When it succeeds, run the body and loop
    let true_path = do
          -- Create new temporary variables to hold live-out values
          return_vars <- lift $ mapM LL.newAnonymousVar return_types
          
          -- Generate body and bind its result
          bindAtom return_vars =<< genStmtAtom tenv body
          
          -- Loop
          return $ LL.ReturnE $ LL.PrimCallA (LL.VarV while_var) (map LL.VarV return_vars)
          
    cond' <- asVal =<< genExpr tenv cond
    genIf cond' true_path false_path
  
  emitLetrec [LL.FunDef while_var $
              LL.primFun param_vars return_types function_body]

-- | Generate an if-else expression in tail position
genTailIf :: TypeEnv -> Expr Typed -> Stmt Typed -> Stmt Typed -> G LL.Stm
genTailIf tenv cond if_true if_false = do
  cond' <- asVal =<< genExpr tenv cond
  genIf cond' (genStmt tenv if_true) (genStmt tenv if_false)

genMedialIf :: TypeEnv -> Expr Typed -> Stmt Typed -> Stmt Typed
            -> [LValue Typed]
            -> G a -> G a
genMedialIf tenv cond if_true if_false lhs continuation = do
  cond' <- asVal =<< genExpr tenv cond
  
  -- Create new temporary variables to hold live-out values
  let return_types = map convertToValueType $ stmtType if_true
  return_vars <- lift $ mapM LL.newAnonymousVar return_types
  
  -- Generate the branch
  getContinuation True return_vars $ \cont ->
    let gen_branch br = do
          -- Generate a branch of the 'if' statement that ends by
          -- passing its live-out values to the continuation
          bindAtom return_vars =<< genStmtAtom tenv br
          return cont
    in genIf cond' (gen_branch if_true) (gen_branch if_false)
  
  -- Generate the continuation
  genLValues tenv lhs (LL.ValA $ map LL.VarV return_vars) return_types
  continuation

-- | Generate code to assign to some LValues
genLValues :: TypeEnv -> [LValue Typed] -> LL.Atom -> [LL.ValueType] -> G ()
genLValues tenv lvals atom atom_types = do
  (unzip -> (binders, code)) <- zipWithM (genLValue tenv) lvals atom_types
  bindAtom binders atom
  sequence_ code

-- | Generate code from an LValue.
--
--   This generates variables that should be bound and code to
--   do any necessary evaluation for the LValue.  Any values not
--   bound by the LValue is returned.
genLValue :: TypeEnv -> LValue Typed -> LL.ValueType -> G (LL.Var, G ())
genLValue tenv lvalue ty =
  case lvalue
  of VarL v ->
       return (v, return ())

     StoreL dst -> do
       -- Create a temporary variable to hold the stored value
       tmpvar <- lift $ LL.newAnonymousVar ty

       -- Evaluate the destination address
       dst_val <- asVal =<< genExpr tenv dst
       let write_dst = primStore ty dst_val (LL.VarV tmpvar)

       return (tmpvar, write_dst)

     StoreFieldL base fld -> do
       -- Create a temporary variable to hold the stored value
       tmpvar <- lift $ LL.newAnonymousVar ty

       -- Compute the destination address
       base_val <- asVal =<< genExpr tenv base
       (offset, _) <- genField tenv fld
       let write_dst = primStoreOff ty base_val offset (LL.VarV tmpvar)
       
       return (tmpvar, write_dst)

     UnpackL rec field_binders -> do
       -- Create a temporary variable to hold the stored value
       tmpvar <- lift $ LL.newAnonymousVar ty
       
       let record = convertToStaticRecord rec
           fields = LowLevel.Record.recordFields record
           field_type fld =
             case fieldType fld
             of PrimField pt -> LL.PrimType pt
                RecordField rec -> LL.RecordType rec
                _ -> internalError "genLValue: Can't put this record field in a variable"
           field_types = map field_type fields
           atom = LL.UnpackA record (LL.VarV tmpvar)
       let unpack_it = genLValues tenv field_binders atom field_types
       return (tmpvar, unpack_it)

     WildL -> do
       tmpvar <- lift $ LL.newAnonymousVar ty
       return (tmpvar, return ())

genFunctionDef :: TypeEnv -> FunctionDef Typed -> FreshVarM LL.FunDef
genFunctionDef tenv fdef = do
  let params = [v | Parameter _ v <- functionParams fdef]
      returns = map convertToValueType $ functionReturns fdef
  body <- execBuild returns $ genStmt tenv $ functionBody fdef
  
  let function =
        if functionIsProcedure fdef
        then LL.primFun params returns body
        else LL.closureFun params returns body
  return (LL.FunDef (functionName fdef) function)

genDataDef :: DataDef Typed -> FreshVarM LL.DataDef
genDataDef ddef = do
  -- Get the data type
  let record_type = case exprType (dataValue ddef)
                    of [RecordT rec] -> convertToStaticRecord rec
                       _ -> internalError "genDataDef"

  -- Convert the initializer
  value <- genDataExpr (dataValue ddef)
  
  return $ LL.DataDef (dataName ddef) record_type [value]

genDef :: Def Typed -> FreshVarM (Either LL.FunDef LL.DataDef)
genDef (DataDefEnt d) = fmap Right $ genDataDef d
genDef (FunctionDefEnt d) = fmap Left $ genFunctionDef emptyTypeEnv d
genDef (RecordDefEnt _) = internalError "genDef: Unexpected record definition"

genDefs :: [Def Typed] -> FreshVarM ([LL.FunDef], [LL.DataDef])
genDefs defs = do
  defs' <- mapM genDef defs
  return $ partitionEithers defs'

generateLowLevelModule :: [LL.Import]
                       -> [Def Typed]
                       -> IO LL.Module
generateLowLevelModule externs defs =
  withTheLLVarIdentSupply $ \var_ids -> runFreshVarM var_ids $ do
    (fun_defs, data_defs) <- genDefs defs
    return $ LL.Module externs fun_defs data_defs []
