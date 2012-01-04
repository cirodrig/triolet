{-| Turn the parser data structures into low-level code.
-}

{-# LANGUAGE ViewPatterns #-}
module LLParser.GenLowLevel2 where

import Control.Monad
import Control.Monad.Trans
import Data.Either
import qualified Data.IntMap as IntMap
import Data.List
import qualified Data.Set as Set

import Common.Error
import Common.Identifier
import Common.Label
import Common.Supply
import LLParser.AST
import LLParser.TypeInference
import LowLevel.Build
import LowLevel.Builtins
import LowLevel.FreshVar
import LowLevel.CodeTypes hiding(Field)
import qualified LowLevel.Syntax as LL
import Globals
import Export

data GenExpr = GenVal LL.Val
             | GenAtom [ValueType] LL.Atom

asVal :: GenExpr -> G LL.Val
asVal (GenVal v) = return v
asVal (GenAtom [vtype] atom) = emitAtom1 vtype atom
asVal (GenAtom _ _) =
  internalError "asVal: Expression does not have one return value"

asAtom :: GenExpr -> G LL.Atom
asAtom (GenVal v) = return (LL.ValA [v])
asAtom (GenAtom _ atom) = return atom

returnType :: GenExpr -> [ValueType]
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

lookupTypeSynonym syn m =
  case IntMap.lookup (fromIdent (typeSynonymID syn)) m
  of Just t -> t
     Nothing -> internalError "lookupTypeSynonym"

parameterVar (Parameter _ (Just v)) = v
parameterVar (Parameter _ Nothing)  = internalError "parameterVar: No variable"

-------------------------------------------------------------------------------

type G a = Gen FreshVarM a

-- | Generate code for a type whose size and alignemnt are dynamically
--   computed
convertToDynamicFieldType :: TypeEnv -> Type Typed -> G DynamicFieldType
convertToDynamicFieldType tenv ty = 
  case ty
  of PrimT pt -> return $ PrimField pt
     NamedT (SynonymT syn) ->
       let ty' = lookupTypeSynonym syn tenv
       in case dynamicTypeRecord ty'
          of Just dyn_record ->
               return $ RecordField dyn_record
             Nothing ->
               return $ BytesField (dynamicTypeSize ty') (dynamicTypeAlign ty')
     NamedT (RecordT record) -> do
       dyn_record <- convertToDynamicRecord tenv record
       return $ RecordField dyn_record
     ArrayT mut size elt_type -> do
       elt_type' <- genDynamicType tenv elt_type
       padded_size <- genArrayElementSize elt_type'
       num_elts <- asVal =<< genExpr tenv size
       array_size <- nativeMulUZ padded_size num_elts
       return $ BytesField array_size (dynamicTypeAlign elt_type')
     BytesT size align -> do
       size_val <- asVal =<< genExpr tenv size
       align_val <- asVal =<< genExpr tenv align
       return $ BytesField size_val align_val
     AppT ty args ->
       -- Apply, then convert
       convertToDynamicFieldType tenv $ applyTemplate ty args

convertToDynamicRecord :: TypeEnv -> TypedRecord -> G DynamicRecord
convertToDynamicRecord tenv rec = do
  field_types <- forM (typedRecordFields rec) $ \(FieldDef m t _) -> do 
    t' <- convertToDynamicFieldType tenv t
    return (m, t')
  createDynamicRecord field_types

convertTypeToDynamicRecord :: TypeEnv -> Type Typed -> G DynamicRecord
convertTypeToDynamicRecord tenv ty =
  case dereferenceTypeSynonym ty
  of NamedT (RecordT rec) -> convertToDynamicRecord tenv rec
     _ -> error "Expecting record type"

genDynamicType :: TypeEnv -> Type Typed -> G DynamicType
genDynamicType tenv ty =
  case ty
  of PrimT pt ->
       let size = nativeWordV $ sizeOf pt
           align = nativeWordV $ alignOf pt
       in return $ DynamicType size align Nothing
     NamedT (SynonymT syn) -> do
       return $ lookupTypeSynonym syn tenv
     NamedT (RecordT rec) -> do
       dynamic_rec <- convertToDynamicRecord tenv rec
       return $ DynamicType (recordSize dynamic_rec) (recordAlignment dynamic_rec) (Just dynamic_rec)
     NamedT (TemplateT {}) ->
       internalError "genDynamicType: Underapplied type"
     BytesT size align -> do
       size_val <- asVal =<< genExpr tenv size
       align_val <- asVal =<< genExpr tenv align
       return $ DynamicType size_val align_val Nothing
     ArrayT mut size elt_type -> do
       elt_type' <- genDynamicType tenv elt_type
       padded_size <- genArrayElementSize elt_type'
       num_elts <- asVal =<< genExpr tenv size
       total_size <- nativeMulUZ padded_size num_elts
       return $ DynamicType total_size (dynamicTypeAlign elt_type') Nothing
     AppT ty args ->
       genDynamicType tenv $ applyTemplate ty args

-- | Generate code of an expression used to initialize global data.
genDataExpr :: Expr Typed -> FreshVarM LL.Val
genDataExpr expr =
  case expExp expr
  of VarE v -> return $ LL.VarV v
     IntLitE ty n
       | PrimT (IntType sgn sz) <- ty ->
           if not $ isRepresentableInt sgn sz n
           then internalError "genExpr: Integer literal out of range"
           else return $ LL.LitV (LL.intL sgn sz n)
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
     RecordE rec_type fields -> do
       let srecord = case dereferenceTypeSynonym rec_type
                     of NamedT (RecordT rec) -> convertToStaticRecord rec
                        _ -> internalError "genExpr: Expecting record type"
       when (length (LowLevel.CodeTypes.recordFields srecord) /= length fields) $
         error "Wrong number of fields in record expression"
       fields' <- mapM genDataExpr fields
       return $ LL.RecV srecord fields'
     SizeofE ty ->
       let ty' = convertToValueType ty
           lit = mkIntLit (PrimType nativeWordType) (fromIntegral $ sizeOf ty')
       in return $ LL.LitV lit
     AlignofE ty ->
       let ty' = convertToValueType ty
           lit = mkIntLit (PrimType nativeWordType) (fromIntegral $ alignOf ty')
       in return $ LL.LitV lit

mkIntLit :: ValueType -> Integer -> LL.Lit
mkIntLit ty n =
  case ty
  of PrimType (IntType sgn sz) ->
       if not $ isRepresentableInt sgn sz n 
       then internalError "mkIntLit: Integer out of range"
       else LL.intL sgn sz n
     _ -> error "Invalid integer type"

mkFloatLit :: ValueType -> Double -> LL.Lit
mkFloatLit ty n =
  case ty
  of PrimType (FloatType sz) -> LL.FloatL sz n
     _ -> error "Invalid floating-point type"

mkWordVal :: Expr Typed -> LL.Val
mkWordVal expr =
  case expExp expr
  of IntLitE _ n -> nativeWordV n
     VarE v -> LL.VarV v

-- | Generate code to load or store a record field.  Return the field offset,
--   its mutability,
--   and the type at which the field should be accessed.
genField :: TypeEnv -> Field Typed -> G (LL.Val, Mutability, ValueType)
genField tenv (Field base_type fnames cast_type) =
  get_field_offset (nativeIntV 0) base_type fnames
  where
    get_field_offset base_offset base_type (ArrayFS index:fnames) =
      case dereferenceTypeSynonym base_type
      of ArrayT mut array_size elt_type -> do
           -- Get the size and alignment of an array element
           dyn_elt_type <- genDynamicType tenv elt_type
           
           -- Compute the size of one array element
           padded_size <- genArrayElementSize dyn_elt_type
           
           -- Compute the offset
           index_val <- asVal =<< genExpr tenv index
           offset <- nativeMulZ index_val padded_size
           new_base_offset <- nativeAddZ base_offset offset
           
           case fnames of
             [] -> let val_type = convertToValueType elt_type
                   in return_field_offset new_base_offset mut val_type
             _ -> get_field_offset new_base_offset elt_type fnames
         _ -> internalError "genField: Base type is not an array"

    get_field_offset base_offset base_type (RecordFS fname:fnames) = do
      dyn_type <- genDynamicType tenv base_type
      let dyn_rec =
            case dynamicTypeRecord dyn_type
            of Just dyn_rec -> dyn_rec
               Nothing -> internalError "genField: Base type is not a record"
          static_rec =
            case dereferenceTypeSynonym base_type
            of NamedT (RecordT rec) -> rec
               _ -> internalError "genField: Base type is not a record"
          field_index =
            case findIndex (match_name fname) $ typedRecordFields static_rec
            of Just ix -> ix
               Nothing -> 
                 internalError $ "genField: No field named '" ++ fname ++ "'"

      let rfield = typedRecordFields static_rec !! field_index
          dfield = dyn_rec !!: field_index

      new_base_offset <- nativeAddZ base_offset (fieldOffset dfield)
      case fnames of
        [] -> let mutable = fieldMutable dfield
                  field_type = dynamicToStaticFieldType $ fieldType dfield
              in return_field_offset new_base_offset mutable field_type
        _  -> case rfield
              of FieldDef _ next_rec _ ->
                   get_field_offset new_base_offset next_rec fnames
                 _ -> internalError "genField"

    return_field_offset offset mutable field_type
      | LL.valType offset /= PrimType nativeIntType =
        internalError "genField: Offset has wrong type"
      | otherwise =
        let ty = case cast_type
                 of Just t -> convertToValueType t
                    Nothing -> field_type
        in return (offset, mutable, ty)

    match_name want_name (FieldDef _ _ name) = name == want_name

genArrayElementSize dyn_elt_type =
  let elt_size = dynamicTypeSize dyn_elt_type
      elt_align = dynamicTypeAlign dyn_elt_type
  in genPaddedSize elt_size elt_align


genPaddedSize sz al = do
  native_sz <- primCastZ (PrimType nativeIntType) sz
  neg_sz <- nativeNegateZ native_sz
  native_al <- primCastZ (PrimType nativeIntType) al
  padding <- neg_sz `nativeModZ` native_al
  nativeAddZ native_sz padding

dynamicToStaticFieldType :: DynamicFieldType -> ValueType
dynamicToStaticFieldType (PrimField pt) = PrimType pt
dynamicToStaticFieldType (RecordField r) =
  RecordType $ dynamicToStaticRecordType r

-- | Convert to a static record type.  The type must not contain non-constant
--   expressions.  Throw an error if it doesn't satisfy these conditions.
dynamicToStaticRecordType :: DynamicRecord -> StaticRecord
dynamicToStaticRecordType r =
  constStaticRecord $ map to_field $ LowLevel.CodeTypes.recordFields r
  where
    to_field f = valueToFieldType $ dynamicToStaticFieldType $ fieldType f

-- | Create a record type corresponding to a set of local variables.
localsRecord :: Locals Typed -> StaticRecord
localsRecord locals =
  let field_types = [(Mutable, convertToStaticFieldType t)
                    | Parameter t _ <- locals]
  in staticRecord field_types

-- | Define a pointer variable that points to each local variable.
--   Also return the size of the local stack frame.
genLocals :: Locals Typed -> G Int
genLocals [] = return 0
genLocals locals =
  let rec = localsRecord locals
      offsets = [nativeIntV $ fieldOffset f
                | f <- LowLevel.CodeTypes.recordFields rec]
      local_vars = map parameterVar locals
  in do locals_ptr <- emitAtom1 (PrimType PointerType) (LL.PrimA LL.PrimGetFrameP [])
        zipWithM_ (primAddPAs locals_ptr) offsets local_vars
        return $ recordSize rec

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
       let record_type = case record
                         of NamedT (RecordT rec) -> convertToStaticRecord rec
                            _ -> internalError "genExpr: Expecting record type"
           atom = LL.PackA record_type fs'
       when (length (LowLevel.CodeTypes.recordFields record_type) /= length fs) $
         error "Wrong number of fields in record expression"
       return $ GenAtom [RecordType record_type] atom
     FieldE base fld -> do
       addr <- asVal =<< subexpr base
       (offset, _, _) <- genField tenv fld
       let atom = LL.PrimA LL.PrimAddP [addr, offset]
       return $ GenAtom [PrimType PointerType] atom
     LoadFieldE base fld -> do
       addr <- asVal =<< subexpr base
       (offset, mutable, ty) <- genField tenv fld
       let atom = LL.PrimA (LL.PrimLoad mutable ty) [addr, offset]
       return $ GenAtom [ty] atom
     LoadE ty base -> do
       addr <- asVal =<< subexpr base
       let llty = convertToValueType ty
       let atom = LL.PrimA (LL.PrimLoad Mutable llty) [addr, nativeIntV 0]
       return $ GenAtom [llty] atom
     CallE returns op args -> do
       op' <- asVal =<< subexpr op
       args' <- mapM (asVal <=< subexpr) args
       let atom = LL.closureCallA op' args'
           return_types = map convertToValueType returns
       return $ GenAtom return_types atom
     PrimCallE returns op args -> do
       op' <- asVal =<< subexpr op
       args' <- mapM (asVal <=< subexpr) args
       let atom = LL.primCallA op' args'
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
       dyn_type <- genDynamicType tenv ty
       return $ GenVal $ dynamicTypeSize dyn_type
     AlignofE ty -> do
       dyn_type <- genDynamicType tenv ty
       return $ GenVal $ dynamicTypeAlign dyn_type
  where
    subexpr e = genExpr tenv e
    data_expr = lift $ fmap GenVal $ genDataExpr expr

genUnaryOp :: UnaryOp -> GenExpr -> G GenExpr
genUnaryOp op arg = 
  case op
  of NegateOp ->
       -- Create the expression [| 0 - arg |]
       case returnType arg
       of rt@[PrimType (IntType sgn sz)] -> do
            arg_val <- asVal arg
            let operand = LL.LitV $ LL.IntL sgn sz 0
                op = LL.PrimSubZ sgn sz
                atom = LL.PrimA op [operand, arg_val]
            return $ GenAtom rt atom
     NotOp ->
       case returnType arg
       of rt@[PrimType BoolType] -> do
            arg_val <- asVal arg
            return $ GenAtom rt $ LL.PrimA LL.PrimNot [arg_val]

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
     DivOp -> division
     IntDivOp -> integer_division
     AndOp -> boolean LL.PrimAnd
     OrOp -> boolean LL.PrimOr
     _ -> internalError "mkBinary: Unhandled binary operator"
  where
    comparison cmp_op = do
      let operator =
            case returnType l_arg
            of [PrimType (IntType sgn sz)] -> LL.PrimCmpZ sgn sz cmp_op
               [PrimType (FloatType sz)] -> LL.PrimCmpF sz cmp_op
               [PrimType PointerType] -> LL.PrimCmpP cmp_op
               _ -> internalError "Binary comparison not implemented for this type"
      l_val <- asVal l_arg
      r_val <- asVal r_arg
      let atom = LL.PrimA operator [l_val, r_val]
      return $ GenAtom [PrimType BoolType] atom
    
    atomic_int atomic_op = do
      let operator =
            case returnType r_arg
            of [PrimType (IntType sgn sz)] -> atomic_op sgn sz
      l_val <- asVal l_arg
      r_val <- asVal r_arg
      let atom = LL.PrimA operator [l_val, r_val]
      return $ GenAtom (returnType r_arg) atom

    pointer_add = do
      l_val <- asVal l_arg
      r_val <- asVal r_arg
      let atom = LL.PrimA LL.PrimAddP [l_val, r_val]
      return $ GenAtom [PrimType PointerType] atom
    
    arithmetic int_op float_op = do
      l_val <- asVal l_arg
      r_val <- asVal r_arg
      let atom =
            case returnType l_arg
            of [PrimType (IntType sgn sz)] ->
                 LL.PrimA (int_op sgn sz) [l_val, r_val]
               [PrimType (FloatType sz)] ->
                 LL.PrimA (float_op sz) [l_val, r_val]
               _ -> internalError "Arithmetic operator not implemented for this type"
      return $ GenAtom (returnType l_arg) atom
    
    boolean op =
      case returnType l_arg
      of [PrimType BoolType] -> do
           l_val <- asVal l_arg
           r_val <- asVal r_arg
           let atom = LL.PrimA op [l_val, r_val]
           return $ GenAtom [PrimType BoolType] atom
         _ -> internalError "Wrong argument type for boolean operator"
    
    division = do
      l_val <- asVal l_arg
      r_val <- asVal r_arg
      atom <-
        case returnType l_arg
        of [PrimType (FloatType sz)] ->
             return $ LL.PrimA (LL.PrimDivF sz) [l_val, r_val]
      return $ GenAtom (returnType l_arg) atom
    
    integer_division = do
      l_val <- asVal l_arg
      r_val <- asVal r_arg
      atom <-
        case returnType l_arg
        of [PrimType (IntType sgn sz)] ->
             return $ LL.PrimA (LL.PrimDivZ sgn sz) [l_val, r_val]
           [rty@(PrimType (FloatType sz))] -> do
             quotient <- emitAtom1 rty $ LL.PrimA (LL.PrimDivF sz) [l_val, r_val]
             let round_op = LL.PrimRoundF LL.Floor sz Signed nativeIntSize
             return $ LL.PrimA round_op [quotient]
      return $ GenAtom (returnType l_arg) atom
    
genCast :: ValueType -> GenExpr -> G GenExpr
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
       | otherwise -> do
         val <- asVal e
         case () of
           _ | e_sz == g_sz ->
                 success $ LL.PrimA (LL.PrimCastZ g_sgn e_sgn g_sz) [val]
             | e_sgn == g_sgn ->
                 success $ LL.PrimA (LL.PrimExtendZ g_sgn g_sz e_sz) [val]
             | e_sz > g_sz -> do
                 -- Change size, then change sign
                 val' <- emitAtom1 (PrimType (IntType g_sgn e_sz)) $
                         LL.PrimA (LL.PrimExtendZ g_sgn g_sz e_sz) [val]
                 success $ LL.PrimA (LL.PrimCastZ g_sgn e_sgn e_sz) [val']
             | otherwise -> do
                 val <- asVal e
                 -- Change sign, then change size
                 val' <- emitAtom1 (PrimType (IntType e_sgn g_sz)) $
                         LL.PrimA (LL.PrimCastZ g_sgn e_sgn g_sz) [val]
                 success $ LL.PrimA (LL.PrimExtendZ e_sgn g_sz e_sz) [val']
         
     (IntType Signed e_sz, FloatType g_sz) -> do
       val <- asVal e
       success $ LL.PrimA (LL.PrimCastFToZ g_sz e_sz) [val]
     (FloatType e_sz, IntType Signed g_sz) -> do
       val <- asVal e
       success $ LL.PrimA (LL.PrimCastZToF g_sz e_sz) [val]
     _ -> cannot
  where
    given_type =
      case returnType e
      of [PrimType t] -> t
         _ -> internalError "genCast: Cannot cast from type"
    
    expected_type =
      case ty
      of PrimType t -> t
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
       emitLetrec . LL.Rec =<< lift (mapM (genFunctionDef tenv) fdefs)
       genStmt tenv body
     TypedefS (SynonymT (TypeSynonym type_id _)) ty stmt -> do
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
       emitLetrec . LL.Rec =<< lift (mapM (genFunctionDef tenv) fdefs)
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
  while_var <- lift $ LL.newAnonymousVar (PrimType PointerType)
  
  -- When done, return the loop-carried variables
  let cont = return $ LL.ReturnE $ LL.ValA
             [LL.VarV $ parameterVar p | (p, _) <- inits]
  return_types <- getReturnTypes
  genWhileFunction tenv while_var inits return_types cond body cont
  initializers <- mapM (asVal <=< genExpr tenv) (map snd inits)
  return $ LL.ReturnE $ LL.primCallA (LL.VarV while_var) initializers

genMedialWhile :: TypeEnv -> [(Parameter Typed, Expr Typed)] -> Expr Typed
               -> Stmt Typed -> [LValue Typed] -> G a -> G a
genMedialWhile tenv inits cond body lhs mk_cont = do
  let param_vars = [parameterVar p | (p, _) <- inits]
      param_types = map LL.varType param_vars
  while_var <- lift $ LL.newAnonymousVar (PrimType PointerType)
  
  -- Turn the continuation into a function so we can call it.
  return_types <- getReturnTypes
  getContinuation True param_vars $ \cont -> do
    -- Generate the while function
    genWhileFunction tenv while_var inits return_types cond body (return cont)
    
    -- Call the while function
    initializers <- mapM (asVal <=< genExpr tenv) (map snd inits)
    return $ LL.ReturnE $ LL.primCallA (LL.VarV while_var) initializers 

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
                 -> LL.Var
                 -> [(Parameter Typed, Expr Typed)]
                 -> [ValueType]
                 -> Expr Typed
                 -> Stmt Typed -> G LL.Stm -> G ()
genWhileFunction tenv while_var params return_types cond body cont = do
  let param_vars = [parameterVar p | (p, _) <- params]
      -- Types of values that are passed to the continuation
      live_out_types = [convertToValueType t | (Parameter t _, _) <- params]

  function_body <- lift $ execBuild return_types $ do
    -- When condition fails, run the continuation
    let false_path = cont
    
    -- When it succeeds, run the body and loop
    let true_path = do
          -- Create new temporary variables to hold live-out values
          return_vars <- lift $ mapM LL.newAnonymousVar live_out_types
          
          -- Generate body and bind its result
          bindAtom return_vars =<< genStmtAtom tenv body
          
          -- Loop
          return $ LL.ReturnE $ LL.primCallA (LL.VarV while_var) (map LL.VarV return_vars)
          
    cond' <- asVal =<< genExpr tenv cond
    genIf cond' true_path false_path
  
  emitLetrec (LL.Rec [LL.Def while_var $
                      LL.primFun param_vars return_types function_body])

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
genLValues :: TypeEnv -> [LValue Typed] -> LL.Atom -> [ValueType] -> G ()
genLValues tenv lvals atom atom_types = do
  (unzip -> (binders, code)) <- zipWithM (genLValue tenv) lvals atom_types
  bindAtom binders atom
  sequence_ code

-- | Generate code from an LValue.
--
--   This generates variables that should be bound and code to
--   do any necessary evaluation for the LValue.  Any values not
--   bound by the LValue is returned.
genLValue :: TypeEnv -> LValue Typed -> ValueType -> G (LL.Var, G ())
genLValue tenv lvalue ty =
  case lvalue
  of VarL v ->
       return (v, return ())

     StoreL dst -> do
       -- Create a temporary variable to hold the stored value
       tmpvar <- lift $ LL.newAnonymousVar ty

       -- Evaluate the destination address
       dst_val <- asVal =<< genExpr tenv dst
       let write_dst = primStore Mutable ty dst_val (LL.VarV tmpvar)

       return (tmpvar, write_dst)

     StoreFieldL base fld -> do
       -- Create a temporary variable to hold the stored value
       tmpvar <- lift $ LL.newAnonymousVar ty

       -- Compute the destination address
       base_val <- asVal =<< genExpr tenv base
       (offset, mutable, _) <- genField tenv fld
       let write_dst = primStoreOff mutable ty base_val offset (LL.VarV tmpvar)
       
       return (tmpvar, write_dst)

     UnpackL rec field_binders -> do
       -- Create a temporary variable to hold the stored value
       tmpvar <- lift $ LL.newAnonymousVar ty
       
       let record = case dereferenceTypeSynonym rec
                      of NamedT (RecordT r) -> convertToStaticRecord r
                         _ -> internalError "genLValue"
           fields = LowLevel.CodeTypes.recordFields record
           field_type fld =
             case fieldType fld
             of PrimField pt -> PrimType pt
                RecordField rec -> RecordType rec
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
  let params = map parameterVar $ functionParams fdef
      returns = map convertToValueType $ functionReturns fdef
  -- Generate function body
  (body, locals_size) <- execBuild' returns $ do 
    locals_size <- genLocals $ functionLocals fdef
    body <- genStmt tenv $ functionBody fdef
    return (body, locals_size)
  
  let conv = if functionIsProcedure fdef then PrimCall else ClosureCall
      function =
        LL.mkFun conv (functionInlineRequest fdef) locals_size params returns body
  return (LL.Def (functionName fdef) function)

genDataDef :: DataDef Typed -> FreshVarM LL.DataDef
genDataDef ddef = do
  -- Convert the initializer
  value <- genDataExpr (dataValue ddef)  
  return $ LL.Def (dataName ddef) (LL.StaticData value)

genDef :: Def Typed -> FreshVarM  LL.GlobalDef
genDef (DataDefEnt d) = fmap LL.GlobalDataDef $ genDataDef d
genDef (FunctionDefEnt d) = fmap LL.GlobalFunDef $ genFunctionDef emptyTypeEnv d
genDef (RecordDefEnt _) = internalError "genDef: Unexpected record definition"

genDefs :: [Def Typed] -> FreshVarM [LL.GlobalDef]
genDefs defs = mapM genDef defs

generateLowLevelModule :: ModuleName
                       -> [LL.Import]
                       -> [Def Typed]
                       -> IO LL.Module
generateLowLevelModule module_name externs defs = do
  supply <- newLocalIDSupply
  withTheLLVarIdentSupply $ \var_ids -> runFreshVarM var_ids $ do
    global_defs <- genDefs defs
    
    -- Identify the actual imports and exports of this module
    let defined_here = Set.fromList $ map LL.globalDefiniendum global_defs
        (exports, imports) = find_exports defined_here
    
    return $ LL.Module module_name supply externs [LL.Rec global_defs] exports
  where
    -- If a variable is external and defined here, it's exported
    find_exports defined_here = partitionEithers $ map pick_export externs
      where
        pick_export impent
          | impent_var `Set.member` defined_here =
              -- Assume it's exported to other Pyon code
              Left (impent_var, PyonExportSig)
          | otherwise = Right impent
          where
            impent_var = LL.importVar impent
