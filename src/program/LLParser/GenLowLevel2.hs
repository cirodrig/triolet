{-| Turn the parser data structures into low-level code.
-}

{-# LANGUAGE ViewPatterns #-}
module LLParser.GenLowLevel2 where

import Control.Monad
import Control.Monad.Trans
import Data.Either
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

type G a = Gen FreshVarM a

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
genField :: Field Typed -> G (LL.Val, LL.ValueType)
genField (Field rec fnames cast_type) =
  get_field_offset 0 rec fnames
  where
    get_field_offset base_offset rec (fname:fnames) =
      case findIndex (match_name fname) $ typedRecordFields0 rec
      of Just ix ->
           let rfield = typedRecordFields0 rec !! ix
               sfield = convertToStaticRecord rec !!: ix
               offset = base_offset + fieldOffset sfield
           in case fnames
              of [] -> return_field_offset offset sfield
                 _  -> case rfield
                       of FieldDef (RecordT next_rec) _ ->
                            get_field_offset offset next_rec fnames
                          _ -> internalError "genField"
         Nothing ->
           internalError "genField"

    return_field_offset offset field =
      let ty = case cast_type
               of Just t -> convertToValueType t
                  Nothing -> case fieldType field
                             of PrimField pt -> LL.PrimType pt
                                RecordField r -> LL.RecordType r
                                _ -> internalError "genField"
      in return (nativeIntV offset, ty)

    match_name want_name (FieldDef _ name) = name == want_name

-- | Generate code of an expression
genExpr :: Expr Typed -> G GenExpr
genExpr expr =
  case expExp expr
  of VarE {} -> data_expr
     IntLitE {} -> data_expr
     FloatLitE {} -> data_expr
     BoolLitE {} -> data_expr
     NilLitE {} -> data_expr
     NullLitE {} -> data_expr
     RecordE record fs -> do
       fs' <- mapM (asVal <=< genExpr) fs
       let record_type = convertToStaticRecord record
           atom = LL.PackA record_type fs'
       return $ GenAtom [LL.RecordType record_type] atom
     FieldE base fld -> do
       addr <- asVal =<< genExpr base
       (offset, _) <- genField fld
       let atom = LL.PrimA LL.PrimAddP [addr, offset]
       return $ GenAtom [LL.PrimType PointerType] atom
     LoadFieldE base fld -> do
       addr <- asVal =<< genExpr base
       (offset, ty) <- genField fld
       let atom = LL.PrimA (LL.PrimLoad ty) [addr, offset]
       return $ GenAtom [ty] atom
     LoadE ty base -> do
       addr <- asVal =<< genExpr base
       let llty = convertToValueType ty
       let atom = LL.PrimA (LL.PrimLoad llty) [addr, nativeIntV 0]
       return $ GenAtom [llty] atom
     CallE returns op args -> do
       op' <- asVal =<< genExpr op
       args' <- mapM (asVal <=< genExpr) args
       let atom = LL.CallA op' args'
           return_types = map convertToValueType returns
       return $ GenAtom return_types atom
     PrimCallE returns op args -> do
       op' <- asVal =<< genExpr op
       args' <- mapM (asVal <=< genExpr) args
       let atom = LL.PrimCallA op' args'
           return_types = map convertToValueType returns
       return $ GenAtom return_types atom
     UnaryE op arg -> do
       arg' <- genExpr arg
       genUnaryOp op arg'
     BinaryE op l r -> do
       l' <- genExpr l
       r' <- genExpr r
       genBinaryOp op l' r'
     CastE e ty -> do
       e' <- genExpr e
       genCast (convertToValueType ty) e'
     SizeofE ty -> do
       let size =
             case ty
             of BytesT size _ -> mkWordVal size
                _ -> nativeWordV $ sizeOf $ convertToValueType ty
       return $ GenVal size
     AlignofE ty -> do
       let align =
             case ty
             of BytesT _ align -> mkWordVal align
                _ -> nativeWordV $ alignOf $ convertToValueType ty
       return $ GenVal align
  where
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

genAtom :: Atom Typed -> G LL.Atom
-- If there's only one expression, make an atom
genAtom (ValA [expr]) = asAtom =<< genExpr expr

genAtom (ValA exprs)
  | all ((1 ==) . length . exprType) exprs = do
      -- If there are many single-valued expressions,
      -- bind each to one value
      values <- mapM (asVal <=< genExpr) exprs 
      return (LL.ValA values)
  | otherwise = do
      -- Create values for each expression, then
      -- concatenate them into an atom
      values <- forM exprs $ \expr -> do
        expr' <- genExpr expr
        emitAtom (returnType expr') =<< asAtom expr'
      return (LL.ValA $ concat values)

-- | Generate code of a statement
genStmt :: Stmt Typed -> G LL.Stm
genStmt stmt =
  case stmt
  of LetS lvals atom body -> do
       genLetAssignment lvals atom
       genStmt body
     IfS cond if_true if_false Nothing ->
       genTailIf cond if_true if_false
     IfS cond if_true if_false (Just (lhs, continuation)) ->
       genMedialIf cond if_true if_false lhs (genStmt continuation)
     ReturnS atom -> do 
       atom' <- genAtom atom
       return (LL.ReturnE atom')

genStmtAtom :: Stmt Typed -> G LL.Atom
genStmtAtom stmt =
  case stmt
  of LetS lvals atom body -> do
       genLetAssignment lvals atom
       genStmtAtom body
     IfS cond if_true if_false Nothing -> do
       -- Generate an if statement, then group its result values into an atom
       let return_types = map convertToValueType $ stmtType if_true
       return_vars <- lift $ mapM LL.newAnonymousVar return_types

       let lvals = map VarL return_vars
           return_atom = LL.ValA $ map LL.VarV return_vars
       genMedialIf cond if_true if_false lvals (return return_atom)
     IfS cond if_true if_false (Just (lhs, continuation)) ->
       genMedialIf cond if_true if_false lhs (genStmtAtom continuation)
     ReturnS atom -> do 
       genAtom atom

-- | Create code of an assignment 
genLetAssignment :: [LValue Typed] -> Atom Typed -> G ()
genLetAssignment lvals atom = do
  rhs <- genAtom atom
  genLValues lvals rhs (map convertToValueType $ atomType atom)

-- | Generate an if-else expression in tail position
genTailIf :: Expr Typed -> Stmt Typed -> Stmt Typed -> G LL.Stm
genTailIf cond if_true if_false = do
  cond' <- asVal =<< genExpr cond
  genIf cond' (genStmt if_true) (genStmt if_false)

genMedialIf :: Expr Typed -> Stmt Typed -> Stmt Typed -> [LValue Typed]
            -> G a -> G a
genMedialIf cond if_true if_false lhs continuation = do
  cond' <- asVal =<< genExpr cond
  
  -- Create new temporary variables to hold live-out values
  let return_types = map convertToValueType $ stmtType if_true
  return_vars <- lift $ mapM LL.newAnonymousVar return_types
  
  -- Generate the branch
  getContinuation True return_vars $ \cont ->
    let gen_branch br = do
          -- Generate a branch of the 'if' statement that ends by
          -- passing its live-out values to the continuation
          bindAtom return_vars =<< genStmtAtom br
          return cont
    in genIf cond' (gen_branch if_true) (gen_branch if_false)
  
  -- Generate the continuation
  genLValues lhs (LL.ValA $ map LL.VarV return_vars) return_types
  continuation

-- | Generate code to assign to some LValues
genLValues :: [LValue Typed] -> LL.Atom -> [LL.ValueType] -> G ()
genLValues lvals atom atom_types = do
  (unzip -> (binders, code)) <- zipWithM genLValue lvals atom_types
  bindAtom binders atom
  sequence_ code

-- | Generate code from an LValue.
--
--   This generates variables that should be bound and code to
--   do any necessary evaluation for the LValue.  Any values not
--   bound by the LValue is returned.
genLValue :: LValue Typed -> LL.ValueType -> G (LL.Var, G ())
genLValue lvalue ty =
  case lvalue
  of VarL v ->
       return (v, return ())

     StoreL dst -> do
       -- Create a temporary variable to hold the stored value
       tmpvar <- lift $ LL.newAnonymousVar ty

       -- Evaluate the destination address
       dst_val <- asVal =<< genExpr dst
       let write_dst = primStore ty dst_val (LL.VarV tmpvar)

       return (tmpvar, write_dst)

     StoreFieldL base fld -> do
       -- Create a temporary variable to hold the stored value
       tmpvar <- lift $ LL.newAnonymousVar ty

       -- Compute the destination address
       base_val <- asVal =<< genExpr base
       (offset, _) <- genField fld
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
       let unpack_it = genLValues field_binders atom field_types
       return (tmpvar, unpack_it)

     WildL -> do
       tmpvar <- lift $ LL.newAnonymousVar ty
       return (tmpvar, return ())

genFunctionDef :: FunctionDef Typed -> FreshVarM LL.FunDef
genFunctionDef fdef = do
  let params = [v | Parameter _ v <- functionParams fdef]
      returns = map convertToValueType $ functionReturns fdef
  body <- execBuild returns $ genStmt $ functionBody fdef
  
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
genDef (FunctionDefEnt d) = fmap Left $ genFunctionDef d
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
