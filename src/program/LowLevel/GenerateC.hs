
module LowLevel.GenerateC(generateCFile)
where

import Control.Monad.Writer
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Pretty
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import Gluon.Common.Error
import Gluon.Common.Identifier(fromIdent)
import Gluon.Common.Label
import LowLevel.Builtins
import LowLevel.Label
import LowLevel.Types
import LowLevel.Record
import LowLevel.Syntax
import LowLevel.Print
import LowLevel.GenerateCUtils

type CBlockItems = [CBlockItem]

-- | The set of global variables.  Global variables are bound by a 'FunDef' or
-- 'DataDef' or defined in another compilation unit.  When referencing a
-- global variable, we need to take its address.
type GlobalVars = Set.Set Var

-- | How an atom's results should be dispatched.
data ReturnValues =
    -- | Assign the results to the given (pre-existing) variables
    AssignValues [ParamVar]
    -- | Define these variables and assign to them
  | DefineValues [ParamVar]
    -- | Return the results at the given types
  | ReturnValues [PrimType]

returnTypes :: ReturnValues -> [PrimType]
returnTypes (AssignValues vs) = map varPrimType vs
returnTypes (DefineValues vs) = map varPrimType vs
returnTypes (ReturnValues ps) = ps

-- | Define an unitialized piece of data.
declareBytes :: Var -> Int -> Int -> CDecl
declareBytes v size align =
  let array = CArrDeclr [] (CArrSize False $ genSmallIntConst size) internalNode
      align_expr = genSmallIntConst align
      align_attr = CAttr (builtinIdent "aligned") [align_expr] internalNode
      declr = CDeclr (Just $ varIdent v) [array] Nothing [align_attr] internalNode
      type_spec = CTypeSpec (CCharType internalNode)
  in CDecl [type_spec] [(Just declr, Nothing, Nothing)] internalNode

-- | Declare or define a value variable
declareVariable :: Var -> Maybe CExpr -> CDecl
declareVariable v initializer =
  let (type_specs, derived_declr) = primTypeDeclSpecs $ varPrimType v
      declr = CDeclr (Just $ varIdent v) derived_declr Nothing [] internalNode
      init = case initializer
             of Nothing -> Nothing
                Just e  -> Just $ CInitExpr e internalNode
  in CDecl type_specs [(Just declr, init, Nothing)] internalNode

declareUndefVariable :: Var -> CDecl
declareUndefVariable v = declareVariable v Nothing

{-
-- | Generate an abstract declarator, used in type casting 
abstractDeclr :: PrimType -> CDecl
abstractDeclr ty =
  let (type_specs, derived_declr) = primTypeDeclSpecs ty
      declr = CDeclr Nothing derived_declr Nothing [] internalNode
  in CDecl type_specs [(Just declr, Nothing, Nothing)] internalNode

-- | Generate an abstract declarator for a pointer to the specified type,
-- used in type casting 
abstractPtrDeclr :: PrimType -> CDecl
abstractPtrDeclr ty = anonymousDecl $ ptrDeclSpecs ty
-}

pyonPointerType :: CDecl
pyonPointerType =
  let type_specs = [CTypeSpec (CTypeDef (internalIdent "PyonPtr") internalNode)]
      declr = CDeclr Nothing [] Nothing [] internalNode
  in CDecl type_specs [(Just declr, Nothing, Nothing)] internalNode

-- | Generate a constant integer expression
genIntConst :: Integral a => Signedness -> Size -> a -> CExpr
genIntConst sgn sz n =
  let sign_flag = case sgn
                  of Signed -> ""
                     Unsigned -> "U"     
      size_flag = case sz
                  of S64 -> "L"
                     _ -> ""
      read_int m =
        case readCInteger DecRepr (show m ++ sign_flag ++ size_flag)
        of Left _ -> internalError "genLit: Cannot generate integer literal"
           Right x -> x
      
      -- If the literal is negative, then generate a positive literal and then
      -- negate it
      literal = CConst $ CIntConst (read_int $ abs n) internalNode
  in if n >= 0
     then literal
     else CUnary CMinOp literal internalNode

genSmallIntConst :: Int -> CExpr
genSmallIntConst n = genIntConst Signed nativeIntSize n

-- | Cast an expression to the C equivalent of the given type
genCast :: PrimType -> CExpr -> CExpr
genCast to_type expr =
  let decl = anonymousDecl $ ptrDeclSpecs $ primTypeDeclSpecs to_type
  in CCast decl expr internalNode

-- | Generate a pointer offset expression
-- The generated expression is a call to PYON_OFF (actually a macro) 
-- with the pointer and offset
genOffset :: CExpr -> CExpr -> CExpr
genOffset base off 
  | isZeroCExpr off = base
  | otherwise =
      CCall (CVar (internalIdent "PYON_OFF") internalNode) [base, off]
      internalNode

isZeroCExpr :: CExpr -> Bool
isZeroCExpr e =
  case e
  of CConst (CIntConst n _) -> getCInteger n == 0
     _ -> False

genLit :: Lit -> CExpr

-- Null literal = (void *)0
genLit NullL =
  let zero = genSmallIntConst 0
      pointer_deriv = CPtrDeclr [] internalNode
      pointer_declr =
        CDeclr Nothing [pointer_deriv] Nothing [] internalNode
      void_ptr_type = CDecl
                      [CTypeSpec (CVoidType internalNode)]
                      [(Just pointer_declr, Nothing, Nothing)]
                      internalNode
  in CCast void_ptr_type zero internalNode
genLit (BoolL True) = genSmallIntConst 1
genLit (BoolL False) = genSmallIntConst 0
genLit (IntL sgn sz n) = genIntConst sgn sz n

genLit (FloatL S32 n) =
  let literal = CConst $ CFloatConst (readCFloat (show $ abs n)) internalNode
  in if n >= 0
     then literal
     else CUnary CMinOp literal internalNode

genVal :: GlobalVars -> Val -> CExpr
genVal gvars (VarV v)
  | v `Set.member` gvars =
      -- Take address of global variable; cast to pointer
      CCast pyonPointerType (CUnary CAdrOp var_exp internalNode) internalNode
  | otherwise = var_exp
  where
  var_exp = CVar (varIdent v) internalNode
      
genVal _ (LitV l) = genLit l

genVal _ _ = internalError "genVal: Unexpected value"

valPrimType v =
  case valType v
  of PrimType pt -> pt
     _ -> internalError "valPrimType"

genAssignVar :: Var -> CExpr -> CExpr
genAssignVar v e =
  CAssign CAssignOp (CVar (varIdent v) internalNode) e internalNode

genManyResults :: ReturnValues -> [CExpr] -> CBlockItems
genManyResults rtn exprs =
  case rtn
  of AssignValues [] -> return_nothing
     AssignValues [v] -> return_expr $ genAssignVar v expr
     AssignValues xs -> too_many xs
     DefineValues [] -> return_nothing
     DefineValues [v] ->
       [CBlockDecl $ declareVariable v $ Just expr]
     DefineValues xs -> too_many xs
     ReturnValues [] -> return_nothing
     ReturnValues [t] ->
       return_stm $ CReturn (Just expr) internalNode
     ReturnValues xs -> too_many xs
  where
    too_many xs =
      internalError $ "genManyResults: Cannot generate statement with " ++
      show (length xs) ++ " result values"
    expr = case exprs
           of [e] -> e
              _ -> internalError "genManyResults"
    return_nothing = []
    return_stm stm = [CBlockStmt stm]
    return_expr e = return_stm $ CExpr (Just e) internalNode

genOneResult :: ReturnValues -> CExpr -> CBlockItems
genOneResult rtn expr =
  case rtn
  of AssignValues [] -> return_expr expr
     AssignValues [v] -> return_expr $ genAssignVar v expr
     DefineValues [] -> return_expr expr
     DefineValues [v] ->
       [CBlockDecl $ declareVariable v $ Just expr]
     ReturnValues [] -> return_expr expr
     ReturnValues [t] -> 
       return_stm $ CReturn (Just expr) internalNode
  where
    return_stm stm = [CBlockStmt stm]
    return_expr e = return_stm $ CExpr (Just e) internalNode

-- | Generate a statement from an atom.  The function parameter uses
-- the translated expression to make a statement.
genAtom :: GlobalVars -> ReturnValues -> Atom -> CBlockItems
genAtom gvars returns atom =
  case atom
  of ValA vals -> genManyResults returns $ map (genVal gvars) vals
     PrimCallA op args ->
       genOneResult returns $ genCall gvars (returnTypes returns) op args
     PrimA op args ->
       genOneResult returns $ genPrimCall op $ map (genVal gvars) args
     SwitchA val [(c1, block1), (c2, block2)]
       | c1 == BoolL True && c2 == BoolL False ->
           genIf gvars returns val block1 block2
       | c1 == BoolL False && c2 == BoolL True ->
           genIf gvars returns val block2 block1
       | otherwise ->
           internalError "genStatement: Unexpected branching control flow"
     _ -> traceShow (pprAtom atom) $ internalError "genStatement: Unexpected atom"

genCall gvars return_types op args =
  let op' = genVal gvars op
      args' = map (genVal gvars) args
      
      -- Create the actual function type
      (return_specs, return_derived_declr) =
        case return_types
        of [] -> voidDeclSpecs
           [t] -> primTypeDeclSpecs t
           _ -> internalError "genCall: Cannot generate multiple return values"
      
      param_types = map (anonymousDecl . primTypeDeclSpecs . valPrimType) args
      fn_derived_declrs =
        CPtrDeclr [] internalNode :
        CFunDeclr (Right (param_types, False)) [] internalNode :
        return_derived_declr
      fn_declr = CDeclr Nothing fn_derived_declrs Nothing [] internalNode
      fn_type = CDecl return_specs [(Just fn_declr, Nothing, Nothing)] internalNode
      
      -- Cast operator to function pointer type
      cast = CCast fn_type op' internalNode
  in CCall cast args' internalNode

genPrimCall :: Prim -> [CExpr] -> CExpr
genPrimCall prim args =
  case prim
  of PrimCastZ from_sgn to_sgn sz ->
       let to_type = anonymousDecl $ primTypeDeclSpecs $ IntType to_sgn sz
       in case args
          of [arg] -> CCast to_type arg internalNode
     PrimAddZ _ _ -> binary CAddOp args
     PrimSubZ _ _ -> binary CSubOp args
     PrimMulZ _ _ -> binary CMulOp args
     PrimModZ Unsigned _ -> binary CRmdOp args -- Unsigned modulus operation
     PrimModZ Signed _ ->
       -- Emit a (floor) modulus operation using
       -- C's (to-zero) remainder operation
       --   (x % y) + ((x >= 0) == (y >= 0) ? 0 : y)
       case args
       of [x, y] ->
            let remainder = binary' CRmdOp x y
                correction =
                  CCond
                  (geZero x `equals` geZero y)
                  (Just zero) y internalNode
            in binary' CAddOp remainder correction
     PrimMaxZ _ _ ->
       case args
       of [x, y] -> CCond (binary' CGeqOp x y) (Just x) y internalNode
     PrimCmpZ _ _ CmpEQ -> binary CEqOp args
     PrimCmpZ _ _ CmpNE -> binary CNeqOp args
     PrimCmpZ _ _ CmpLT -> binary CLeOp args
     PrimCmpZ _ _ CmpLE -> binary CLeqOp args
     PrimCmpZ _ _ CmpGT -> binary CGrOp args
     PrimCmpZ _ _ CmpGE -> binary CGeqOp args
     PrimCmpP CmpEQ -> binary CEqOp args
     PrimCmpP CmpNE -> binary CNeqOp args
     PrimCmpP CmpLT -> binary CLeOp args
     PrimCmpP CmpLE -> binary CLeqOp args
     PrimCmpP CmpGT -> binary CGrOp args
     PrimCmpP CmpGE -> binary CGeqOp args
     PrimAnd -> binary CAndOp args
     PrimOr -> binary COrOp args
     PrimNot -> case args of [arg] -> CUnary CNegOp arg internalNode
     PrimAddP ->
       case args of [ptr, off] -> genOffset ptr off
     PrimLoad (PrimType ty) ->
       -- Cast the pointer to the desired pointer type, then dereference
       case args
       of [ptr, off] ->
            let offptr = genOffset ptr off
                cast_ptr = genCast ty offptr
            in CUnary CIndOp cast_ptr internalNode
     PrimStore (PrimType ty) ->
       -- Cast the pointer to the desired type, then assign to it
       case args
       of [ptr, off, val] ->
            let offptr = genOffset ptr off
                cast_ptr = genCast ty offptr
                lhs = CUnary CIndOp cast_ptr internalNode
            in CAssign CAssignOp lhs val internalNode
     PrimAAddZ sgn sz 
       | sz == nativeIntSize ->
           case args
           of [ptr, val] ->
                let add_fun = internalIdent "__sync_fetch_and_add"
                    cast_ptr = genCast (IntType sgn sz) ptr
                in CCall (CVar add_fun internalNode) [cast_ptr, val] internalNode
     PrimAddF _ -> binary CAddOp args
     PrimSubF _ -> binary CSubOp args
     PrimMulF _ -> binary CMulOp args
     PrimModF _ -> internalError "Not implemented: floating-point modulus"
     _ -> internalError $ 
          "Cannot generate C code for primitive operation: " ++
          show (pprPrim prim)
  where
    zero = genSmallIntConst 0
    geZero x = binary' CGeqOp x zero
    equals x y = binary' CEqOp x y
    binary' op x y = CBinary op x y internalNode
    binary op [x, y] = binary' op x y
    binary op _ = internalError "genPrimCall: Wrong number of arguments"

genStatement :: GlobalVars -> Stm -> CBlockItems

-- Don't generate this useless statemnt if it appears
genStatement gvars (LetE [] (ValA [])) = []

genStatement gvars (LetE params atom) =
  genAtom gvars (DefineValues params) atom
genStatement _ (LetrecE {}) = internalError "genStatement: Unexpected letrec"

genBlock :: GlobalVars -> ReturnValues -> Block -> CStat
genBlock gvars returns (Block stms atom) =
  let stmts = concat $ map (genStatement gvars) stms ++
              [genAtom gvars returns atom]
  in CCompound [] stmts internalNode

isEmptyBlock (CCompound [] [] _) = True
isEmptyBlock _ = False

-- | Generate an @if@ statement.
-- The output variables are declared before the statement, then assigned 
-- inside the statement.
genIf :: GlobalVars -> ReturnValues -> Val -> Block -> Block -> CBlockItems
genIf gvars returns scrutinee if_true if_false =
  let (returns', return_var_decls) =
        case returns
        of AssignValues vs -> (returns, [])
           DefineValues vs ->
             (AssignValues vs, map (CBlockDecl . declareUndefVariable) vs)
           ReturnValues vs -> (returns, [])
      true_path = genBlock gvars returns' if_true
      false_path = genBlock gvars returns' if_false
      false_branch = if isEmptyBlock false_path
                     then Nothing
                     else Just false_path
  in return_var_decls ++
     [CBlockStmt $
      CIf (genVal gvars scrutinee) true_path false_branch internalNode]

-- | Generate a forward declaration and definition of a function
genFun :: GlobalVars -> FunDef -> (CDecl, CFunDef)
genFun gvars (FunDef v fun) =
  let -- Function return type
      (return_type_specs, return_derived_declr) =
        case funReturnTypes fun
        of [] -> voidDeclSpecs
           [PrimType t] -> primTypeDeclSpecs t
           [_] -> internalError "genFun: Unexpected return type"
           _ -> internalError "genFun: Cannot generate multiple return values"
      -- Function parameter declarations
      param_decls = [declareVariable v Nothing | v <- funParams fun]
      -- Function declaration
      fun_declr =
        CFunDeclr (Right (param_decls, False)) [] internalNode
      derived_declr =
        fun_declr : return_derived_declr
      fun_decl =
        CDeclr (Just (varIdent v)) derived_declr Nothing [] internalNode

      -- Create the function body
      return_values = ReturnValues $ map valueToPrimType $ funReturnTypes fun
      body_stmt = genBlock gvars return_values $ funBody fun

      forward_declaration =
        CDecl return_type_specs [(Just fun_decl, Nothing, Nothing)] internalNode
      definition =
        CFunDef return_type_specs fun_decl [] body_stmt internalNode
  in if isPrimFun fun 
     then (forward_declaration, definition)
     else internalError "genFun: Can only generate primitive-call functions"

-- | Create a global static data definition and initialization code.
genData :: GlobalVars -> DataDef -> (CExtDecl, CStat)
genData gvars (DataDef v record_type values) =
  (CDeclExt $
   declareBytes v (recordSize record_type) (recordAlignment record_type),
   initializeBytes gvars v record_type values)

-- | Declare an external variable.  Its actual type is unimportant, since it
-- is cast to the appropriate type every time it is used.  Use an array type
-- so that (by C's semantics) references to the variable get its /address/ 
-- instead of its contents.
genImport :: ImportVar -> CDecl
genImport v =
  let return_type_specs =
        [CStorageSpec (CExtern internalNode),
         CTypeSpec $ CVoidType internalNode]
      pointer_decl =
        [CArrDeclr [] (CNoArrSize False) internalNode,
         CPtrDeclr [] internalNode]
      fun_decl = CDeclr (Just $ varIdent v) pointer_decl Nothing [] internalNode
  in CDecl return_type_specs [(Just fun_decl, Nothing, Nothing)] internalNode

initializeBytes gvars v record_type values =
  let base = CVar (varIdent v) internalNode 
      stmts =
        map mk_stmt $
        zipWith (initializeField gvars base) (recordFields record_type) values
  in CCompound [] stmts internalNode
  where
    mk_stmt e = CBlockStmt $ CExpr (Just e) internalNode

initializeField gvars base fld val =
  -- Generate the assignment *(TYPE *)(PYON_OFF(base, fld)) = val
  let field_offset = genSmallIntConst (fieldOffset fld)
      field_ptr = genOffset base field_offset
      field_cast_ptr = case fieldType fld
                       of PrimField t -> genCast t field_ptr
                          _ -> internalError "initializeField"
      lhs = CUnary CIndOp field_cast_ptr internalNode
      rhs = genVal gvars val
  in CAssign CAssignOp lhs rhs internalNode

-- | Create the module initialization function, which initializes the
-- module's global data.
initializationFunction :: [CStat] -> CFunDef
initializationFunction stmts =
  let return_type = CTypeSpec (CVoidType internalNode)
      static = CStorageSpec (CStatic internalNode)
      constructor_attr = CAttr (internalIdent "constructor") [] internalNode
      fun_declr =
        CFunDeclr (Right ([], False)) [constructor_attr] internalNode
      fun_decl = CDeclr (Just (internalIdent "initialize_module"))
                 [fun_declr] Nothing [] internalNode
      body = CCompound [] (map CBlockStmt stmts) internalNode
  in CFunDef [static, return_type] fun_decl [] body internalNode

generateCFile :: Module -> String
generateCFile (Module imports funs datas _) =
  let defined_vars =
        Set.fromList $ [f | FunDef f _ <- funs] ++
                       [v | DataDef v _ _ <- datas]
      global_vars = defined_vars `Set.union` Set.fromList imports
      
      -- Create an import declaration for symbols that are not defined in
      -- this module
      import_decls = map genImport $ filter (not . (`Set.member` defined_vars)) imports
      
      (data_defs, data_inits) = unzip $ map (genData global_vars) datas
      init_fun = initializationFunction data_inits
      (fun_decls, fun_defs) = unzip $ map (genFun global_vars) funs
      top_level = map CDeclExt import_decls ++
                  map CDeclExt fun_decls ++
                  data_defs ++
                  CFDefExt init_fun :
                  map CFDefExt fun_defs
      transl_module = CTranslUnit top_level internalNode
      
      module_body_text = show $ pretty transl_module
  in cModuleHeader ++ module_body_text
  
cModuleHeader =
  "#include <inttypes.h>\n\
  \#include <pyon.h>\n"
