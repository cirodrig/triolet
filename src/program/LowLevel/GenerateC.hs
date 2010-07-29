
module LowLevel.GenerateC(generateCFile)
where

import Control.Monad.Writer
import qualified Data.Set as Set
import Debug.Trace

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Pretty
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import Gluon.Common.Error
import Gluon.Common.Identifier(fromIdent)
import Gluon.Common.Label
import LowLevel.Builtins
import LowLevel.Types
import LowLevel.Record
import LowLevel.Syntax
import LowLevel.Print

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

varPrimType v = valueToPrimType $ varType v

-- | Generate the C name for a variable.
-- If it's a builtin variable, or if it's an exported
-- variable, then use the name alone.  Otherwise, generate a unique name
-- using the variable's name and ID.
varIdent :: Var -> Ident
varIdent v 
  -- If it's a builtin variable, use the label
  | Just var_name <- varName v,
    moduleOf var_name == builtinModuleName =
      internalIdent $ showLabel var_name
  -- Otherwise, generate a unique naem
  | otherwise =
      let leader =
            case varName v
            of Just nm ->  '_' : (showLabel nm ++ "_")
               Nothing -> type_leader $ varPrimType v
          name = leader ++ show (fromIdent $ varID v)
      in internalIdent name
  where
    type_leader PointerType = "v_"
    type_leader BoolType = "b_"
    type_leader (IntType Signed _) = "i_"
    type_leader (IntType Unsigned _) = "u_"
    type_leader (FloatType _) = "f_"
    type_leader _ = internalError "varIdent: Unexpected type"


-- | Get the type specificer for a non-pointer primitive type
typeSpec :: PrimType -> CTypeSpec
typeSpec pt = 
  case pt
  of BoolType -> CIntType internalNode
     IntType Signed S8 -> type_def "int8_t"
     IntType Signed S16 -> type_def "int16_t"
     IntType Signed S32 -> type_def "int32_t"
     IntType Signed S64 -> type_def "int64_t"
     IntType Unsigned S8 -> type_def "uint8_t"
     IntType Unsigned S16 -> type_def "uint16_t"
     IntType Unsigned S32 -> type_def "uint32_t"
     IntType Unsigned S64 -> type_def "uint64_t"
     FloatType S32 -> CFloatType internalNode
     FloatType S64 -> CDoubleType internalNode
  where
    type_def name = CTypeDef (internalIdent name) internalNode

-- | Get the declaration components to use to declare a variable or a
-- function return type
declspecs :: PrimType -> ([CDeclSpec], [CDerivedDeclr])
declspecs PointerType =
  ([CTypeSpec (CCharType internalNode)], [CPtrDeclr [] internalNode])
declspecs t =
  ([CTypeSpec $ typeSpec t], [])

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
  let (type_specs, derived_declr) = declspecs $ varPrimType v
      declr = CDeclr (Just $ varIdent v) derived_declr Nothing [] internalNode
      init = case initializer
             of Nothing -> Nothing
                Just e  -> Just $ CInitExpr e internalNode
  in CDecl type_specs [(Just declr, init, Nothing)] internalNode

declareUndefVariable :: Var -> CDecl
declareUndefVariable v = declareVariable v Nothing

-- | Generate an abstract declarator, used in type casting 
abstractDeclr :: PrimType -> CDecl
abstractDeclr ty =
  let (type_specs, derived_declr) = declspecs ty
      declr = CDeclr Nothing derived_declr Nothing [] internalNode
  in CDecl type_specs [(Just declr, Nothing, Nothing)] internalNode

-- | Generate an abstract declarator for a pointer to the specified type,
-- used in type casting 
abstractPtrDeclr :: PrimType -> CDecl
abstractPtrDeclr ty =
  let (type_specs, derived_declr) = declspecs ty
      declr = CDeclr Nothing (derived_declr ++ [CPtrDeclr [] internalNode]) Nothing [] internalNode
  in CDecl type_specs [(Just declr, Nothing, Nothing)] internalNode

charPointerType :: CDecl
charPointerType =
  let type_specs = [CTypeSpec (CCharType internalNode)]
      declr = CDeclr Nothing [CPtrDeclr [] internalNode] Nothing [] internalNode
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
  CCast (abstractPtrDeclr to_type) expr internalNode

genLit :: Lit -> CExpr
genLit NullL = genSmallIntConst 0
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
      -- Take address of global variable; cast to character pointer
      CCast charPointerType (CUnary CAdrOp var_exp internalNode) internalNode
  | otherwise = var_exp
  where
  var_exp = CVar (varIdent v) internalNode
      
genVal _ (LitV l) = genLit l

genVal _ _ = internalError "genVal: Unexpected value"

valType :: Val -> PrimType
valType (VarV v) = varPrimType v
valType (LitV l) = litType l
valType _ = internalError "valType: Unexpected value"

genAssignVar :: Var -> CExpr -> CExpr
genAssignVar v e =
  CAssign CAssignOp (CVar (varIdent v) internalNode) e internalNode

genManyResults :: ReturnValues -> [CExpr] -> CBlockItems
genManyResults rtn exprs =
  case rtn
  of AssignValues [] -> return_nothing
     AssignValues [v] -> return_expr $ genAssignVar v expr
     DefineValues [] -> return_nothing
     DefineValues [v] ->
       [CBlockDecl $ declareVariable v $ Just expr]
     ReturnValues [] -> return_nothing
     ReturnValues [t] ->
       return_stm $ CReturn (Just expr) internalNode
  where
    expr = case exprs of [e] -> e
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
        of [] -> ([CTypeSpec (CVoidType internalNode)], [])
           [t] -> declspecs t 
           _ -> internalError "genCall: Cannot generate multiple return values"
      
      param_types = map abstractDeclr $ map valType args
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
  of PrimAddZ _ _ -> binary CAddOp args
     PrimSubZ _ _ -> binary CSubOp args
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
     PrimAddP ->
       -- The argument is already a (char *)
       -- Add the desired byte offset
       binary CAddOp args
     PrimLoad (PrimType ty) ->
       -- Cast the pointer to the desired pointer type, then dereference
       case args
       of [ptr] ->
            let cast_ptr = genCast ty ptr
            in CUnary CIndOp cast_ptr internalNode
     PrimStore (PrimType ty) ->
       -- Cast the pointer to the desired type, then assign to it
       case args
       of [ptr, val] ->
            let cast_ptr = genCast ty ptr
                lhs = CUnary CIndOp cast_ptr internalNode
            in CAssign CAssignOp lhs val internalNode
     PrimAAddZ sgn sz 
       | sz == nativeIntSize ->
           case args
           of [ptr, val] ->
                let add_fun = case sgn
                              of Signed   -> internalIdent "pyon_atomic_add_s"
                                 Unsigned -> internalIdent "pyon_atomic_add_u"
                    cast_ptr = genCast (IntType sgn sz) ptr
                in CCall (CVar add_fun internalNode) [cast_ptr, val] internalNode
     PrimAddF _ -> binary CAddOp args
     PrimSubF _ -> binary CSubOp args
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
        of [] -> ([CTypeSpec (CVoidType internalNode)], []) 
           [PrimType t] -> declspecs t
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

initializeBytes gvars v record_type values =
  let stmts =
        map mk_stmt $
        zipWith (initializeField gvars v) (recordFields record_type) values
  in CCompound [] stmts internalNode
  where
    mk_stmt e = CBlockStmt $ CExpr (Just e) internalNode

initializeField gvars v fld val =
  -- Generate the assignment *(TYPE *)(v + fld) = val
  let field_offset = genSmallIntConst (fieldOffset fld)
      base_ptr = genCast PointerType $
                 CUnary CAdrOp (CVar (varIdent v) internalNode) internalNode
      field_ptr = CBinary CAddOp base_ptr field_offset internalNode
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
      fun_declr =
        CFunDeclr (Right ([], False)) [] internalNode
      fun_decl = CDeclr (Just (internalIdent "initialize_module"))
                 [fun_declr] Nothing [] internalNode
      body = CCompound [] (map CBlockStmt stmts) internalNode
  in CFunDef [return_type] fun_decl [] body internalNode

generateCFile :: Module -> String
generateCFile (Module funs datas) =
  let global_vars =
        Set.fromList $ [f | FunDef f _ <- funs] ++
                       [v | DataDef v _ _ <- datas] ++
                       allBuiltins
      
      (data_defs, data_inits) = unzip $ map (genData global_vars) datas
      init_fun = initializationFunction data_inits
      (fun_decls, fun_defs) = unzip $ map (genFun global_vars) funs
      top_level = map CDeclExt fun_decls ++
                  data_defs ++
                  CFDefExt init_fun :
                  map CFDefExt fun_defs
      transl_module = CTranslUnit top_level internalNode
      
      module_body_text = show $ pretty transl_module
  in cModuleHeader ++ module_body_text
  
cModuleHeader =
  "#include <inttypes.h>\n\
  \#include <pyon.h>\n"
