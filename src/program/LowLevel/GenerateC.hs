
{-# LANGUAGE ViewPatterns, FlexibleInstances #-}
module LowLevel.GenerateC(generateCFile)
where

import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.Set as Set
import qualified Data.Map as Map
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Language.C.Data.Ident
import Language.C.Data.Node
import Language.C.Pretty
import Language.C.Syntax.AST
import Language.C.Syntax.Constants

import Common.Error
import qualified Common.Identifier
import Common.Identifier(fromIdent, IdentSupply)
import Common.Label
import Common.Supply
import LowLevel.Builtins
import LowLevel.CodeTypes
import LowLevel.Syntax
import LowLevel.Print
import LowLevel.GenerateCUtils
import LowLevel.GenerateCCode
import Globals

data CodeItem =
    CCode [CBlockItem]
  | Group LocalFunctionGroup

type Code = [CodeItem]

-- | The C code translation of a local function.  Local functions become
-- contiguous sequences of statements; they are entered with \"goto\".
data LocalFunction =
  LocalFunction
  { -- | The function's entry point is labeled
    lfunLabel :: !Ident
    -- | Local function parameter variables
  , lfunParamVars :: [Ident]
    -- | Local function parameters are function-scope variables
  , lfunParameters :: [CDecl]
    -- | The function's body is some code, possibly with its own local
    -- functions
  , lfunBody :: Code
    -- | The function may have a fallthrough path
  , lfunFallsThrough :: Bool
  }

-- | A local function group consists of an entry point and some local
--   functions.
data LocalFunctionGroup =
  LocalFunctionGroup
  { lfgLabel :: !Ident
  , lfgEntry :: Code
  , lfgGroup :: [LocalFunction]
  , lfgFallsThrough :: Bool
  }

-- | The set of global variables.  Global variables are bound by a 'FunDef' or
-- 'DataDef' or defined in another compilation unit.  When referencing a
-- global variable, we need to take its address.
type GlobalVars = Set.Set Var

-- | Local functions.  This is used to look up labels and parameters, in order
--   to generate function calls.
type LocalFunctionMap = Map.Map Var LocalFunction

newNameSupply :: IO (Supply Int)
newNameSupply = newSupply 1 (1+)

-- | Structure names, used for functions with multiple return values.
type Structs = Map.Map [PrimType] Ident

data Env = Env
           { globalVars :: GlobalVars 
           , localFunctions :: LocalFunctionMap 
           , nameSupply :: {-# UNPACK #-}!(Supply Int)
           , varIDSupply :: {-# UNPACK #-}!(IdentSupply Var)
           }

newtype GenC a = GenC {runGenC :: Env -> Structs -> IO (a, Structs)}

instance Functor GenC where
  fmap f m = GenC $ \env st -> do (x, st') <- runGenC m env st
                                  return (f x, st')

instance Monad GenC where
  return x = GenC $ \_ st -> return (x, st)
  m >>= k = GenC $ \env st -> do (x, st') <- runGenC m env st
                                 runGenC (k x) env st'

instance MonadFix GenC where
  mfix f = GenC $ \env st -> mfix $ \ ~(x, st') -> runGenC (f x) env st 

instance Supplies GenC (Common.Identifier.Ident Var) where
  fresh = GenC $ \env st -> do n <- supplyValue (varIDSupply env)
                               return (n, st)

newName :: (Int -> String) -> GenC Ident
newName to_string = GenC $ \env st -> do
  n <- supplyValue (nameSupply env)
  return (internalIdent $ to_string n, st)

newAnonymousLabel :: GenC Ident
newAnonymousLabel = newName (\n -> "c_" ++ show n)

newAnonymousStructName :: GenC Ident
newAnonymousStructName = newName (\n -> "struct_" ++ show n)

getGlobalVars :: GenC GlobalVars
getGlobalVars = GenC $ \env st -> return (globalVars env, st)

withLocalFunctions :: [(Var, LocalFunction)] -> GenC a -> GenC a
withLocalFunctions local_fs m = GenC $ \env st ->
  let env' = env {localFunctions = 
                     foldr (uncurry Map.insert) (localFunctions env) local_fs}
  in runGenC m env' st      

lookupLocalFunction :: Var -> GenC (Maybe LocalFunction)
lookupLocalFunction v = GenC $ \env st ->
  return (Map.lookup v (localFunctions env), st)

-- | Get the name of the structure type used to encode the given sequence 
--   of values.  An existing structure is returned if found, otherwise a
--   new one is created.
getStructName :: [PrimType] -> GenC Ident
getStructName types = GenC $ \env st ->
  case Map.lookup types st
  of Just idt -> return (idt, st)
     Nothing  -> do (idt, st') <- runGenC newAnonymousStructName env st
                    return (idt, Map.insert types idt st') 

-------------------------------------------------------------------------------
-- Declarations

valueTypeDeclSpecs :: ValueType -> GenC DeclSpecs
valueTypeDeclSpecs (PrimType pt) = return $ primTypeDeclSpecs pt
valueTypeDeclSpecs (RecordType r) =
  fmap identDeclSpecs $ getStructName field_types
  where
    field_types = map field_prim_type $ recordFields r
                 
    field_prim_type fld =
      case fieldType fld
      of PrimField pt -> pt
         _ -> internalError "declareLocalVariable"

-- | Declare a structure type with the given name and field types.
--   The structure is declared as a typedef, so it can be referred to by the
--   name.
declareStruct :: Ident -> [DeclSpecs] -> CDecl
declareStruct name fields =
  let type_specs = typedefDeclSpecs $ structDeclSpecs fields
  in namedDecl type_specs name

-- | Declare or define a variable.  The variable is not global and
--   is not accessed by reference.  It must not have record type.
declareLocalVariable :: Var -> Maybe CExpr -> GenC CDecl
declareLocalVariable v initializer = do
  declspecs <- valueTypeDeclSpecs (varType v)
  return $ declareVariable (localVarIdent v) declspecs initializer

-- | Declare a local variable with no initial value.
declareUndefLocalVariable :: Var -> GenC CDecl
declareUndefLocalVariable v = declareLocalVariable v Nothing


-------------------------------------------------------------------------------
-- Non-recursive expressions

genLit :: Lit -> CExpr
genLit NullL           = nullPtr
genLit NullRefL        = nullPtr
genLit UnitL           = smallIntConst 0
genLit (BoolL True)    = smallIntConst 1
genLit (BoolL False)   = smallIntConst 0
genLit (IntL sgn sz n) = intConst sgn sz n
genLit (FloatL S32 n)  = floatConst S32 n

genVal :: Val -> GenC CExpr
genVal val = do gvars <- getGlobalVars
                return $ genValWorker gvars val

genVals :: [Val] -> GenC [CExpr]
genVals vals = do gvars <- getGlobalVars
                  return $ map (genValWorker gvars) vals

genValWorker :: GlobalVars -> Val -> CExpr
genValWorker gvars (VarV v)
  | v `Set.member` gvars =
      -- Take address of global variable, and cast to pointer
      castToPyonPtr $ cUnary CAdrOp var_exp
  | otherwise = var_exp
  where
  var_exp = cVar $ varIdentScoped gvars v
      
genValWorker _ (LitV l) = genLit l

genValWorker _ _ = internalError "genVal: Unexpected value"

valPrimType v =
  case valType v
  of PrimType pt -> pt
     _ -> internalError "valPrimType"

genAssignVar :: Var -> CExpr -> CExpr
genAssignVar v e = cAssign (CVar (localVarIdent v) internalNode) e

-- | Get the C type used for this return type.
returnTypeDecl :: [PrimType] -> GenC DeclSpecs
returnTypeDecl []  = return voidDeclSpecs
returnTypeDecl [t] = return $ primTypeDeclSpecs t
returnTypeDecl ts  = fmap identDeclSpecs $ getStructName ts

-------------------------------------------------------------------------------
-- Atoms and statements

-- | How an atom's results should be dispatched.
data ReturnValues =
    -- | Assign the results to the given (pre-existing) variables
    AssignValues [ParamVar]
    -- | Define these variables and assign to them
  | DefineValues [ParamVar]
    -- | Return the results at the given types
  | ReturnValues [ValueType]

returnTypes :: ReturnValues -> [ValueType]
returnTypes (AssignValues vs) = map varType vs
returnTypes (DefineValues vs) = map varType vs
returnTypes (ReturnValues ps) = ps

genManyResults :: ReturnValues -> [CExpr] -> GenC [CBlockItem]
genManyResults rtn exprs =
  case rtn
  of AssignValues xs  -> return_exprs $ zipWith genAssignVar xs exprs
     DefineValues xs  -> zipWithM declare_variable xs exprs
     ReturnValues []  -> return_nothing
     ReturnValues [t] -> expr `seq` return_stm (cReturn $ Just expr)
     ReturnValues xs  -> do
       struct_name <- getStructName $ map valueToPrimType xs
       let struct_decl = anonymousDecl $ identDeclSpecs struct_name
           compound_expr = cCompoundLit struct_decl $ cInitExprs exprs
       return_stm $ cReturn (Just compound_expr)
  where
    expr = case exprs
           of [e] -> e
              _ -> internalError "genManyResults"
    return_nothing = return []
    return_stm stm = return [CBlockStmt stm]
    return_expr e = return_stm $ cExprStat e
    return_exprs es = return $ map (CBlockStmt . cExprStat) es
    declare_variable v e = do 
      decl <- declareLocalVariable v $ Just e
      return (CBlockDecl decl)

-- | Put an expression's results in the appropriate place.  The expression   
--   returns a single value, or void.  If there's more than one result, it's
--   returned as a structure.
genOneResult :: ReturnValues -> CExpr -> GenC [CBlockItem]
genOneResult rtn expr =
  case rtn
  of AssignValues [] -> return_expr expr
     AssignValues [v] -> return_expr $ genAssignVar v expr
     AssignValues vs -> do
       (tmp_assignment, tmpvar) <- assign_temporary vs
       let assignments = unpack_and_assign tmpvar vs
       return (tmp_assignment : assignments)
     DefineValues [] -> return_expr expr
     DefineValues [v] -> do
       decl <- declare_variable v expr
       return [decl]
     DefineValues vs -> do
       (tmp_assignment, tmpvar) <- assign_temporary vs
       assignments <- unpack_and_define tmpvar vs
       return (tmp_assignment : assignments)
     ReturnValues [] -> return_expr expr
     ReturnValues _ ->
       -- Return the expression's result. 
       -- If there are many values packed in a struct, they stay that way.
       return_stm $ CReturn (Just expr) internalNode
  where
    return_stm stm = return [CBlockStmt stm]
    return_expr e = return_stm $ CExpr (Just e) internalNode
    
    declare_variable v e = do 
      decl <- declareLocalVariable v $ Just e
      return (CBlockDecl decl)

    -- Assign the expression's result to a temporary structure.
    -- Use 'vs' to determine the structure's C type.
    assign_temporary vs = do
      let prim_types = map varPrimType vs
          var_type = RecordType $ constStaticRecord (map PrimField prim_types)
      v <- newAnonymousVar var_type
      typespecs <- fmap identDeclSpecs $ getStructName prim_types
      let tmp_assignment =
            declareVariable (localVarIdent v) typespecs $ Just expr
      return (CBlockDecl tmp_assignment, v)

    -- Unpack the fields of the source variable and define the destination
    -- variables
    unpack_and_define source_var vs =
      zipWithM define_value vs (map (internalIdent . return) ['a' .. 'z'])
      where
        source_expr = cVar (localVarIdent source_var)
        define_value v field_name =
          let field_expr = CMember source_expr field_name False internalNode
          in declare_variable v field_expr

    -- Unpack the fields of the source variable and assign the destinations
    unpack_and_assign source_var vs =
      zipWith assign_value vs (map (internalIdent . return) ['a' .. 'z'])
      where
        source_expr = cVar (localVarIdent source_var)
        assign_value v field_name =
          let field_expr = CMember source_expr field_name False internalNode
              dst_expr = cVar (localVarIdent v)
          in CBlockStmt $ cExprStat $ cAssign dst_expr field_expr

-- | Generate a statement from an atom.  It must not be a call to a local
-- function.
genNonTailAtom :: ReturnValues -> Atom -> GenC [CBlockItem]
genNonTailAtom returns atom = do
  (code, b) <- genAtom returns atom
  if b
    then return code
    else internalError "genNonTailAtom: Invalid call in non-tail position"

-- | Generate a statement from an atom.  The function parameter uses
-- the translated expression to make a statement.
-- Also return True if the atom is not a call to a local function.
genAtom :: ReturnValues -> Atom -> GenC ([CBlockItem], Bool)
genAtom returns atom =
  case atom
  of ValA vals -> do
       vals' <- genVals vals
       code <- genManyResults returns vals'
       return (code, True)

     CallA PrimCall op args -> do
       call <- genCall (returnTypes returns) op args
       case call of
         Left items -> return (items, False)
         Right call -> do result <- genOneResult returns call
                          return (result, True)
     PrimA op args -> do
       args' <- genVals args
       result <- genOneResult returns $ genPrimCall op args'
       return (result, True)

     UnpackA _ arg -> do
       result <- genOneResult returns =<< genVal arg
       return (result, True)
     _ -> internalError "genAtom: Unexpected atom"

-- | Create a function call expression.  The call is either generated as a
-- sequence of assignments followed by a @goto@ or a C function call.
genCall :: [ValueType] 
        -> Val 
        -> [Val] 
        -> GenC (Either [CBlockItem] CExpr)
genCall return_types op args =
  -- If calling a local function, generate a goto call
  case op
  of VarV v -> do
       lfun <- lookupLocalFunction v
       case lfun of
         Nothing -> fmap Right gen_c_call
         Just f  -> fmap Left $ gen_goto_call f
     _ -> fmap Right gen_c_call
  where
    gen_goto_call lfun = do
      -- Generate a local function "call".  Jump to the function. 
      -- Assign parameter variables
      args' <- genVals args
      let assignments = zipWith make_assignment (lfunParamVars lfun) args'
            where
              make_assignment ident expr =
                cExprStat $ cAssign (cVar ident) expr

          statements = map CBlockStmt $
                       assignments ++ [cGoto $ lfunLabel lfun]
      return statements

    gen_c_call = do
      -- Generate an ordinary function call.
      op' <- genVal op
      args' <- genVals args
      
      -- Create the actual function type
      return_type <- returnTypeDecl $ map valueToPrimType return_types

      let param_types =
            map (anonymousDecl . primTypeDeclSpecs . valPrimType) args
          fn_type =
            ptrDeclSpecs $ funDeclSpecs param_types return_type

          -- Cast operator to function pointer type
          cast = CCast (anonymousDecl fn_type) op' internalNode
      return $ cCall cast args'

genPrimCall :: Prim -> [CExpr] -> CExpr
genPrimCall prim args =
  case prim
  of PrimCastZ from_sgn to_sgn sz ->
       case args of [arg] -> cCast (IntType to_sgn sz) arg
     PrimExtendZ sgn from_sz to_sz ->
       case args of [arg] -> cCast (IntType sgn to_sz) arg       
     PrimAddZ _ _ -> binary CAddOp args
     PrimSubZ _ _ -> binary CSubOp args
     PrimMulZ _ _ -> binary CMulOp args
     PrimModZ Unsigned _ -> binary CRmdOp args -- Unsigned modulus operation
     PrimModZ Signed _ -> integer_modulus args
     PrimDivZ Unsigned _ -> binary CDivOp args -- Unsigned division operation
     PrimDivZ Signed _ -> integer_div args
     PrimMaxZ _ _ ->
       case args
       of [x, y] -> cCond (binary' CGeqOp x y) x y
     PrimMinZ _ _ ->
       case args
       of [x, y] -> cCond (binary' CLeOp x y) x y
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
     PrimSelect _ ->
       case args of [b, x, y] -> cCond b x y
     PrimAnd -> binary CLndOp args
     PrimOr -> binary CLorOp args
     PrimNot -> case args of [arg] -> CUnary CNegOp arg internalNode
     PrimAddP ->
       case args of [ptr, off] -> offset ptr off
     PrimLoad _ (PrimType ty) ->
       -- Cast the pointer to the desired pointer type, then dereference
       case args
       of [ptr, off] ->
            let offptr = offset ptr off
                cast_ptr = cPtrCast ty offptr
            in CUnary CIndOp cast_ptr internalNode
     PrimStore _ (PrimType ty) ->
       -- Cast the pointer to the desired type, then assign to it
       case args
       of [ptr, off, val] ->
            let offptr = offset ptr off
                cast_ptr = cPtrCast ty offptr
                lhs = CUnary CIndOp cast_ptr internalNode
            in CAssign CAssignOp lhs val internalNode
     PrimAAddZ sgn sz 
       | sz == nativeIntSize ->
           case args
           of [ptr, val] ->
                let add_fun = internalIdent "__sync_fetch_and_add"
                    cast_ptr = cPtrCast (IntType sgn sz) ptr
                in CCall (CVar add_fun internalNode) [cast_ptr, val] internalNode
     PrimCastZToF from_size to_size ->
       case args
       of [val] ->
            let decl = anonymousDecl $ primTypeDeclSpecs (FloatType to_size) 
            in CCast decl val internalNode
     PrimCastFToZ from_size to_size ->
       case args
       of [val] ->
            let decl = anonymousDecl $ primTypeDeclSpecs (IntType Signed to_size) 
            in CCast decl val internalNode
     PrimGetFrameP ->
       CVar (internalIdent "frame_ptr") internalNode
     PrimCmpF _ CmpEQ -> binary CEqOp args
     PrimCmpF _ CmpNE -> binary CNeqOp args
     PrimCmpF _ CmpLT -> binary CLeOp args
     PrimCmpF _ CmpLE -> binary CLeqOp args
     PrimCmpF _ CmpGT -> binary CGrOp args
     PrimCmpF _ CmpGE -> binary CGeqOp args
     PrimAddF _ -> binary CAddOp args
     PrimSubF _ -> binary CSubOp args
     PrimMulF _ -> binary CMulOp args
     PrimModF _ -> float_modulus args
     PrimDivF _ -> binary CDivOp args
     PrimRoundF mode fp_sz sgn sz ->
       let round_op_name =
             case mode
             of Floor -> case fp_sz 
                         of S32 -> "floorf"
                            S64 -> "floor"
                Ceiling -> case fp_sz 
                           of S32 -> "ceilf"
                              S64 -> "ceil"
                Truncate -> case fp_sz 
                            of S32 -> "truncf"
                               S64 -> "trunc"
                Nearest -> case fp_sz 
                           of S32 -> "roundf"
                              S64 -> "round"
           round_op = internalIdent round_op_name
           [arg] = args
       in cCast (IntType sgn sz) $ cCall (cVar round_op) [arg]
     PrimPowF sz ->
       let op = case sz
                of S32 -> internalIdent "powf"
                   S64 -> internalIdent "pow"
           [x, y] = args
       in cCall (cVar op) [x, y]
     PrimUnaryF intrinsic fp_sz ->
       let op_name =
             case intrinsic
             of ExpI -> case fp_sz
                        of S32 -> "expf"
                           S64 -> "exp"
                LogI -> case fp_sz
                        of S32 -> "logf"
                           S64 -> "log"
                SqrtI -> case fp_sz
                         of S32 -> "sqrtf"
                            S64 -> "sqrt"
                SinI -> case fp_sz
                        of S32 -> "sinf"
                           S64 -> "sin"
                CosI -> case fp_sz
                        of S32 -> "cosf"
                           S64 -> "cos"
                TanI -> case fp_sz
                        of S32 -> "tanf"
                           S64 -> "tan"
           op = internalIdent op_name
           [arg] = args
       in cCall (cVar op) [arg]
     _ -> internalError $ 
          "Cannot generate C code for primitive operation: " ++
          show (pprPrim prim)
  where
    zero = smallIntConst 0
    geZero x = binary' CGeqOp x zero
    ltZero x = binary' CLeOp x zero
    add x y = binary' CAddOp x y
    neg x = cUnary CMinOp x
    equals x y = binary' CEqOp x y
    binary' op x y = cBinary op x y
    binary op [x, y] = binary' op x y
    binary op _ = internalError "genPrimCall: Wrong number of arguments"
    
    float_modulus [x, y] =
      -- x mod y = x - y * floor(x / y)
      let div_op = binary' CDivOp x y
          floor_op = cCall (cVar (internalIdent "floor")) [div_op]
          mul_op = binary' CMulOp y floor_op
          sub_op = binary' CSubOp x mul_op
      in sub_op

    integer_modulus [x, y] =
      -- Emit a (floor) modulus operation using
      -- C's (to-zero) remainder operation
      -- >  x % y == 0 ? 0 :
      -- >    (y >= 0 ? x % y      + (x < 0 ? y : 0)
      -- >            : -(-x % -y) + (x < 0 ? 0 : -y))
      let remainder = binary' CRmdOp x y
          zero_check = equals remainder zero
          pos_rem = add remainder $ cCond (ltZero x) y zero
          neg_rem = add (neg (binary' CRmdOp (neg x) (neg y))) $
                    cCond (ltZero x) zero (neg y)
      in cCond zero_check zero $ cCond (geZero y) pos_rem neg_rem

    integer_div [x, y] =
      -- Floor division using C's round-to-zero division
      -- >  (x >= 0) == (y >= 0) || x % y == 0 ? x / y : x / y - 1
      let remainder = binary' CRmdOp x y
          zero_check = equals remainder zero
          same_sign = geZero x `equals` geZero y
          test = binary' CLorOp same_sign zero_check
          frac = binary' CDivOp x y
          adjusted_frac = binary' CSubOp frac (smallIntConst 1)
      in cCond test frac adjusted_frac

-------------------------------------------------------------------------------
-- Statements

-- | Create C code from one statement.  Also return True if the statement
-- can fall through (as opposed to making a tail call).
genStatement :: ReturnValues -> Stm -> GenC (Code, Bool)
genStatement returns stm =
  case stm
  of LetE [] (ValA []) stm' -> 
       genStatement returns stm' -- Useless statement
     LetE params atom stm' -> do
       block_items <- genNonTailAtom (DefineValues params) atom
       (code, fallthrough) <- genStatement returns stm'
       return (CCode block_items : code, fallthrough)
     LetrecE funs stm' ->
       genLocalFunctions returns (groupMembers funs) $ \localfs -> do
         label <- newAnonymousLabel
         (code, fallthrough) <- genStatement returns stm'
         return ([Group $ LocalFunctionGroup label code localfs fallthrough],
                 fallthrough)
     SwitchE cond [(c1, block1), (c2, block2)]
       | c1 == BoolL True && c2 == BoolL False ->
         genIf returns cond block1 block2
       | c1 == BoolL False && c2 == BoolL True ->
         genIf returns cond block2 block1
     SwitchE cond cases ->
       genSwitch returns cond cases
     ReturnE atom -> do
       (block_items, fallthrough) <- genAtom returns atom
       return ([CCode block_items], fallthrough)

genSwitch returns cond cases = do
  cond_exp <- genVal cond
  case_codes1 <- mapM (mk_case False) (init cases)
  last_case_code <- mk_case True (last cases)

  let switch_statements = map fst (case_codes1 ++ [last_case_code])
      fallthrough = any snd (case_codes1 ++ [last_case_code])
      switch_body = cCompoundStat switch_statements
      switch = CSwitch cond_exp switch_body internalNode
  return ([CCode [CBlockStmt switch]], fallthrough)
  where
    -- Create a switch case.
    -- > case TAG: { code; break; }
    -- or
    -- > default: { code; }
    mk_case :: Bool -> Alt -> GenC (CBlockItem, Bool)
    mk_case is_last (tag, stm) = do
      (code, fallthrough) <- genStatement returns stm
      stmtss <- mapM codeItemStatements code
      let case_code =
            if is_last
            then CDefault (cCompoundStat (concat stmtss)) internalNode
            else CCase (genLit tag) (cCompoundStat (concat stmtss ++ [CBlockStmt $ CBreak internalNode])) internalNode
      return (CBlockStmt case_code, fallthrough)
{-
genStatement gvars (LetE params atom) =
  genAtom gvars (DefineValues params) atom
genStatement _ (LetrecE {}) = internalError "genStatement: Unexpected letrec"

genBlock :: GlobalVars -> ReturnValues -> Block -> CStat
genBlock gvars returns (Block stms atom) =
  let stmts = concat $ map (genStatement gvars) stms ++
              [genAtom gvars returns atom]
  in CCompound [] stmts internalNode-}

isEmptyBlock (CCompound [] [] _) = True
isEmptyBlock _ = False

-- | Generate an @if@ statement.
-- The output variables are declared before the statement, then assigned 
-- inside the statement.
genIf :: ReturnValues -> Val -> Stm -> Stm -> GenC (Code, Bool)
genIf returns scrutinee if_true if_false = do
  (returns', return_var_decls) <-
    case returns
    of AssignValues vs -> return (returns, [])
       DefineValues vs -> do
         decls <- mapM declareUndefLocalVariable vs
         return (AssignValues vs, map CBlockDecl decls)
       ReturnValues vs -> return (returns, [])

  (true_path, true_fallthrough) <- makeBlock =<< genStatement returns' if_true
  (false_path, false_fallthrough) <- makeBlock =<< genStatement returns' if_false
  let false_branch = if isEmptyBlock false_path
                     then Nothing
                     else Just false_path

  cond_expr <- genVal scrutinee
  let if_stmt = CCode $
                return_var_decls ++
                [CBlockStmt $ CIf cond_expr true_path false_branch internalNode]
  return ([if_stmt], true_fallthrough || false_fallthrough)


genLocalFunctions :: ReturnValues -> [FunDef]
                  -> ([LocalFunction] -> GenC a) -> GenC a
genLocalFunctions returns fs m = do
  local_functions <- mfix $ \local_functions ->
    add_to_env local_functions $ mapM (genLocalFunction returns) fs
  
  add_to_env local_functions $ m local_functions
  where
    -- Add the functions to the environment.  Uses 'local_functions' lazily.
    add_to_env :: [LocalFunction] -> GenC b -> GenC b
    add_to_env local_functions =
      withLocalFunctions (lazy_zip fun_names local_functions)
      
    fun_names = map definiendum fs
    
    -- Like 'zip', but lazy in the second parameter.
    lazy_zip (f:fs) ~(lf:lfs) = (f,lf) : lazy_zip fs lfs
    lazy_zip [] _ = []

-- | Generate code for a locally defined function.  The assignment destinations
-- on the fall-through path are given as extra parameters.  They are only
-- assigned if the function falls through.
genLocalFunction :: ReturnValues -> FunDef -> GenC LocalFunction
genLocalFunction returns (Def v f)
  | not (isPrimFun f) =
      internalError "genLocalFunction: Not a primitive-call function"
  | otherwise = do
      let fun_name = localVarIdent v
      param_decls <- mapM declareUndefLocalVariable $ funParams f
      (body, ft) <- genStatement returns (funBody f)
      return $ LocalFunction { lfunLabel = fun_name
                             , lfunParamVars = map localVarIdent $ funParams f
                             , lfunParameters = param_decls
                             , lfunBody = body
                             , lfunFallsThrough = ft
                             }

makeBlock :: (Code, Bool) -> GenC (CStat, Bool)
makeBlock (code, is_tail) = do
  statements <- make_statement code
  return (statements, is_tail) 
  where 
    make_statement code = do
      statements <- mapM codeItemStatements code
      return $ cCompoundStat (concat statements)

codeItemStatements :: CodeItem -> GenC [CBlockItem]
codeItemStatements (CCode items) = return items
codeItemStatements (Group lfg)   = fmap return $ makeFunctionGroupCode lfg

-- | Create the code of a function group.  The following sequence of things
-- is produced:
--
-- 1. Function parameter variables
--
-- 2. Entry code
--
-- 3. Functions
--
-- 4. Fallthrough statement
--
-- The fallthrough statement is where control flow goes from any path that
-- doesn't end in a tail call.
makeFunctionGroupCode :: LocalFunctionGroup -> GenC CBlockItem
makeFunctionGroupCode lfg = do
  fallthrough <- newAnonymousLabel
  let fallthrough_stmt = CLabel fallthrough cEmptyStat [] internalNode
        
  -- Convert entry code
  (concat -> entry_statements) <- mapM codeItemStatements $ lfgEntry lfg
  
  -- At the end of the letrec's body, jump past local functions
  let entry_ft = [CBlockStmt $ CGoto fallthrough internalNode]

  -- Convert local functions
  functions <- mapM (makeFunctionCode fallthrough) $ lfgGroup lfg
  let decls = concatMap lfunParameters $ lfgGroup lfg

  -- Assemble a C block statement
  let block_items = map CBlockDecl decls ++
                    entry_statements ++
                    entry_ft ++
                    functions ++
                    [CBlockStmt fallthrough_stmt]
      compound = cCompoundStat block_items
  return $ CBlockStmt $ CLabel (lfgLabel lfg) compound [] internalNode


makeFunctionCode :: Ident -> LocalFunction -> GenC CBlockItem
makeFunctionCode fallthrough local_function = do
  let fallthrough_stmt =
        if lfunFallsThrough local_function
        then [CBlockStmt $ CGoto fallthrough internalNode]
        else []
  (concat -> body) <- mapM codeItemStatements (lfunBody local_function)
  let statements = body ++ fallthrough_stmt
      compound = cCompoundStat statements
  return $ CBlockStmt $ CLabel (lfunLabel local_function) compound [] internalNode

-- | Generate a forward declaration and definition of a function
genFun :: Set.Set Var -> FunDef -> GenC (CDecl, CFunDef)
genFun exported_vars (Def v fun)
  | not (isPrimFun fun) = 
      internalError "genFun: Can only generate primitive-call functions"
  | otherwise = do
    return_type <- returnTypeDecl (map from_prim_type $ funReturnTypes fun)

    param_decls <- sequence [declareLocalVariable v Nothing
                            | v <- funParams fun]
    let -- Function declaration
        (return_type_specs, fun_declr) =
          mark_static_if_not_exported $ funDeclSpecs param_decls return_type
        fun_decl = CDeclr (Just (varIdent v)) fun_declr Nothing [] internalNode

    -- Create the function body
    let return_values = ReturnValues $ funReturnTypes fun
    (body_stmt, _) <- makeBlock =<< genStatement return_values (funBody fun)
    let body_stmt' = insert_stack_variable_def body_stmt

    let forward_declaration =
          CDecl return_type_specs [(Just fun_decl, Nothing, Nothing)] internalNode
        definition =
          CFunDef return_type_specs fun_decl [] body_stmt' internalNode
    return (forward_declaration, definition)
  where
    from_prim_type (PrimType t) = t
    from_prim_type _ = internalError "genFun: Unexpected record type"

    mark_static_if_not_exported specs =
      if v `Set.member` exported_vars
      then specs
      else staticDeclSpecs specs

    -- Insert local variables for the stack data pointer
    insert_stack_variable_def (CCompound llabs block_items info) =
      let data_name = internalIdent "frame_data"
          ptr_name  = internalIdent "frame_ptr"
          -- If stack space is used, declare a local variable
          data_def =
            case funFrameSize fun
            of 0 -> []
               sz -> let specs = arrayDeclSpecs (smallIntConst sz) $
                                 primTypeDeclSpecs (IntType Signed S8)
                     in [declareVariable data_name specs Nothing]
          ptr_expr =
            if funFrameSize fun == 0
            then nullPtr
            else cUnary CAdrOp $ cVar data_name
          ptr_def =
            let specs = primTypeDeclSpecs PointerType
            in [declareVariable ptr_name specs (Just ptr_expr)]
          defs = data_def ++ ptr_def
      in CCompound llabs (map CBlockDecl defs ++ block_items) info

-- | Create a global static data definition and initialization code.
genData :: GlobalVars -> Set.Set Var -> DataDef -> (CExtDecl, CStat)
genData gvars exported_vars (Def v (StaticData record_type values)) =
  (CDeclExt $
   declareBytes not_exported v (recordSize record_type) (recordAlignment record_type),
   initializeBytes gvars v record_type values)
  where
    not_exported = not $ v `Set.member` exported_vars

-- | Declare an external variable.  Its actual type is unimportant, since it
-- is cast to the appropriate type every time it is used.  Use an array type
-- so that (by C's semantics) references to the variable get its /address/ 
-- instead of its contents.
genImport :: Import -> [CDecl]
genImport impent =
  case impent
  of ImportClosureFun entry_points _ ->
       let clo =
             case globalClosure entry_points
             of Just x -> x
                Nothing -> internalError "genImport: Missing global closure"
       in map genImportVar [ directEntry entry_points
                           , exactEntry entry_points
                           , inexactEntry entry_points
                           , clo]
     ImportPrimFun v _ _ ->
       [genImportVar v]
     ImportData v _ ->
       [genImportVar v]

genImportVar :: Var -> CDecl
genImportVar v =
  let return_type_specs =
        [CStorageSpec (CExtern internalNode),
         CTypeSpec $ CVoidType internalNode]
      pointer_decl =
        [CArrDeclr [] (CNoArrSize False) internalNode,
         CPtrDeclr [] internalNode]
  in declareVariable (varIdent v) (return_type_specs, pointer_decl) Nothing

initializeBytes gvars v record_type values =
  let base = cVar (varIdent v)
      stmts =
        map mk_stmt $
        zipWith (initializeField gvars base) (recordFields record_type) values
  in cCompoundStat stmts
  where
    mk_stmt e = CBlockStmt $ CExpr (Just e) internalNode

initializeField gvars base fld val =
  -- Generate the assignment *(TYPE *)(PYON_OFF(base, fld)) = val
  let field_offset = smallIntConst (fieldOffset fld)
      field_ptr = offset base field_offset
      field_cast_ptr = case fieldType fld
                       of PrimField t -> cPtrCast t field_ptr
                          _ -> internalError "initializeField"
      lhs = CUnary CIndOp field_cast_ptr internalNode
      rhs = genValWorker gvars val
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
      body = cCompoundStat (map CBlockStmt stmts)
  in CFunDef [static, return_type] fun_decl [] body internalNode

generateCFile :: Module -> IO String
generateCFile (Module { moduleImports = imports
                      , moduleGlobals = defs
                      , moduleExports = exports}) = do
  ident_supply <- newNameSupply
      
  -- Create an import declaration for symbols that are not defined in
  -- this module
  let import_decls =
        concatMap genImport $
        filter (not . (`Set.member` defined_vars) . importVar) imports
  
  let (data_defs, data_inits) =
        unzip $ map (genData global_vars exported_vars) datas
  let init_fun = initializationFunction data_inits
  
  ((fun_decls, fun_defs), structs) <-  
    withTheLLVarIdentSupply $ \var_supply ->
    let gen_c_env = Env global_vars Map.empty ident_supply var_supply
    in runGenC (mapAndUnzipM (genFun defined_vars) funs) gen_c_env Map.empty
       
  let struct_decls =
        [declareStruct name (map primTypeDeclSpecs fields)
        | (fields, name) <- Map.toList structs]
  
  let top_level = map CDeclExt struct_decls ++
                  map CDeclExt import_decls ++
                  map CDeclExt fun_decls ++
                  data_defs ++
                  CFDefExt init_fun :
                  map CFDefExt fun_defs
  return $ makeCFileText top_level
  where
    flattened_defs = concatMap groupMembers defs
    (funs, datas) = partitionGlobalDefs flattened_defs
    defined_vars = Set.fromList $ map globalDefiniendum flattened_defs
    global_vars = defined_vars `Set.union` Set.fromList (map importVar imports)
    exported_vars = Set.fromList $ map fst exports
      
      
makeCFileText top_level =
  let transl_module = CTranslUnit top_level internalNode
      module_body_text = show $ pretty transl_module
  in cModuleHeader ++ module_body_text
  
cModuleHeader =
  "#include <inttypes.h>\n\
  \#include <math.h>\n\
  \typedef void *PyonPtr;\n\
  \#define PYON_OFF(base, offset) ((PyonPtr)((char *)(base) + (offset)))\n"
