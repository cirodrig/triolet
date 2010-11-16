
{-# LANGUAGE ViewPatterns #-}
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

import Gluon.Common.Error
import Gluon.Common.Identifier(fromIdent)
import Gluon.Common.Label
import Gluon.Common.Supply
import LowLevel.Builtins
import LowLevel.Label
import LowLevel.Types
import LowLevel.Record
import LowLevel.Syntax
import LowLevel.Print
import LowLevel.GenerateCUtils
import LowLevel.GenerateCCode

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

data Env = Env
           { globalVars :: GlobalVars 
           , localFunctions :: LocalFunctionMap 
           , nameSupply :: !(Supply Int)
           }

newtype GenC a = GenC (Reader Env a)

runGenC (GenC m) env = runReader m env

instance Functor GenC where
  fmap f (GenC m) = GenC (fmap f m)

instance Monad GenC where
  return x = GenC (return x)
  GenC m >>= k = GenC (m >>= \x -> case k x of GenC m' -> m')

instance MonadFix GenC where
  mfix f = GenC (mfix $ \x -> case f x of GenC m -> m)

newAnonymousLabel :: (Ident -> GenC a) -> GenC a
newAnonymousLabel f = GenC $ Reader $ \env -> do
  forceSupplyValue (nameSupply env) $ \n ->
    case f (make_label n) of GenC m -> runReader m env
  where
    make_label n = internalIdent $ "c_" ++ show n


getGlobalVars :: GenC GlobalVars
getGlobalVars = GenC $ asks globalVars

withLocalFunctions :: [(Var, LocalFunction)] -> GenC a -> GenC a
withLocalFunctions local_fs (GenC m) = GenC $ local insert m
  where
    insert env =
      env {localFunctions = 
              foldr (uncurry Map.insert) (localFunctions env) local_fs}

-------------------------------------------------------------------------------
-- Non-recursive expressions

genLit :: Lit -> CExpr
genLit NullL           = nullPtr
genLit (BoolL True)    = smallIntConst 1
genLit (BoolL False)   = smallIntConst 0
genLit (IntL sgn sz n) = intConst sgn sz n
genLit (FloatL S32 n)  = floatConst S32 n

genVal :: GlobalVars -> Val -> CExpr
genVal gvars (VarV v)
  | v `Set.member` gvars =
      -- Take address of global variable, and cast to pointer
      cPtrCast $ cUnary CAdrOp var_exp
  | otherwise = var_exp
  where
  var_exp = cVar $ varIdentScoped gvars v
      
genVal _ (LitV l) = genLit l

genVal _ _ = internalError "genVal: Unexpected value"

valPrimType v =
  case valType v
  of PrimType pt -> pt
     _ -> internalError "valPrimType"

genAssignVar :: Var -> CExpr -> CExpr
genAssignVar v e = cAssign (CVar (localVarIdent v) internalNode) e

-------------------------------------------------------------------------------
-- Atoms and statements

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

genManyResults :: ReturnValues -> [CExpr] -> [CBlockItem]
genManyResults rtn exprs =
  case rtn
  of AssignValues [] -> return_nothing
     AssignValues [v] -> return_expr $ genAssignVar v expr
     AssignValues xs -> too_many xs
     DefineValues [] -> return_nothing
     DefineValues [v] ->
       [CBlockDecl $ declareLocalVariable v $ Just expr]
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

genOneResult :: ReturnValues -> CExpr -> [CBlockItem]
genOneResult rtn expr =
  case rtn
  of AssignValues [] -> return_expr expr
     AssignValues [v] -> return_expr $ genAssignVar v expr
     DefineValues [] -> return_expr expr
     DefineValues [v] ->
       [CBlockDecl $ declareLocalVariable v $ Just expr]
     ReturnValues [] -> return_expr expr
     ReturnValues [t] -> 
       return_stm $ CReturn (Just expr) internalNode
  where
    return_stm stm = [CBlockStmt stm]
    return_expr e = return_stm $ CExpr (Just e) internalNode

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
genAtom returns atom = GenC $ Reader $ \env ->
  let gvars = globalVars env
      local_functions = localFunctions env
  in case atom
     of ValA vals ->
          (genManyResults returns $ map (genVal gvars) vals, True)
        PrimCallA op args ->
          case genCall gvars local_functions (returnTypes returns) op args
          of Left items -> (items, False)
             Right call -> (genOneResult returns call, True)
        PrimA op args ->
          (genOneResult returns $ genPrimCall op $ map (genVal gvars) args,
           True)
        _ -> internalError "genAtom: Unexpected atom"

-- | Create a function call expression.  The call is either generated as a
-- sequence of assignments followed by a @goto@ or a C function call.
genCall :: GlobalVars 
        -> LocalFunctionMap 
        -> [PrimType] 
        -> Val 
        -> [Val] 
        -> Either [CBlockItem] CExpr
genCall gvars local_functions return_types op args
  | VarV v <- op,
    Just lfun <- Map.lookup v local_functions =
      -- Generate a local function "call".  Jump to the function. 
      -- Assign parameter variables
      let assignments = zipWith make_assignment (lfunParamVars lfun) $
                        map (genVal gvars) args
            where
              make_assignment ident expr =
                cExprStat $ cAssign (cVar ident) expr

          statements = map CBlockStmt $
                       assignments ++ [cGoto $ lfunLabel lfun]
      in Left statements

  | otherwise =
      -- Generate an ordinary function call.
      let op' = genVal gvars op
          args' = map (genVal gvars) args
      
          -- Create the actual function type
          return_type =
            case return_types
            of [] -> voidDeclSpecs
               [t] -> primTypeDeclSpecs t
               _ -> internalError "genCall: Cannot generate multiple return values"

          param_types =
            map (anonymousDecl . primTypeDeclSpecs . valPrimType) args
          fn_type =
            ptrDeclSpecs $ funDeclSpecs param_types return_type

          -- Cast operator to function pointer type
          cast = CCast (anonymousDecl fn_type) op' internalNode
      in Right (cCall cast args')

genPrimCall :: Prim -> [CExpr] -> CExpr
genPrimCall prim args =
  case prim
  of PrimCastZ from_sgn to_sgn sz ->
       case args of [arg] -> cCast (IntType to_sgn sz) arg
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
                  cCond (geZero x `equals` geZero y) zero y
            in binary' CAddOp remainder correction
     PrimMaxZ _ _ ->
       case args
       of [x, y] -> cCond (binary' CGeqOp x y) x y
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
       case args of [ptr, off] -> offset ptr off
     PrimLoad (PrimType ty) ->
       -- Cast the pointer to the desired pointer type, then dereference
       case args
       of [ptr, off] ->
            let offptr = offset ptr off
                cast_ptr = cCast ty offptr
            in CUnary CIndOp cast_ptr internalNode
     PrimStore (PrimType ty) ->
       -- Cast the pointer to the desired type, then assign to it
       case args
       of [ptr, off, val] ->
            let offptr = offset ptr off
                cast_ptr = cCast ty offptr
                lhs = CUnary CIndOp cast_ptr internalNode
            in CAssign CAssignOp lhs val internalNode
     PrimAAddZ sgn sz 
       | sz == nativeIntSize ->
           case args
           of [ptr, val] ->
                let add_fun = internalIdent "__sync_fetch_and_add"
                    cast_ptr = cCast (IntType sgn sz) ptr
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
     PrimAddF _ -> binary CAddOp args
     PrimSubF _ -> binary CSubOp args
     PrimMulF _ -> binary CMulOp args
     PrimModF _ -> internalError "Not implemented: floating-point modulus"
     _ -> internalError $ 
          "Cannot generate C code for primitive operation: " ++
          show (pprPrim prim)
  where
    zero = smallIntConst 0
    geZero x = binary' CGeqOp x zero
    equals x y = binary' CEqOp x y
    binary' op x y = cBinary op x y
    binary op [x, y] = binary' op x y
    binary op _ = internalError "genPrimCall: Wrong number of arguments"

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
       newAnonymousLabel $ \label ->
       genLocalFunctions returns funs $ \localfs -> do
         (code, fallthrough) <- genStatement returns stm'
         return ([Group $ LocalFunctionGroup label code localfs fallthrough],
                 fallthrough)
     SwitchE cond [(c1, block1), (c2, block2)]
       | c1 == BoolL True && c2 == BoolL False ->
         genIf returns cond block1 block2
       | c1 == BoolL False && c2 == BoolL True ->
         genIf returns cond block2 block1
       | otherwise ->
         internalError "genStatement: Unexpected branching control flow"
     ReturnE atom -> do
       (block_items, fallthrough) <- genAtom returns atom
       return ([CCode block_items], fallthrough)
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
  let (returns', return_var_decls) =
        case returns
        of AssignValues vs -> (returns, [])
           DefineValues vs ->
             (AssignValues vs, map (CBlockDecl . declareUndefLocalVariable) vs)
           ReturnValues vs -> (returns, [])

  (true_path, true_fallthrough) <- makeBlock =<< genStatement returns' if_true
  (false_path, false_fallthrough) <- makeBlock =<< genStatement returns' if_false
  let false_branch = if isEmptyBlock false_path
                     then Nothing
                     else Just false_path

  gvars <- getGlobalVars
  let cond_expr = genVal gvars scrutinee
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
    add_to_env local_functions =
      withLocalFunctions (lazy_zip fun_names local_functions)
      
    fun_names = [v | FunDef v _ <- fs]
    
    -- Like 'zip', but lazy in the second parameter.
    lazy_zip (f:fs) ~(lf:lfs) = (f,lf) : lazy_zip fs lfs
    lazy_zip [] _ = []

-- | Generate code for a locally defined function.  The assignment destinations
-- on the fall-through path are given as extra parameters.  They are only
-- assigned if the function falls through.
genLocalFunction :: ReturnValues -> FunDef -> GenC LocalFunction
genLocalFunction returns (FunDef v f)
  | not (isPrimFun f) =
      internalError "genLocalFunction: Not a primitive-call function"
  | otherwise = do
      let fun_name = localVarIdent v
      let param_decls = map declareUndefLocalVariable $ funParams f
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
      return $ CCompound [] (concat statements) internalNode

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
makeFunctionGroupCode lfg = newAnonymousLabel $ \fallthrough -> do
  let fallthrough_stmt =
        CLabel fallthrough (CExpr Nothing internalNode) [] internalNode
        
  -- Convert entry code
  (concat -> entry_statements) <- mapM codeItemStatements $ lfgEntry lfg
  
  -- Convert local functions
  functions <- mapM (makeFunctionCode fallthrough) $ lfgGroup lfg
  let decls = concatMap lfunParameters $ lfgGroup lfg

  -- Assemble a C block statement
  let block_items = map CBlockDecl decls ++
                    entry_statements ++
                    functions ++
                    [CBlockStmt fallthrough_stmt]
      compound = CCompound [] block_items internalNode
  return $ CBlockStmt $ CLabel (lfgLabel lfg) compound [] internalNode


makeFunctionCode :: Ident -> LocalFunction -> GenC CBlockItem
makeFunctionCode fallthrough local_function = do
  let fallthrough_stmt =
        if lfunFallsThrough local_function
        then [CBlockStmt $ CGoto fallthrough internalNode]
        else []
  (concat -> body) <- mapM codeItemStatements (lfunBody local_function)
  let statements = body ++ fallthrough_stmt
      compound = CCompound [] statements internalNode
  return $ CBlockStmt $ CLabel (lfunLabel local_function) compound [] internalNode

-- | Generate a forward declaration and definition of a function
genFun :: FunDef -> GenC (CDecl, CFunDef)
genFun (FunDef v fun) 
  | not (isPrimFun fun) = 
      internalError "genFun: Can only generate primitive-call functions"
  | otherwise = do
    let -- Function return type
      return_type =
        case funReturnTypes fun
        of [] -> voidDeclSpecs
           [PrimType t] -> primTypeDeclSpecs t
           [_] -> internalError "genFun: Unexpected return type"
           _ -> internalError "genFun: Cannot generate multiple return values"
      -- Function parameter declarations
      param_decls = [declareLocalVariable v Nothing | v <- funParams fun]
      -- Function declaration
      (return_type_specs, fun_declr) = funDeclSpecs param_decls return_type
      fun_decl = CDeclr (Just (varIdent v)) fun_declr Nothing [] internalNode

    -- Create the function body
    let return_values = ReturnValues $ map valueToPrimType $ funReturnTypes fun
    (body_stmt, _) <- makeBlock =<< genStatement return_values (funBody fun)

    let forward_declaration =
          CDecl return_type_specs [(Just fun_decl, Nothing, Nothing)] internalNode
        definition =
          CFunDef return_type_specs fun_decl [] body_stmt internalNode
    return (forward_declaration, definition)


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
genImport :: Import -> [CDecl]
genImport impent =
  case impent
  of ImportClosureFun entry_points ->
       let clo =
             case globalClosure entry_points
             of Just x -> x
                Nothing -> internalError "genImport: Missing global closure"
       in map genImportVar [ directEntry entry_points
                           , exactEntry entry_points
                           , inexactEntry entry_points
                           , clo]
     ImportPrimFun v _ ->
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
      fun_decl = CDeclr (Just $ varIdent v) pointer_decl Nothing [] internalNode
  in CDecl return_type_specs [(Just fun_decl, Nothing, Nothing)] internalNode

initializeBytes gvars v record_type values =
  let base = cVar (varIdent v)
      stmts =
        map mk_stmt $
        zipWith (initializeField gvars base) (recordFields record_type) values
  in CCompound [] stmts internalNode
  where
    mk_stmt e = CBlockStmt $ CExpr (Just e) internalNode

initializeField gvars base fld val =
  -- Generate the assignment *(TYPE *)(PYON_OFF(base, fld)) = val
  let field_offset = smallIntConst (fieldOffset fld)
      field_ptr = offset base field_offset
      field_cast_ptr = case fieldType fld
                       of PrimField t -> cCast t field_ptr
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

generateCFile :: Module -> IO String
generateCFile (Module imports funs datas _) = do
  ident_supply <- newNameSupply
      
  -- Create an import declaration for symbols that are not defined in
  -- this module
  let import_decls =
        concatMap genImport $
        filter (not . (`Set.member` defined_vars) . importVar) imports
      
  let (data_defs, data_inits) = unzip $ map (genData global_vars) datas
  let init_fun = initializationFunction data_inits
  
  let gen_c_env = Env global_vars Map.empty ident_supply
  let (fun_decls, fun_defs) = runGenC (mapAndUnzipM genFun funs) gen_c_env
  
  let top_level = map CDeclExt import_decls ++
                  map CDeclExt fun_decls ++
                  data_defs ++
                  CFDefExt init_fun :
                  map CFDefExt fun_defs
  return $ makeCFileText top_level
  where
    defined_vars =
        Set.fromList $ [f | FunDef f _ <- funs] ++
                       [v | DataDef v _ _ <- datas]
    global_vars = defined_vars `Set.union` Set.fromList (map importVar imports)
      
makeCFileText top_level =
  let transl_module = CTranslUnit top_level internalNode
      module_body_text = show $ pretty transl_module
  in cModuleHeader ++ module_body_text
  
cModuleHeader =
  "#include <inttypes.h>\n\
  \#include <pyon.h>\n"
