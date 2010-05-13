
{-# LANGUAGE ForeignFunctionInterface, DeriveDataTypeable #-}

module Pyon.Exports.Untyped() where

import Control.Monad
import Foreign.C
import qualified Language.Haskell.TH as TH

import PythonInterface.Python
import PythonInterface.HsObject
import Gluon.Common.SourcePos
import qualified Gluon.Core as Gluon
import Pyon.Globals
import Pyon.Untyped.Syntax
import Pyon.Untyped.Print
import Pyon.Untyped.TypeInference
import Pyon.Untyped.BuiltinsTH
import Pyon.Untyped.Builtins
import Pyon.Untyped.HMType
import Pyon.Untyped.Kind
import Pyon.Untyped.InitializeBuiltins
import Pyon.SystemF.Syntax(Lit(..))
import qualified Pyon.SystemF.Typecheck as SystemF
import qualified Pyon.SystemF.Print as SystemF
import qualified Pyon.SystemF.ElimPatternMatching as SystemF
import qualified Pyon.SystemF.PartialEval as SystemF
import qualified Pyon.SystemF.DeadCode as SystemF
import Pyon.SystemF.Flatten.ToAnf as SystemF
import qualified Pyon.Anf.Print as Anf
import qualified Pyon.Anf.Typecheck as Anf

-- Imported for compilation dependences only
import Pyon.NewCore.Optimizations()

dummyAnn :: Ann
dummyAnn = Ann noSourcePos

posAnn :: SourcePos -> Ann
posAnn pos = Ann pos

-------------------------------------------------------------------------------
-- Constants

foreign export ccall pyon_builtinTypes :: IO PyPtr

-- Create a list of (name, type) pairs
pyon_builtinTypes = rethrowExceptionsInPython $ do
  let assocs = zip pyonSourceTypes builtinTypes
  withPyPtrExc (newList $ length assocs) $ \list -> do
    forM_ (zip [0..] assocs) $ \(index, (name, ty)) ->
      withPyPtrExc (newTuple 2) $ \tuple -> do
        withPyPtrExc (stringToPython name) $ setTupleItem tuple 0
        withPyPtrExc (newHsObject (ConTy ty)) $ setTupleItem tuple 1
        setListItem list index tuple
    return list

foreign export ccall pyon_globalVariables :: IO PyPtr

-- Create a list of (name, variable) pairs
pyon_globalVariables = rethrowExceptionsInPython $ do
  let assocs = zip pyonSourceGlobals builtinGlobals
  withPyPtrExc (newList $ length assocs) $ \list -> do
    forM_ (zip [0..] assocs) $ \(index, (name, var)) ->
      withPyPtrExc (newTuple 2) $ \tuple -> do
        withPyPtrExc (stringToPython name) $ setTupleItem tuple 0
        withPyPtrExc (newHsObject var) $ setTupleItem tuple 1
        setListItem list index tuple
    return list

foreign export ccall pyon_fun_makelist :: IO PyPtr
foreign export ccall pyon_fun_do :: IO PyPtr
foreign export ccall pyon_fun_guard :: IO PyPtr
foreign export ccall pyon_fun_iter :: IO PyPtr
foreign export ccall pyon_fun_iterBind :: IO PyPtr
foreign export ccall pyon_oper_ADD :: IO PyPtr
foreign export ccall pyon_oper_SUB :: IO PyPtr
foreign export ccall pyon_oper_MUL :: IO PyPtr
foreign export ccall pyon_oper_DIV :: IO PyPtr
foreign export ccall pyon_oper_MOD :: IO PyPtr
foreign export ccall pyon_oper_FLOORDIV :: IO PyPtr
foreign export ccall pyon_oper_POWER :: IO PyPtr
foreign export ccall pyon_oper_EQ :: IO PyPtr
foreign export ccall pyon_oper_NE :: IO PyPtr
foreign export ccall pyon_oper_LT :: IO PyPtr
foreign export ccall pyon_oper_LE :: IO PyPtr
foreign export ccall pyon_oper_GT :: IO PyPtr
foreign export ccall pyon_oper_GE :: IO PyPtr
foreign export ccall pyon_oper_BITWISEAND :: IO PyPtr
foreign export ccall pyon_oper_BITWISEOR :: IO PyPtr
foreign export ccall pyon_oper_BITWISEXOR :: IO PyPtr
foreign export ccall pyon_oper_NEGATE :: IO PyPtr
foreign export ccall pyon_Star :: IO PyPtr

globalObject x = rethrowExceptionsInPython $ newHsObject x

pyon_fun_makelist = globalObject $ tiBuiltin the_makelist
pyon_fun_do = globalObject $ tiBuiltin the_do
pyon_fun_guard = globalObject $ tiBuiltin the_guard
pyon_fun_iter = globalObject $ tiBuiltin the___iter__
pyon_fun_iterBind = globalObject $ tiBuiltin the_iterBind
pyon_oper_ADD = globalObject $ tiBuiltin the___add__
pyon_oper_SUB = globalObject $ tiBuiltin the___sub__
pyon_oper_MUL = globalObject $ tiBuiltin the___mul__
pyon_oper_DIV = globalObject $ tiBuiltin the___div__
pyon_oper_MOD = globalObject $ tiBuiltin the___mod__
pyon_oper_FLOORDIV = globalObject $ tiBuiltin the___floordiv__
pyon_oper_POWER = globalObject $ tiBuiltin the___power__
pyon_oper_EQ = globalObject $ tiBuiltin the___eq__
pyon_oper_NE = globalObject $ tiBuiltin the___ne__
pyon_oper_LT = globalObject $ tiBuiltin the___lt__
pyon_oper_LE = globalObject $ tiBuiltin the___le__
pyon_oper_GT = globalObject $ tiBuiltin the___gt__
pyon_oper_GE = globalObject $ tiBuiltin the___ge__
pyon_oper_BITWISEAND = globalObject $ tiBuiltin the___and__
pyon_oper_BITWISEOR = globalObject $ tiBuiltin the___or__
pyon_oper_BITWISEXOR = globalObject $ tiBuiltin the___xor__
pyon_oper_NEGATE = globalObject $ tiBuiltin the___negate__
pyon_Star = globalObject Star

-------------------------------------------------------------------------------
-- Constructors

foreign export ccall pyon_SourcePos :: CString -> CInt -> CInt -> IO PyPtr 

pyon_SourcePos fname line column = do
  s <- peekCString fname
  newHsObject $ fileSourcePos s (fromIntegral line) (fromIntegral column)

foreign export ccall pyon_ArrowK :: PyPtr -> PyPtr -> IO PyPtr

pyon_ArrowK py_k1 py_k2 = rethrowExceptionsInPython $ do
  k1 <- fromHsObject' py_k1
  k2 <- fromHsObject' py_k2
  newHsObject $ k1 :-> k2

foreign export ccall pyon_RigidTyVar :: PyPtr -> PyPtr -> IO PyPtr

pyon_RigidTyVar py_label py_kind = rethrowExceptionsInPython $ do
  label <- fromHsObject' py_label
  kind <- fromHsObject' py_kind
  newHsObject =<< newRigidTyVar kind (Just label)

foreign export ccall pyon_tupleType :: PyPtr -> IO PyPtr

pyon_tupleType py_fields = rethrowExceptionsInPython $ do
  fields <- fromTypeOrConList py_fields
  newHsObject $ tupleType fields

foreign export ccall pyon_Variable :: PyPtr -> IO PyPtr

pyon_Variable ptr = rethrowExceptionsInPython $ do
  -- Name is 'None' or a label
  name <- if isPyNone ptr
          then return Nothing
          else do b <- isHsObject ptr 
                  if b
                    then liftM Just $ fromHsObject' ptr
                    else throwPythonExc pyTypeError "Expecting HsObject or None"
  sfvar_id <- getNextVarIdent
  let sfvar = Just $ Gluon.mkVar sfvar_id name Gluon.ObjectLevel
  newHsObject =<< newVariable name sfvar

foreign export ccall pyon_WildP :: IO PyPtr
foreign export ccall pyon_VariableP :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_TupleP :: PyPtr -> IO PyPtr

pyon_WildP = rethrowExceptionsInPython $ do
  newHsObject $ WildP dummyAnn

pyon_VariableP py_v py_type = rethrowExceptionsInPython $ do
  v <- fromHsObject' py_v
  ty <- if isPyNone py_type
        then return Nothing 
        else liftM Just $ fromTypeOrCon py_type
  newHsObject $ VariableP dummyAnn v ty

pyon_TupleP py_fs = rethrowExceptionsInPython $ do
  fs <- fromListOfHsObject' py_fs
  newHsObject $ TupleP dummyAnn fs

foreign export ccall pyon_VariableE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_NoneLiteral :: PyPtr -> IO PyPtr
foreign export ccall pyon_IntLiteral :: PyPtr -> CLong -> IO PyPtr
foreign export ccall pyon_FloatLiteral :: PyPtr -> CDouble -> IO PyPtr
foreign export ccall pyon_BoolLiteral :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_UndefinedE :: PyPtr -> IO PyPtr
foreign export ccall pyon_TupleE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_CallE :: PyPtr -> PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_FunE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_IfE :: PyPtr -> PyPtr -> PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_LetE :: PyPtr -> PyPtr -> PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_LetrecE :: PyPtr -> PyPtr -> PyPtr -> IO PyPtr

pyon_VariableE py_pos py_v = rethrowExceptionsInPython $ do
  pos <- fromHsObject' py_pos
  v <- fromHsObject' py_v
  newHsObject $ VariableE (posAnn pos) v

pyon_NoneLiteral py_pos = rethrowExceptionsInPython $ do 
  pos <- fromHsObject' py_pos
  newHsObject $ LiteralE (posAnn pos)  NoneL

pyon_IntLiteral py_pos n = rethrowExceptionsInPython $ do
  pos <- fromHsObject' py_pos
  newHsObject $ LiteralE (posAnn pos) (IntL (fromIntegral n))

pyon_FloatLiteral py_pos d = rethrowExceptionsInPython $ do
  pos <- fromHsObject' py_pos
  newHsObject $ LiteralE (posAnn pos) (FloatL (realToFrac d))

pyon_BoolLiteral py_pos py_bool = rethrowExceptionsInPython $ do
  pos <- fromHsObject' py_pos
  b <- fromPythonBool py_bool
  newHsObject $ LiteralE (posAnn pos) (BoolL b)

pyon_UndefinedE py_pos = rethrowExceptionsInPython $ do
  pos <- fromHsObject' py_pos
  newHsObject $ UndefinedE (posAnn pos)

pyon_TupleE py_pos py_fs = rethrowExceptionsInPython $ do
  pos <- fromHsObject' py_pos
  fs <- fromListOfHsObject' py_fs
  newHsObject $ TupleE (posAnn pos) fs

pyon_CallE py_pos py_oper py_args = rethrowExceptionsInPython $ do
  pos <- fromHsObject' py_pos
  oper <- fromHsObject' py_oper
  args <- fromListOfHsObject' py_args
  newHsObject $ CallE (posAnn pos) oper args

pyon_FunE py_pos py_fun = rethrowExceptionsInPython $ do
  pos <- fromHsObject' py_pos
  f <- fromHsObject' py_fun
  newHsObject $ FunE (posAnn pos) f

pyon_IfE py_pos py_cond py_tr py_fa = rethrowExceptionsInPython $ do
  pos <- fromHsObject' py_pos
  cond <- fromHsObject' py_cond
  tr <- fromHsObject' py_tr
  fa <- fromHsObject' py_fa
  newHsObject $ IfE (posAnn pos) cond tr fa

pyon_LetE py_pos py_lhs py_rhs py_body = rethrowExceptionsInPython $ do
  pos <- fromHsObject' py_pos
  lhs <- fromHsObject' py_lhs
  rhs <- fromHsObject' py_rhs
  body <- fromHsObject' py_body
  newHsObject $ LetE (posAnn pos) lhs rhs body

pyon_LetrecE py_pos py_defs py_body = rethrowExceptionsInPython $ do
  pos <- fromHsObject' py_pos
  defs <- fromListOfHsObject' py_defs
  body <- fromHsObject' py_body
  newHsObject $ LetrecE (posAnn pos) defs body

foreign export ccall pyon_Function :: PyPtr -> PyPtr -> PyPtr -> PyPtr
                                   -> PyPtr -> IO PyPtr

pyon_Function py_pos py_qvars py_params py_rt py_body =
  rethrowExceptionsInPython $ do
    pos <- fromHsObject' py_pos
    qvars <- if isPyNone py_qvars
             then return Nothing
             else liftM Just $ fromListOfHsObject' py_qvars
    params <- fromListOfHsObject' py_params
    rt <- if isPyNone py_rt
          then return Nothing
          else liftM Just $ fromTypeOrCon py_rt
    body <- fromHsObject' py_body
    newHsObject $ Function (posAnn pos) qvars params rt body

foreign export ccall pyon_Def :: PyPtr -> PyPtr -> IO PyPtr

pyon_Def py_v py_f = rethrowExceptionsInPython $ do
  v <- fromHsObject' py_v
  f <- fromHsObject' py_f
  newHsObject $ FunctionDef v f

foreign export ccall pyon_Export :: PyPtr -> PyPtr -> IO PyPtr

pyon_Export py_pos py_name = rethrowExceptionsInPython $ do
  p <- fromHsObject' py_pos
  n <- fromHsObject' py_name
  newHsObject $ Export (posAnn p) n

foreign export ccall pyon_Module :: PyPtr -> PyPtr -> IO PyPtr 

pyon_Module py_defs py_exports = rethrowExceptionsInPython $ do
  defgroups <- mapList (mapList fromHsObject') py_defs
  exports <- fromListOfHsObject' py_exports
  newHsObject $ Module defgroups exports
  where
    mapList f list = do
      -- Argument must be a list
      is_list <- isList list
      unless is_list $ throwPythonExc pyTypeError "Expecting a list"
      
      list_size <- getListSize list
      
      -- Call 'f' to process each list element
      forM [0 .. list_size - 1] $ \i -> do
        f =<< getListItem list i

foreign export ccall pyon_typeApplication :: PyPtr -> PyPtr -> IO PyPtr

pyon_typeApplication py_oper py_args = rethrowExceptionsInPython $ do
  oper <- fromTypeOrCon py_oper
  args <- fromTypeOrConList py_args
  newHsObject $ foldl AppTy oper args

-- Unpack a PyPtr that points to either a HMType or a TyCon.  Convert it
-- to a HMType.
fromTypeOrCon py_ptr = do
  mty <- fromHsObject py_ptr
  case mty of
    Just ty -> return ty
    Nothing -> do mcon <- fromHsObject py_ptr
                  case mcon of
                    Just con -> return $ ConTy con
                    Nothing  -> throwPythonExc pyTypeError
                                "Expecting a HMType or TyCon"

-- Unpack a list of HMType or TyCon
fromTypeOrConList py_listptr = do
  is_list <- isList py_listptr
  unless is_list $ throwPythonExc pyTypeError "Expecting a list"
  
  len <- getListSize py_listptr
  forM [0 .. len - 1] $ fromTypeOrCon <=< getListItem py_listptr

-------------------------------------------------------------------------------
-- Functions

foreign export ccall pyon_initializeUntypedModule :: IO Bool

pyon_initializeUntypedModule = do
  (initializeTIBuiltins >> return True) `catch` \exc -> print exc >> return False

foreign export ccall pyon_typeInferModule :: PyPtr -> PyPtr -> IO PyPtr

pyon_typeInferModule _self py_m = rethrowExceptionsInPython $ do
  expectHsObject py_m
  m <- fromHsObject' py_m
  newHsObject =<< typeInferModule m

foreign export ccall pyon_typeCheckSystemFModule :: PyPtr -> PyPtr -> IO PyPtr

pyon_typeCheckSystemFModule _self mod = rethrowExceptionsInPython $ do
  expectHsObject mod
  m <- fromHsObject' mod
  SystemF.typeCheckModulePython m
  pyNone

foreign export ccall pyon_typeCheckAnfModule :: PyPtr -> PyPtr -> IO PyPtr

pyon_typeCheckAnfModule _self mod = rethrowExceptionsInPython $ do
  expectHsObject mod
  m <- fromHsObject' mod
  Anf.typeCheckModule m
  pyNone

{-
foreign export ccall pyon_specializeSystemFModule :: PyPtr -> PyPtr -> IO PyPtr

pyon_specializeSystemFModule _self mod = rethrowExceptionsInPython $ do
  expectHsObject mod
  m <- fromHsObject' mod
  newHsObject =<< SystemF.doSpecialization m
-}

foreign export ccall pyon_eliminatePatternMatching :: PyPtr -> PyPtr -> IO PyPtr

pyon_eliminatePatternMatching _self mod = rethrowExceptionsInPython $ do
  expectHsObject mod
  m <- fromHsObject' mod
  newHsObject =<< SystemF.eliminatePatternMatching m

foreign export ccall pyon_eliminateDeadCode :: PyPtr -> PyPtr -> IO PyPtr

pyon_eliminateDeadCode _self mod = rethrowExceptionsInPython $ do
  expectHsObject mod
  m <- fromHsObject' mod
  newHsObject $ SystemF.eliminateDeadCode m


foreign export ccall pyon_partialEvaluateModule :: PyPtr -> PyPtr -> IO PyPtr

pyon_partialEvaluateModule _self mod = rethrowExceptionsInPython $ do
  expectHsObject mod
  m <- fromHsObject' mod
  newHsObject $ SystemF.partialEvaluateModule m

foreign export ccall pyon_flattenModule :: PyPtr -> PyPtr -> IO PyPtr

pyon_flattenModule _self mod = rethrowExceptionsInPython $ do
  expectHsObject mod
  m <- fromHsObject' mod
  newHsObject =<< SystemF.flatten m

foreign export ccall pyon_printModule :: PyPtr -> PyPtr -> IO PyPtr

pyon_printModule _self mod = rethrowExceptionsInPython $ do
  expectHsObject mod
  doAny [print_untyped mod, print_systemF mod, print_anf mod, print_fail]
  pyNone
  where
    doAny (m:ms) = do
      x <- m
      if x then return () else doAny ms
    doAny [] = return ()

    print_untyped mod = do
      m <- fromHsObject mod
      case m of
        Nothing -> return False
        Just mod -> do print $ pprModule mod
                       return True
    
    print_systemF mod = do
      m <- fromHsObject mod
      case m of
        Nothing -> return False
        Just mod -> do print $ SystemF.pprModule mod
                       return True
    
    print_anf mod = do
      m <- fromHsObject mod
      case m of
        Nothing -> return False
        Just mod -> do print $ Anf.pprModule mod
                       return True

    print_fail =
      throwPythonExc pyTypeError "Expecting an untyped or system F module"

