
{-# LANGUAGE ForeignFunctionInterface, DeriveDataTypeable #-}

module Pyon.Exports.SystemF() where

import Prelude hiding(sequence, mapM)
import Control.Applicative
import Control.Monad hiding(mapM)
import Data.Traversable
import Data.Typeable
import Foreign.Ptr(nullPtr)
import Foreign.C.String
import Foreign.C.Types

import PythonInterface.Python
import PythonInterface.HsObject
import Gluon.Common.Label
import qualified Gluon.Core
import Pyon.Globals
import Pyon.SystemF.Builtins
import Pyon.SystemF.Syntax
import Pyon.SystemF.Print
import Pyon.SystemF.Optimizations
import Pyon.Exports.Delayed

-------------------------------------------------------------------------------
-- Exported placeholder operations

foreign export ccall pyon_newExpPlaceholder :: IO PyPtr

pyon_newExpPlaceholder = newHsObject =<< (newPlaceholder :: IO (Delayed Exp))

foreign export ccall pyon_setExpPlaceholder :: PyPtr -> PyPtr -> IO PyPtr

pyon_setExpPlaceholder :: PyPtr -> PyPtr -> IO PyPtr
pyon_setExpPlaceholder placeholder value = rethrowExceptionsInPython $ do
  ph <- fromHsObject' placeholder
  val <- fromHsObject' value
  setPlaceholder ph (val :: Delayed Exp)
  pyNone

-------------------------------------------------------------------------------
-- Exported constants.
  
-- Helper function for exporting constants that may raise an exception
asGlobalObject :: Typeable a => a -> IO PyPtr
asGlobalObject = rethrowExceptionsInPython . newHsObject

foreign export ccall pyon_con_Action :: IO PyPtr
foreign export ccall pyon_con_Stream :: IO PyPtr
foreign export ccall pyon_con_NoneType :: IO PyPtr
foreign export ccall pyon_con_bool :: IO PyPtr
foreign export ccall pyon_con_list :: IO PyPtr
foreign export ccall pyon_con_EqDict :: IO PyPtr
foreign export ccall pyon_con_OrdDict :: IO PyPtr
foreign export ccall pyon_con_TraversableDict :: IO PyPtr
foreign export ccall pyon_con_EQ_Int :: IO PyPtr
foreign export ccall pyon_con_NE_Int :: IO PyPtr
foreign export ccall pyon_con_LT_Int :: IO PyPtr
foreign export ccall pyon_con_LE_Int :: IO PyPtr
foreign export ccall pyon_con_GT_Int :: IO PyPtr
foreign export ccall pyon_con_GE_Int :: IO PyPtr
foreign export ccall pyon_con_EQ_Float :: IO PyPtr
foreign export ccall pyon_con_NE_Float :: IO PyPtr
foreign export ccall pyon_con_LT_Float :: IO PyPtr
foreign export ccall pyon_con_LE_Float :: IO PyPtr
foreign export ccall pyon_con_GT_Float :: IO PyPtr
foreign export ccall pyon_con_GE_Float :: IO PyPtr
foreign export ccall pyon_con_EQ_Tuple2 :: IO PyPtr
foreign export ccall pyon_con_NE_Tuple2 :: IO PyPtr
foreign export ccall pyon_con_LT_Tuple2 :: IO PyPtr
foreign export ccall pyon_con_LE_Tuple2 :: IO PyPtr
foreign export ccall pyon_con_GT_Tuple2 :: IO PyPtr
foreign export ccall pyon_con_GE_Tuple2 :: IO PyPtr
foreign export ccall pyon_con_TRAVERSE_Stream :: IO PyPtr
foreign export ccall pyon_con_TRAVERSE_list :: IO PyPtr

pyon_con_Action = asGlobalObject $ pyonBuiltin the_Action
pyon_con_Stream = asGlobalObject $ pyonBuiltin the_Stream
pyon_con_NoneType = asGlobalObject $ pyonBuiltin the_NoneType
pyon_con_bool = asGlobalObject $ pyonBuiltin the_bool
pyon_con_list = asGlobalObject $ pyonBuiltin the_list
pyon_con_EqDict = asGlobalObject $ pyonBuiltin the_EqDict
pyon_con_OrdDict = asGlobalObject $ pyonBuiltin the_OrdDict
pyon_con_TraversableDict = asGlobalObject $ pyonBuiltin the_TraversableDict
pyon_con_EQ_Int = asGlobalObject $ eqMember $ pyonBuiltin the_EqDict_Int
pyon_con_NE_Int = asGlobalObject $ neMember $ pyonBuiltin the_EqDict_Int
pyon_con_LT_Int = asGlobalObject $ ltMember $ pyonBuiltin the_OrdDict_Int
pyon_con_LE_Int = asGlobalObject $ leMember $ pyonBuiltin the_OrdDict_Int
pyon_con_GT_Int = asGlobalObject $ gtMember $ pyonBuiltin the_OrdDict_Int
pyon_con_GE_Int = asGlobalObject $ geMember $ pyonBuiltin the_OrdDict_Int
pyon_con_EQ_Float = asGlobalObject $ eqMember $ pyonBuiltin the_EqDict_Float
pyon_con_NE_Float = asGlobalObject $ neMember $ pyonBuiltin the_EqDict_Float
pyon_con_LT_Float = asGlobalObject $ ltMember $ pyonBuiltin the_OrdDict_Float
pyon_con_LE_Float = asGlobalObject $ leMember $ pyonBuiltin the_OrdDict_Float
pyon_con_GT_Float = asGlobalObject $ gtMember $ pyonBuiltin the_OrdDict_Float
pyon_con_GE_Float = asGlobalObject $ geMember $ pyonBuiltin the_OrdDict_Float
pyon_con_EQ_Tuple2 = asGlobalObject $ eqMember $ pyonBuiltin the_EqDict_Tuple2
pyon_con_NE_Tuple2 = asGlobalObject $ neMember $ pyonBuiltin the_EqDict_Tuple2
pyon_con_LT_Tuple2 = asGlobalObject $ ltMember $ pyonBuiltin the_OrdDict_Tuple2
pyon_con_LE_Tuple2 = asGlobalObject $ leMember $ pyonBuiltin the_OrdDict_Tuple2
pyon_con_GT_Tuple2 = asGlobalObject $ gtMember $ pyonBuiltin the_OrdDict_Tuple2
pyon_con_GE_Tuple2 = asGlobalObject $ geMember $ pyonBuiltin the_OrdDict_Tuple2
pyon_con_TRAVERSE_Stream = asGlobalObject $ traverseMember $ pyonBuiltin the_TraversableDict_Stream
pyon_con_TRAVERSE_list = asGlobalObject $ traverseMember $ pyonBuiltin the_TraversableDict_list
  
foreign export ccall pyon_getTupleCon :: CInt -> IO PyPtr

pyon_getTupleCon n = rethrowExceptionsInPython $
  case getPyonTupleType (fromIntegral n)
  of Just c  -> newHsObject c
     Nothing -> throwPythonExc pyIndexError $ 
                "Tuple type of size " ++ show n ++ " not available"

foreign export ccall pyon_EqClass :: IO PyPtr
foreign export ccall pyon_OrdClass :: IO PyPtr
foreign export ccall pyon_TraversableClass :: IO PyPtr

pyon_EqClass = asGlobalObject EqClass
pyon_OrdClass = asGlobalObject OrdClass
pyon_TraversableClass = asGlobalObject TraversableClass

-------------------------------------------------------------------------------
-- Exportable constructors for System F things.
                               
-- Expressions, functions, definitions, and types are all constructed as
-- delayed objects.

foreign export ccall pyon_newVar :: CString -> IO PyPtr

pyon_newVar name = rethrowExceptionsInPython $ do
  label <- if name == nullPtr
           then return Nothing
           else do s <- peekCString name
                   return $ Just $ pgmLabel (moduleName "PyonInput") s
  id <- getNextSystemFVarIdent
  newHsObject $ Var id label

foreign export ccall pyon_mkIntL :: CLong -> IO PyPtr
foreign export ccall pyon_mkFloatL :: CDouble -> IO PyPtr
foreign export ccall pyon_mkBoolL :: CInt -> IO PyPtr
foreign export ccall pyon_mkNoneL :: IO PyPtr

pyon_mkIntL n = newHsObject $ IntL (fromIntegral n)
pyon_mkFloatL n = newHsObject $ FloatL (realToFrac n)
pyon_mkBoolL n = newHsObject $ BoolL (if n /= 0 then True else False)
pyon_mkNoneL = newHsObject NoneL 

foreign export ccall pyon_mkTyPat :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_mkWildP :: PyPtr -> IO PyPtr
foreign export ccall pyon_mkVarP :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_mkTupleP :: PyPtr -> IO PyPtr

pyon_mkTyPat tyvar kind = rethrowExceptionsInPython $ do
  t <- fromHsObject' tyvar
  k <- fromHsObject' kind
  newHsObject $ (TyPat t <$> k :: Delayed TyPat)

pyon_mkWildP ty = rethrowExceptionsInPython $ do
  t <- fromHsObject' ty
  newHsObject $ (WildP <$> t :: Delayed Pat)

pyon_mkVarP var ty = rethrowExceptionsInPython $ do
  v <- fromHsObject' var
  t <- fromHsObject' ty
  newHsObject $ (VarP v <$> t :: Delayed Pat)

pyon_mkTupleP pats = rethrowExceptionsInPython $ do
  ps <- fromListOfHsObject' pats
  newHsObject $ (TupleP <$> sequenceA ps :: Delayed Pat)

foreign export ccall pyon_mkVarE :: PyPtr -> IO PyPtr
foreign export ccall pyon_mkConE :: PyPtr -> IO PyPtr
foreign export ccall pyon_mkLitE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_mkUndefinedE :: PyPtr -> IO PyPtr
foreign export ccall pyon_mkTupleE :: PyPtr -> IO PyPtr
foreign export ccall pyon_mkTyAppE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_mkCallE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_mkIfE :: PyPtr -> PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_mkFunE :: PyPtr -> IO PyPtr
foreign export ccall pyon_mkLetE :: PyPtr -> PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_mkLetrecE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_mkDictE
  :: PyPtr -> PyPtr -> PyPtr -> PyPtr -> IO PyPtr
foreign export ccall pyon_mkMethodSelectE
  :: PyPtr -> PyPtr -> CInt -> PyPtr -> IO PyPtr

expHsObject :: Delayed Exp -> IO PyPtr
expHsObject = newHsObject

pyon_mkVarE var = rethrowExceptionsInPython $ do
  v <- fromHsObject' var
  expHsObject $ pure $ VarE defaultExpInfo v

pyon_mkConE con = rethrowExceptionsInPython $ do
  c <- fromHsObject' con
  expHsObject $ pure $ ConE defaultExpInfo c

pyon_mkLitE lit ty = rethrowExceptionsInPython $ do
  l <- fromHsObject' lit
  t <- fromHsObject' ty
  expHsObject $ LitE defaultExpInfo l <$> t

pyon_mkUndefinedE ty = rethrowExceptionsInPython $ do
  t <- fromHsObject' ty
  expHsObject $ UndefinedE defaultExpInfo <$> t

pyon_mkTupleE args = rethrowExceptionsInPython $ do
  hs_args <- fromListOfHsObject' args
  expHsObject $ TupleE defaultExpInfo <$> sequenceA hs_args

pyon_mkTyAppE oper ty = rethrowExceptionsInPython $ do
  e <- fromHsObject' oper
  t <- fromHsObject' ty
  expHsObject $ TyAppE defaultExpInfo <$> e <*> t

pyon_mkCallE oper args = rethrowExceptionsInPython $ do
  e <- fromHsObject' oper
  es <- fromListOfHsObject' args
  expHsObject $ CallE defaultExpInfo <$> e <*> sequenceA es

pyon_mkIfE oper true false = rethrowExceptionsInPython $ do
  e <- fromHsObject' oper
  t <- fromHsObject' true
  f <- fromHsObject' false
  expHsObject $ IfE defaultExpInfo <$> e <*> t <*> f

pyon_mkFunE fun = rethrowExceptionsInPython $ do
  f <- fromHsObject' fun
  expHsObject $ FunE defaultExpInfo <$> f

pyon_mkLetE pat rhs body = rethrowExceptionsInPython $ do
  p <- fromHsObject' pat
  e <- fromHsObject' rhs
  b <- fromHsObject' body
  expHsObject $ LetE defaultExpInfo <$> p <*> e <*> b

pyon_mkLetrecE defs body = rethrowExceptionsInPython $ do
  ds <- fromListOfHsObject' defs
  b <- fromHsObject' body
  expHsObject $ LetrecE defaultExpInfo <$> sequenceA ds <*> b

pyon_mkDictE cls ty superclasses methods = rethrowExceptionsInPython $ do
  c <- fromHsObject' cls
  t <- fromHsObject' ty
  scs <- fromListOfHsObject' superclasses
  ms <- fromListOfHsObject' methods
  expHsObject $ DictE defaultExpInfo c <$> t <*> sequenceA scs <*> sequenceA ms

pyon_mkMethodSelectE cls ty n exp = rethrowExceptionsInPython $ do
  c <- fromHsObject' cls
  t <- fromHsObject' ty
  e <- fromHsObject' exp
  expHsObject $ MethodSelectE defaultExpInfo <$> c <*> t <*> pure (fromIntegral n) <*> e

foreign export ccall pyon_mkFun :: PyPtr -> PyPtr -> PyPtr -> IO PyPtr

pyon_mkFun tyParams params body = rethrowExceptionsInPython $ do
  tps <- fromListOfHsObject' tyParams
  ps <- fromListOfHsObject' params
  e <- fromHsObject' body
  newHsObject $ (Fun <$> sequenceA tps <*> sequenceA ps <*> e :: Delayed Fun)

foreign export ccall pyon_mkDef :: PyPtr -> PyPtr -> IO PyPtr

pyon_mkDef defVar defFun = rethrowExceptionsInPython $ do
  d <- fromHsObject' defVar
  f <- fromHsObject' defFun
  newHsObject $ (Def d <$> f :: Delayed Def)

foreign export ccall pyon_makeAndEvaluateModule :: PyPtr -> IO PyPtr

pyon_makeAndEvaluateModule :: PyPtr -> IO PyPtr
pyon_makeAndEvaluateModule def_list = rethrowExceptionsInPython $ do
  defs <- fromListOfHsObject' def_list
  real_defs <- mapM force defs
  newHsObject $ Module real_defs
  
-------------------------------------------------------------------------------
-- Exported predicates.

foreign export ccall pyon_isExp :: PyPtr -> IO Bool

pyon_isExp :: PyPtr -> IO Bool
pyon_isExp ptr = do
  type_rep <- hsObjectType ptr
  return $ type_rep == typeOf (undefined :: Delayed Exp)

-------------------------------------------------------------------------------
-- Other exported functions.

foreign export ccall pyon_printModule :: PyPtr -> IO PyPtr
foreign export ccall pyon_optimizeModule :: PyPtr -> IO PyPtr

pyon_printModule :: PyPtr -> IO PyPtr
pyon_printModule mod = rethrowExceptionsInPython $ do
  m <- fromHsObject' mod
  print $ pprModule m
  pyNone

pyon_optimizeModule :: PyPtr -> IO PyPtr
pyon_optimizeModule mod = rethrowExceptionsInPython $ do
  m <- fromHsObject' mod
  newHsObject $ optimizeModule m
