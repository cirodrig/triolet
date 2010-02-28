-- | Gluon functions and constants that are exported for use in Python.

{-# LANGUAGE ForeignFunctionInterface #-}

module Pyon.Exports.Gluon() where

import Prelude hiding(catch)

import Control.Applicative
import Control.Exception
import Control.Monad
import Data.Traversable
import Data.Typeable
import Foreign.C.Types
import Foreign.C.String

import Gluon.Common.SourcePos
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Core

import PythonInterface.Python
import PythonInterface.HsObject
import Pyon.Globals
import Pyon.Exports.Delayed

-------------------------------------------------------------------------------
-- Constants

-- Helper function for exporting constants that may raise an exception
asGlobalObject :: Typeable a => a -> IO PyPtr
asGlobalObject = rethrowExceptionsInPython . newHsObject

foreign export ccall gluon_noSourcePos :: IO PyPtr

gluon_noSourcePos = newHsObject noSourcePos

foreign export ccall gluon_mkObjectLevel :: IO PyPtr
foreign export ccall gluon_mkTypeLevel :: IO PyPtr
foreign export ccall gluon_mkKindLevel :: IO PyPtr
foreign export ccall gluon_mkSortLevel :: IO PyPtr

gluon_mkObjectLevel = newHsObject ObjectLevel
gluon_mkTypeLevel = newHsObject TypeLevel
gluon_mkKindLevel = newHsObject KindLevel
gluon_mkSortLevel = newHsObject SortLevel

foreign export ccall gluon_con_Int :: IO PyPtr
foreign export ccall gluon_con_Float :: IO PyPtr
foreign export ccall gluon_type_Pure :: IO PyPtr
foreign export ccall gluon_con_EmpE :: IO PyPtr

gluon_con_Int = asGlobalObject $ builtin the_Int
gluon_con_Float = asGlobalObject $ builtin the_Float
gluon_type_Pure = asGlobalObject (pure pureKindE :: Delayed (Exp Core))
gluon_con_EmpE = asGlobalObject $ builtin the_EmpE

-------------------------------------------------------------------------------
-- Constructors

foreign export ccall gluon_delayedType :: PyPtr -> IO PyPtr

-- Take a Python callable object that returns an Exp, and wrap it in a
-- delayed object.
-- Since a pointer to the object is retained, use a ForeignPtr to manage its
-- reference count.
gluon_delayedType :: PyPtr -> IO PyPtr
gluon_delayedType callback = do
  callback_ref <- toPyRef callback
  newHsObject $ Unevaluated (runCallback callback_ref)
  where
    runCallback :: PyRef -> IO (Exp Core)
    runCallback callback_ref =
      withPyRef callback_ref $ force <=< fromHsObject' <=< call0

foreign export ccall gluon_pgmLabel :: CString -> CString -> IO PyPtr

gluon_pgmLabel mod_name_ptr name_ptr = rethrowExceptionsInPython $ do
  mod_name <- peekCString mod_name_ptr 
  name <- peekCString name_ptr
  newHsObject $ pgmLabel (moduleName mod_name) name

foreign export ccall gluon_mkVariable :: CInt -> PyPtr -> PyPtr -> IO PyPtr

gluon_mkVariable id label lv = rethrowExceptionsInPython $ do
  let hs_id = toIdent $ fromIntegral id
  hs_label <- fromHsObject' label
  hs_lv <- fromHsObject' lv
  newHsObject $ mkVariable hs_id hs_label hs_lv

foreign export ccall gluon_mkNewVariable :: PyPtr -> PyPtr -> IO PyPtr

gluon_mkNewVariable label lv = rethrowExceptionsInPython $ do
  id <- getNextVarIdent
  hs_label <- fromHsObject' label
  hs_lv <- fromHsObject' lv
  newHsObject $ mkVariable id hs_label hs_lv

foreign export ccall gluon_mkAnonymousVariable :: CInt -> PyPtr -> IO PyPtr

gluon_mkAnonymousVariable id lv = rethrowExceptionsInPython $ do
  let hs_id = toIdent $ fromIntegral id
  hs_lv <- fromHsObject' lv
  newHsObject $ mkAnonymousVariable hs_id hs_lv

foreign export ccall gluon_mkNewAnonymousVariable :: PyPtr -> IO PyPtr

gluon_mkNewAnonymousVariable lv = rethrowExceptionsInPython $ do
  hs_id <- getNextVarIdent
  hs_lv <- fromHsObject' lv
  newHsObject $ mkAnonymousVariable hs_id hs_lv

-- * Core syntax

foreign export ccall gluon_Binder_plain :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_Binder2_plain :: PyPtr -> PyPtr -> IO PyPtr

gluon_Binder_plain var ty = rethrowExceptionsInPython $ do
  hs_var <- fromHsObject' var
  hs_ty <- fromHsObject' ty
  newHsObject (Binder hs_var hs_ty () :: Binder Core ())

gluon_Binder2_plain var ty = rethrowExceptionsInPython $ do
  hs_var <- fromMaybeHsObject' var
  hs_ty <- fromHsObject' ty
  newHsObject (Binder' hs_var hs_ty () :: Binder' Core ())

foreign export ccall gluon_mkAppE :: PyPtr -> PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkConAppE :: PyPtr -> PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkLamE :: PyPtr -> PyPtr -> PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkFunE :: PyPtr -> Int -> PyPtr -> PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkArrowE :: PyPtr -> Int -> PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkVarE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkConE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkTupE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkTupTyE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkLitE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkInternalIntLitE :: CInt -> IO PyPtr

expHsObject :: Delayed (Exp Core) -> IO PyPtr
expHsObject = newHsObject

gluon_mkAppE pos operator arguments = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_operator <- fromHsObject' operator
  hs_arguments <- fromListOfHsObject' arguments
  expHsObject $ mkAppE hs_pos <$> hs_operator <*> sequenceA hs_arguments

gluon_mkConAppE pos operator arguments = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_operator <- fromHsObject' operator
  hs_arguments <- fromListOfHsObject' arguments
  expHsObject $ mkConAppE hs_pos hs_operator <$> sequenceA hs_arguments

gluon_mkLamE pos var ty body = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_var <- fromHsObject' var
  hs_ty <- fromHsObject' ty
  hs_body <- fromHsObject' body
  expHsObject $ mkLamE hs_pos hs_var <$> hs_ty <*> hs_body

gluon_mkFunE pos isLin var dom rng = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  let hs_isLin = isLin /= 0
  hs_var <- fromHsObject' var
  hs_dom <- fromHsObject' dom
  hs_rng <- fromHsObject' rng
  expHsObject $ mkFunE hs_pos hs_isLin hs_var <$> hs_dom <*> hs_rng

gluon_mkArrowE pos isLin dom rng = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  let hs_isLin = isLin /= 0
  hs_dom <- fromHsObject' dom
  hs_rng <- fromHsObject' rng
  expHsObject $ mkArrowE hs_pos hs_isLin <$> hs_dom <*> hs_rng

gluon_mkVarE pos v = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_v <- fromHsObject' v
  expHsObject $ pure $ mkVarE hs_pos hs_v

gluon_mkConE pos c = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_c <- fromHsObject' c
  expHsObject $ pure $ mkConE hs_pos hs_c

gluon_mkTupE pos t = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_t <- fromHsObject' t
  expHsObject $ mkTupE hs_pos <$> hs_t

gluon_mkTupTyE pos t = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_t <- fromHsObject' t
  expHsObject $ mkTupTyE hs_pos <$> hs_t

gluon_mkLitE pos t = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_t <- fromHsObject' t
  expHsObject $ mkLitE hs_pos <$> hs_t

gluon_mkInternalIntLitE n = rethrowExceptionsInPython $ do
  expHsObject $ pure $ mkInternalIntLitE (fromIntegral n)

foreign export ccall gluon_Tuple_Core_cons :: PyPtr -> PyPtr -> IO PyPtr

gluon_Tuple_Core_cons param tail = rethrowExceptionsInPython $ do
  hs_param <- fromHsObject' param
  hs_tail <- fromHsObject' tail
  newHsObject (hs_param :&: hs_tail :: Tuple Core)

foreign export ccall gluon_Tuple_Core_nil :: IO PyPtr

gluon_Tuple_Core_nil = newHsObject (Nil :: Tuple Core)

foreign export ccall gluon_Sum_Core_cons :: PyPtr -> PyPtr -> IO PyPtr

gluon_Sum_Core_cons param tail = rethrowExceptionsInPython $ do
  hs_param <- fromHsObject' param
  hs_tail <- fromHsObject' tail
  newHsObject (hs_param :*: hs_tail :: Sum Core)

foreign export ccall gluon_Sum_Core_nil :: IO PyPtr

gluon_Sum_Core_nil = newHsObject (Unit :: Sum Core)

-------------------------------------------------------------------------------
-- Predicates
-- These functions return nonzero for 'True', zero for 'False'.

test :: IO a -> (a -> Bool) -> IO Bool
m `test` f = return . f =<< m

testJust :: IO (Maybe a) -> (a -> Bool) -> IO Bool
m `testJust` f = m `test` maybe False f

foreign export ccall gluon_isExp :: PyPtr -> IO Bool

gluon_isExp p = do
  t <- hsObjectType p 
  return $ t == typeOf (undefined :: Delayed CExp)

-------------------------------------------------------------------------------
-- Other functions

foreign export ccall gluon_loadBuiltins :: IO Bool

-- Perform initialization by loading builtin modules.
-- Return nonzero on success, 0 otherwise.
gluon_loadBuiltins =
  (loadBuiltins >> return True) `catch` printExceptionAndReturn
    where
      printExceptionAndReturn e = do
        print (e :: SomeException)
        return False

foreign export ccall gluon_builtinsLoaded :: IO Bool
gluon_builtinsLoaded = checkBuiltinsStatus
