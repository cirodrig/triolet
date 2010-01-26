-- | Gluon functions and constants that are exported for use in Python.

{-# LANGUAGE ForeignFunctionInterface #-}

module PythonInterface.Gluon where

import Foreign.C.Types
import Foreign.C.String

import Gluon.Common.SourcePos
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Core

import Python
import PythonInterface.HsObject
import GluonBackend

foreign export ccall gluon_loadBuiltins :: IO PyPtr

gluon_loadBuiltins = rethrowExceptionsInPython $ do
  loadBuiltins
  pyNone

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

foreign export ccall gluon_mkAnonymousVariable :: CInt -> PyPtr -> IO PyPtr

gluon_mkAnonymousVariable id lv = rethrowExceptionsInPython $ do
  let hs_id = toIdent $ fromIntegral id
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
foreign export ccall gluon_mkLamE :: PyPtr -> PyPtr -> PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkFunE :: PyPtr -> Int -> PyPtr -> PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkArrowE :: PyPtr -> Int -> PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkVarE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkConE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkTupE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkTupTyE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkLitE :: PyPtr -> PyPtr -> IO PyPtr
foreign export ccall gluon_mkInternalIntLitE :: CInt -> IO PyPtr

gluon_mkAppE pos operator arguments = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_operator <- fromHsObject' operator
  hs_arguments <- fromListOfHsObject' arguments
  newHsObject (mkAppE hs_pos hs_operator hs_arguments :: Exp Core)

gluon_mkLamE pos var ty body = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_var <- fromHsObject' var
  hs_ty <- fromHsObject' ty
  hs_body <- fromHsObject' body
  newHsObject (mkLamE hs_pos hs_var hs_ty hs_body :: Exp Core)

gluon_mkFunE pos isLin var dom rng = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  let hs_isLin = isLin /= 0
  hs_var <- fromHsObject' var
  hs_dom <- fromHsObject' dom
  hs_rng <- fromHsObject' rng
  newHsObject (mkFunE hs_pos hs_isLin hs_var hs_dom hs_rng :: Exp Core)

gluon_mkArrowE pos isLin dom rng = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  let hs_isLin = isLin /= 0
  hs_dom <- fromHsObject' dom
  hs_rng <- fromHsObject' rng
  newHsObject (mkArrowE hs_pos hs_isLin hs_dom hs_rng :: Exp Core)

gluon_mkVarE pos v = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_v <- fromHsObject' v
  newHsObject (mkVarE hs_pos hs_v :: Exp Core)

gluon_mkConE pos c = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_c <- fromHsObject' c
  newHsObject (mkConE hs_pos hs_c :: Exp Core)

gluon_mkTupE pos t = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_t <- fromHsObject' t
  newHsObject (mkTupE hs_pos hs_t :: Exp Core)

gluon_mkTupTyE pos t = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_t <- fromHsObject' t
  newHsObject (mkTupTyE hs_pos hs_t :: Exp Core)

gluon_mkLitE pos t = rethrowExceptionsInPython $ do
  hs_pos <- fromHsObject' pos
  hs_t <- fromHsObject' t
  newHsObject (mkLitE hs_pos hs_t :: Exp Core)

gluon_mkInternalIntLitE n = rethrowExceptionsInPython $ do
  newHsObject (mkInternalIntLitE (fromIntegral n) :: Exp Core)

foreign export ccall gluon_Tuple_Core_cons :: PyPtr -> PyPtr -> IO PyPtr

gluon_Tuple_Core_cons param tail = rethrowExceptionsInPython $ do
  hs_param <- fromHsObject' param
  hs_tail <- fromHsObject' tail
  newHsObject (hs_param :&: hs_tail :: Tuple Core)

foreign export ccall gluon_Tuple_Core_nil :: IO PyPtr

gluon_Tuple_Core_nil = newHsObject (Nil :: Tuple Core)

foreign export ccall gluon_Prod_Core_cons :: PyPtr -> PyPtr -> IO PyPtr

gluon_Prod_Core_cons param tail = rethrowExceptionsInPython $ do
  hs_param <- fromHsObject' param
  hs_tail <- fromHsObject' tail
  newHsObject (hs_param :*: hs_tail :: Prod Core)

foreign export ccall gluon_Prod_Core_nil :: IO PyPtr

gluon_Prod_Core_nil = newHsObject (Unit :: Prod Core)