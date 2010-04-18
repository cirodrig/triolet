
{-# LANGUAGE TemplateHaskell #-}
module Pyon.Untyped.Builtins where

import Control.Concurrent.MVar
import Control.Monad
import Language.Haskell.TH
import System.IO.Unsafe

import Gluon.Common.THRecord
import Gluon.Common.Label
import Gluon.Core(mkInternalConE)
import Pyon.Untyped.BuiltinsTH
import Pyon.Untyped.HMType
import Pyon.Untyped.Syntax

$(do d <- declareRecord tiBuiltinSpecification
     return [d])

$(declareFieldReaders tiBuiltinSpecification "the")

tiBuiltin :: (TIBuiltins -> a) -> a
tiBuiltin f = unsafePerformIO $ do
  is_empty <- isEmptyMVar the_TIBuiltins
  when is_empty $ fail "TI builtins have not been initialized"
  
  bi <- readMVar the_TIBuiltins
  return $! f bi

the_TIBuiltins :: MVar TIBuiltins
{-# NOINLINE the_TIBuiltins #-}
the_TIBuiltins = unsafePerformIO newEmptyMVar

builtinTypes :: [TyCon]
builtinTypes = $(listE [[| tiBuiltin $(varE $ mkName ("_con_" ++ name)) |] 
                       | name <- pyonSourceTypes ])
               
builtinGlobals :: [Variable]
builtinGlobals = $(listE [[| tiBuiltin $(varE $ mkName ('_':name)) |] 
                         | name <- pyonSourceGlobals ])

-- | The set of all built-in global variables, including those that cannot
-- be referenced directly in source code
allBuiltinGlobals :: [Variable]
allBuiltinGlobals = $(listE [[| tiBuiltin $(varE $ mkName ('_':name)) |] 
                         | name <- pyonSourceGlobals ++ pyonOtherGlobals ])
