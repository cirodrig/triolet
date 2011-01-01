
module Globals where

import Gluon.Common.Supply
import Gluon.Common.Identifier
import Gluon.Core
import Gluon.Core.Module
import qualified SystemF.Syntax as SystemF
import qualified CParser.Driver as CParser
import qualified LowLevel.Syntax as LowLevel
import GlobalVar

the_nextParserVarID :: StaticGlobalVar Int
{-# NOINLINE the_nextParserVarID #-}
the_nextParserVarID = defineStaticGlobalVar $ return 0

the_nextSSAVarID :: StaticGlobalVar Int
{-# NOINLINE the_nextSSAVarID #-}
the_nextSSAVarID = defineStaticGlobalVar $ return 0

the_varIdentSupply :: StaticGlobalVar (Supply (Ident Var))
{-# NOINLINE the_varIdentSupply #-}
the_varIdentSupply = defineStaticGlobalVar newIdentSupply

the_conIdentSupply :: StaticGlobalVar (Supply (Ident Con))
{-# NOINLINE the_conIdentSupply #-}
the_conIdentSupply = defineStaticGlobalVar newIdentSupply

the_llVarIdentSupply :: StaticGlobalVar (Supply (Ident LowLevel.Var))
{-# NOINLINE the_llVarIdentSupply #-}
the_llVarIdentSupply = defineStaticGlobalVar newIdentSupply

-- | The Gluon builtin module.  This starts out empty, and is written
-- when the module is loaded.
the_builtinModule :: InitGlobalVar (Module ())
{-# NOINLINE the_builtinModule #-}
the_builtinModule = defineInitGlobalVar ()

-- | The types of Core terms.
the_coreTypes :: InitGlobalVar (CParser.ConTable)
{-# NOINLINE the_coreTypes #-}
the_coreTypes = defineInitGlobalVar ()

withTheVarIdentSupply :: (Supply (Ident Var) -> IO a) -> IO a
withTheVarIdentSupply f = withStaticGlobalVar the_varIdentSupply f

withTheConIdentSupply :: (Supply (Ident Con) -> IO a) -> IO a
withTheConIdentSupply f = withStaticGlobalVar the_conIdentSupply f

withTheLLVarIdentSupply :: (Supply (Ident LowLevel.Var) -> IO a) -> IO a
withTheLLVarIdentSupply f = withStaticGlobalVar the_llVarIdentSupply f

getNextVarIdent :: IO (Ident Var)
getNextVarIdent = withTheVarIdentSupply supplyValue

-- setNextVarIdent :: Ident Var -> IO ()
-- setNextVarIdent ident =
--   let last = toIdent $ pred $ fromIdent ident
--   in do swapMVar the_varIdentSupply =<< newIdentSupplyAfter last
--         return ()

getNextConIdent :: IO (Ident Con)
getNextConIdent = withTheConIdentSupply supplyValue

-- setNextConIdent :: Ident Con -> IO ()
-- setNextConIdent ident =
--   let last = toIdent $ pred $ fromIdent ident
--   in do swapMVar the_conIdentSupply =<< newIdentSupplyAfter last
--         return ()

-- -- Return True if builtins are loaded, False otherwise
-- checkBuiltinsStatus :: IO Bool
-- checkBuiltinsStatus = return . not =<< isEmptyMVar the_builtinModule

