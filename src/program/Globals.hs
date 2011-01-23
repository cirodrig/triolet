
module Globals where

import qualified Data.Map as Map
import Gluon.Common.Supply
import Gluon.Common.Identifier
import Gluon.Core
import Gluon.Core.Module
import qualified SystemF.Syntax as SystemF
import qualified CParser.Driver as CParser
import qualified CParser2.Driver as CParser2
import qualified LowLevel.Syntax as LowLevel
import GlobalVar
import qualified Type.Environment
import qualified Type.Type
import qualified Type.Var

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

-- | This will eventually replace 'the_varIdentSupply'
the_newVarIdentSupply :: StaticGlobalVar (Supply (Ident Type.Var.Var))
{-# NOINLINE the_newVarIdentSupply #-}
the_newVarIdentSupply =
  defineStaticGlobalVar (newIdentSupplyAfter Type.Type.firstAvailableVarID)

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

-- | The types of System F terms.
the_systemFTypes :: InitGlobalVar Type.Environment.TypeEnv
{-# NOINLINE the_systemFTypes #-}
the_systemFTypes = defineInitGlobalVar ()

-- | The types of Core terms.
the_newCoreTypes :: InitGlobalVar Type.Environment.TypeEnv
{-# NOINLINE the_newCoreTypes #-}
the_newCoreTypes = defineInitGlobalVar ()

-- | The types of explicit-memory terms.
the_memTypes :: InitGlobalVar Type.Environment.TypeEnv
{-# NOINLINE the_memTypes #-}
the_memTypes = defineInitGlobalVar ()

-- | A map from builtin System F function variables 
--   to builtin low-level function variables
the_loweringMap :: InitGlobalVar (Map.Map Type.Var.Var LowLevel.Var)
{-# NOINLINE the_loweringMap #-}
the_loweringMap = defineInitGlobalVar ()

withTheVarIdentSupply :: (Supply (Ident Var) -> IO a) -> IO a
withTheVarIdentSupply f = withStaticGlobalVar the_varIdentSupply f

withTheConIdentSupply :: (Supply (Ident Con) -> IO a) -> IO a
withTheConIdentSupply f = withStaticGlobalVar the_conIdentSupply f

withTheNewVarIdentSupply :: (Supply (Ident Type.Var.Var) -> IO a) -> IO a
withTheNewVarIdentSupply f = withStaticGlobalVar the_newVarIdentSupply f

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

