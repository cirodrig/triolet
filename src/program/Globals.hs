
module Globals where

import qualified Data.Map as Map
import Common.Supply
import Common.Identifier
import qualified SystemF.Syntax as SystemF
import qualified LowLevel.Syntax as LowLevel
import GlobalVar
import Type.Environment
import Type.Type

the_nextParserVarID :: StaticGlobalVar Int
{-# NOINLINE the_nextParserVarID #-}
the_nextParserVarID = defineStaticGlobalVar $ return 0

the_nextSSAVarID :: StaticGlobalVar Int
{-# NOINLINE the_nextSSAVarID #-}
the_nextSSAVarID = defineStaticGlobalVar $ return 0

-- | This will eventually replace 'the_varIdentSupply'
the_newVarIdentSupply :: StaticGlobalVar (Supply (Ident Var))
{-# NOINLINE the_newVarIdentSupply #-}
the_newVarIdentSupply =
  defineStaticGlobalVar (newIdentSupplyAfter Type.Type.firstAvailableVarID)

the_llVarIdentSupply :: StaticGlobalVar (Supply (Ident LowLevel.Var))
{-# NOINLINE the_llVarIdentSupply #-}
the_llVarIdentSupply = defineStaticGlobalVar newIdentSupply

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

-- | The specification types of global variables.
--   Replaces functionality formerly provided by 'the_newCoreTypes'.
the_specTypes :: InitGlobalVar Type.Environment.TypeEnv
{-# NOINLINE the_specTypes #-}
the_specTypes = defineInitGlobalVar ()

-- | A map from builtin System F function variables 
--   to builtin low-level function variables
the_loweringMap :: InitGlobalVar (Map.Map Var LowLevel.Var)
{-# NOINLINE the_loweringMap #-}
the_loweringMap = defineInitGlobalVar ()

withTheNewVarIdentSupply :: (Supply (Ident Var) -> IO a) -> IO a
withTheNewVarIdentSupply f = withStaticGlobalVar the_newVarIdentSupply f

withTheLLVarIdentSupply :: (Supply (Ident LowLevel.Var) -> IO a) -> IO a
withTheLLVarIdentSupply f = withStaticGlobalVar the_llVarIdentSupply f

