
-- Profiling information for these functions is not useful
{-# OPTIONS_GHC -no-auto #-}
module Globals where

import qualified Data.Map as Map
import Data.IORef

import Common.Supply
import Common.Identifier
import qualified Untyped.TIMonad as Untyped
import qualified SystemF.Syntax as SystemF
import qualified SystemF.Datatypes.TypeLayout as SystemF
import qualified SystemF.MemoryIR as SystemF
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

-- | The types used by the frontend type inference engine.
the_TITypes :: InitGlobalVar Untyped.Environment
{-# NOINLINE the_TITypes #-}
the_TITypes = defineInitGlobalVar () 

-- | The types of System F terms.
the_systemFTypes :: InitGlobalVar Type.Environment.TypeEnv
{-# NOINLINE the_systemFTypes #-}
the_systemFTypes = defineInitGlobalVar ()

-- | The types of Core terms.  This variable is going to go away.
the_newCoreTypes :: InitGlobalVar Type.Environment.TypeEnv
{-# NOINLINE the_newCoreTypes #-}
the_newCoreTypes = defineInitGlobalVar ()

-- | The types of explicit-memory terms.
the_memTypes :: InitGlobalVar Type.Environment.TypeEnv
{-# NOINLINE the_memTypes #-}
the_memTypes = defineInitGlobalVar ()

-- | The specification types of global variables.
--   Replaces functionality formerly provided by 'the_newCoreTypes'.
the_specTypes :: InitGlobalVar Type.Environment.SpecTypeEnv
{-# NOINLINE the_specTypes #-}
the_specTypes = defineInitGlobalVar ()

-- | Definitions of some built-in functions.
the_coreModule :: InitGlobalVar (SystemF.Module SystemF.Mem)
{-# NOINLINE the_coreModule #-}
the_coreModule = defineInitGlobalVar ()

-- | A map from builtin System F function variables 
--   to builtin low-level function variables
the_loweringMap :: InitGlobalVar (Map.Map Var LowLevel.Var)
{-# NOINLINE the_loweringMap #-}
the_loweringMap = defineInitGlobalVar ()

-- | Data type layout information for data types.
--   This information is generated from 'the_memTypes' during initialization.
the_layouts :: InitGlobalVar (Map.Map Var SystemF.TypeLayout)
{-# NOINLINE the_layouts #-}
the_layouts = defineInitGlobalVar ()

-- | Fuel, which controls how many transformations the optimizer performs.
--   Some transformations consume fuel.  When the fuel is decreased to zero,
--   transformations that would consume fuel are disabled.
--
--   A negative value represents unlimited fuel.
the_fuel :: InitGlobalVar (IORef Int)
{-# NOINLINE the_fuel #-}
the_fuel = defineInitGlobalVar ()

withTheNewVarIdentSupply :: (Supply (Ident Var) -> IO a) -> IO a
withTheNewVarIdentSupply f = readStaticGlobalVar the_newVarIdentSupply >>= f

withTheLLVarIdentSupply :: (Supply (Ident LowLevel.Var) -> IO a) -> IO a
withTheLLVarIdentSupply f = readStaticGlobalVar the_llVarIdentSupply >>= f

