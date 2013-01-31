
module CParser2.Driver(parseCoreModule2)
where

import qualified Data.Map as Map
import System.FilePath
import System.IO

import Common.Error
import Common.SourcePos
import Common.Identifier
import Common.Label
import Builtins.Builtins
import Builtins.TypeFunctions
import qualified SystemF.Syntax as SystemF
import qualified SystemF.MemoryIR as SystemF
import Type.Var
import Type.Type
import Type.Environment
import CParser2.AST
import CParser2.Lexer
import CParser2.Parser
import CParser2.Resolve
import CParser2.GenCode2
import Paths
import GlobalVar
import Globals

predefinedVarDetails :: [(String, Var)]
predefinedVarDetails =
  [(name v, v) | v <- [valV, boxV, bareV, outV, intindexV, initV,
                       initConV, outPtrV, storeV, posInftyV, negInftyV,
                       arrV, intV, uintV, floatV]]
  where
    name v =
      case varName v
      of Just lab ->
           case labelLocalName lab
           of Left name -> name
              _ -> internalError "Unnamed predefined variable"
         _ -> internalError "Unnamed predefined variable"

-- | Parse the built-in module.
--
--   Create a type environment containing variable, type function, 
--   and data type definitions.  The type environment contains specification
--   types and memory types.  Also, create a module containing
--   definitions of built-in functions and constants.
parseCoreModule2 :: IdentSupply Var
                 -> IO (TypeEnv, SpecTypeEnv, TypeEnv,
                        SystemF.Module SystemF.Mem, Map.Map String Var)
parseCoreModule2 ident_supply = do
  pathname <- getDataFileName ("symbols" </> "coremodule")
  input_file <- readFile pathname

  -- Parse file
  let input_tokens = lexify pathname input_file
  parsed_ast <- parseFile pathname input_tokens

  -- Resolve names
  let modname = ModuleName $ takeBaseName pathname
      resolve_env = globalEnvironment predefinedVarDetails
  resolved_ast <- resolveModule ident_supply resolve_env modname parsed_ast

  -- Convert to core expressions
  createCoreModule ident_supply resolved_ast

