
module CParser2.Driver(parseCoreModule, parseCoreFunctions)
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
import CParser2.GenCode
import CParser2.GenCore
import Paths
import GlobalVar
import Globals

predefinedVarDetails :: [(String, VarDetails)]
predefinedVarDetails =
  map mk_var_details (valV : boxV : bareV : outV : intindexV :
                      initV : propV :
                      posInftyV : negInftyV : allBuiltinVars)
  where
    mk_var_details v = (name, PredefinedVar v type_function)
      where
        name =
          case varName v
          of Just lab ->
               case labelLocalName lab
               of Left name -> name
                  _ -> internalError "Unnamed predefined variable"
             _ -> internalError "Unnamed predefined variable"
        
        type_function = Map.lookup v builtinTypeFunctions

-- | Parse the built-in type declarations.
--
--   Create a type environment and a module containing definitions of
--   built-in functions.
--   The function definitions are created after the type environment is
--   initialized.
parseCoreModule :: IdentSupply Var -> IO SpecTypeEnv
parseCoreModule ident_supply = do
  pathname <- getDataFileName ("symbols" </> "coretypes2")
  input_file <- readFile pathname
  
  -- Parse file
  let input_tokens = lexify pathname input_file
  parsed_ast <- parseFile pathname input_tokens

  -- Resolve names
  let modname = ModuleName $ takeBaseName pathname
      resolve_env = globalEnvironment predefinedVarDetails
  resolved_ast <- resolveModule ident_supply resolve_env modname parsed_ast

  -- Convert to core expressions
  return $ createCoreTable resolved_ast

-- | Parse the built-in function declarations.
--
--   The mem type environment should be passed as a parameter.
parseCoreFunctions :: IdentSupply Var -> TypeEnv
                   -> IO (SystemF.Module SystemF.Mem)
parseCoreFunctions ident_supply mem_types = do
  pathname <- getDataFileName ("symbols" </> "corecode")
  input_file <- readFile pathname
  
  -- Parse file
  let input_tokens = lexify pathname input_file
  parsed_ast <- parseFile pathname input_tokens

  -- Resolve names
  let modname = ModuleName $ takeBaseName pathname
      resolve_env = globalEnvironment predefinedVarDetails
  resolved_ast <- resolveModule ident_supply resolve_env modname parsed_ast

  -- Convert to core expressions
  createCoreFunctions ident_supply mem_types resolved_ast
