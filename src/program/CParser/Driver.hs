
module CParser.Driver(parseCoreModule)
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
import Type.Var
import Type.Type
import Type.Environment
import CParser.AST
import CParser.Lexer
import CParser.Parser
import CParser.Resolve
import CParser.LevelInference
import CParser.GenCore
import Paths
import GlobalVar
import Globals

import CParser.PrettyAST()

predefinedVarDetails :: [(String, VarDetails)]
predefinedVarDetails = map mk_var_details (pureV : intindexV : allBuiltinVars)
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

parseCoreModule :: IdentSupply Var -> IO TypeEnv
parseCoreModule ident_supply = do
  pathname <- getDataFileName ("symbols" </> "coretypes")
  input_file <- readFile pathname
  
  -- Parse file
  let input_tokens = lexify pathname input_file
  parsed_ast <- parseFile pathname input_tokens

  -- Resolve names
  let modname = ModuleName $ takeBaseName pathname
  resolve_env <- globalEnvironment ident_supply predefinedVarDetails
  resolved_ast <- resolveModule ident_supply resolve_env modname parsed_ast
  
  -- Compute levels
  level_ast <- levelInferModule resolved_ast

  -- Convert to core expressions
  return $ createCoreTable level_ast
