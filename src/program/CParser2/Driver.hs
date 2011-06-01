
module CParser2.Driver(parseCoreModule)
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
import CParser2.AST
import CParser2.Lexer
import CParser2.Parser
import CParser2.Resolve
import CParser2.GenCore
import Paths
import GlobalVar
import Globals

predefinedVarDetails :: [(String, VarDetails)]
predefinedVarDetails =
  map mk_var_details (valV : boxV : bareV : outV : intindexV : sideeffectV :
                      writeV :
                      posInftyV : allBuiltinVars)
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
