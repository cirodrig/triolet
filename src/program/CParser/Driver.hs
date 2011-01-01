
module CParser.Driver(ConTable, parseCoreModule)
where

import System.FilePath
import System.IO

import Gluon.Common.Error
import Gluon.Common.Label
import Gluon.Common.SourcePos
import Gluon.Common.Identifier
import qualified Gluon.Core as Gluon
import SystemF.Builtins
import Core.Syntax
import CParser.AST
import CParser.Lexer
import CParser.Parser
import CParser.Resolve
import CParser.LevelInference
import CParser.GenCore
import Paths

predefinedVarDetails :: [(String, VarDetails)]
predefinedVarDetails =
  [(varNameString $ Gluon.varName v, PredefinedVar v) | v <- vars] ++
  [(labelUnqualifiedName $ Gluon.conName c, PredefinedCon c) | c <- cons] ++
  [ ("Pure", PredefinedKind Gluon.PureKind)
  , ("Effect", PredefinedKind Gluon.EffectKind)
  ]
  where
    varNameString (Just l) = labelUnqualifiedName l
    varNameString Nothing = internalError "parseCoreModule: Variable has no name"
    vars = []
    cons = [ pyonBuiltin the_passConv_int
           , pyonBuiltin the_passConv_float
           , pyonBuiltin the_passConv_owned
           , pyonBuiltin the_passConv_iter
           , pyonBuiltin the_passConv_list
           , pyonBuiltin the_OpaqueTraversableDict_list
           ]

parseCoreModule :: IdentSupply Gluon.Var -> IO ConTable
parseCoreModule ident_supply = do
  pathname <- getDataFileName ("symbols" </> "coretypes")
  input_file <- readFile pathname
  
  -- Parse file
  let input_tokens = lexify pathname input_file
  parsed_ast <- parseFile pathname input_tokens

  -- Resolve names
  let modname = moduleName $ takeBaseName pathname
  resolve_env <- globalEnvironment ident_supply predefinedVarDetails
  resolved_ast <- resolveModule ident_supply resolve_env modname parsed_ast
  
  -- Compute levels
  level_ast <- levelInferModule resolved_ast

  -- Convert to core expressions
  return $ createCoreTable level_ast
