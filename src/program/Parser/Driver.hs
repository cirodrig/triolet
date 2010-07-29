-- The parser driver.  This exports a function to be called via C.
-- The driver function takes a filename, reads the file, and returns a
-- Python object.

{-# LANGUAGE ForeignFunctionInterface #-}
module Parser.Driver(parserGlobals, parseFile) where

import Control.Monad
import System.IO
import Parser.Parser
import Parser.ParserSyntax
import Parser.SSA
import Parser.GenUntyped
import Untyped.Syntax
import Untyped.Data(ParserVarBinding)
import Globals
import GlobalVar

-- | The Pyon global variables recognized by the parser.
parserGlobals :: InitGlobalVar [(Var Int, ParserVarBinding)]
{-# NOINLINE parserGlobals #-}
parserGlobals = defineInitGlobalVar ()

ssaGlobals :: [(SSAVar, ParserVarBinding)]
ssaGlobals =
  [(predefinedSSAVar v, b) | (v, b) <- readInitGlobalVar parserGlobals]

-- | Parse a file.  Generates an untyped module.
parseFile :: FilePath -> IO Untyped.Syntax.Module
parseFile file_path = do
  -- Read the file
  text <- readFile file_path

  -- Parse and generate an AST
  pglobals <- readInitGlobalVarIO parserGlobals
  (nextStm, parse_mod) <-
    modifyStaticGlobalVar the_nextParserVarID $ \nextID -> do
      mast <- parseModule text file_path (map fst pglobals) nextID
      case mast of
        Left errs -> do
          mapM_ putStrLn errs  
          fail "Parsing failed" 
        Right (nextStm, nextID', mod) ->
          return (nextID', (nextStm, mod))

  -- Generate SSA form
  ssa_mod <-
    modifyStaticGlobalVar the_nextSSAVarID $ \nextSSAID -> do
      modifyStaticGlobalVar the_nextParserVarID $ \nextID -> do
        (nextStm', nextID', nextSSAID', ssa_mod) <-
          computeSSA nextStm nextID nextSSAID pglobals parse_mod
        return (nextID', (nextSSAID', ssa_mod))

  -- Convert to untyped functional form
  untyped_mod <- convertToUntyped ssaGlobals ssa_mod

  return untyped_mod
