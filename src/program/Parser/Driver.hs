-- The parser driver.  This exports a function to be called via C.
-- The driver function takes a filename, reads the file, and returns a
-- Python object.

{-# LANGUAGE ForeignFunctionInterface #-}
module Parser.Driver(parserGlobals, parseFile) where

import Control.Monad
import Data.IORef
import System.IO

import Common.Label
import qualified Parser.Control as CF
import qualified Parser.Dataflow as CF
import qualified Parser.GenUntyped2 as CF
import qualified Parser.SSA2 as CF
import qualified Parser.MakeCFG as CF
import Parser.Dataflow
import Parser.Parser
import Parser.ParserSyntax
import Untyped.Syntax
import Untyped.Data(ParserVarBinding(..))
import Globals
import GlobalVar

newtype Pipeline group group' export export' =
  Pipeline (IO (group -> IO group', export -> IO export', IO ()))

catPipeline :: Pipeline g  g'  e  e'
            -> Pipeline g' g'' e' e''
            -> Pipeline g  g'' e  e''
catPipeline (Pipeline f) (Pipeline g) = Pipeline $ do
  (f1, f2, f3) <- f
  (g1, g2, g3) <- g
  return (f1 >=> g1, f2 >=> g2, f3 >> g3)

runPipeline :: [g] -> [e] -> Pipeline g g' e e' -> IO ([g'], [e'])
runPipeline groups exports (Pipeline m) = do
  (do_group, do_export, do_finish) <- m
  groups' <- mapM do_group groups
  exports' <- mapM do_export exports
  do_finish
  return (groups', exports')

statelessPipeline :: (group -> IO group') -> (export -> IO export')
                  -> Pipeline group group' export export'
statelessPipeline f g = Pipeline $ return (f, g, return ())

controlFlowStage :: Pipeline [PFunc] [CF.LCFunc AST] (ExportItem AST) (ExportItem AST)
controlFlowStage = statelessPipeline (mapM do_func) do_export
  where
    do_func f = do f' <- CF.buildControlFlow f
                   let !(f'', _) = CF.analyzeLivenessInLFunc f'
                   return f''
    do_export e = return e

ssaStage :: Pipeline [CF.LCFunc AST] [CF.LCFunc CF.SSAID] (ExportItem AST) (ExportItem CF.SSAID)
ssaStage = Pipeline $ do
  id_supply <- CF.newSSAIDSupply
  scope_ref <- newIORef external_vars

  let withScope :: (CF.SSAScope -> IO (a, CF.SSAScope)) -> IO a
      withScope f = do
        s <- readIORef scope_ref
        (x, s') <- f s
        writeIORef scope_ref s'
        return x

  let do_group fs = withScope $ \scope -> do
        CF.ssaGlobalGroup id_supply scope fs
  let do_export e = withScope $ \scope -> do
        CF.ssaExportItem id_supply scope e

  return (do_group, do_export, return ())
  where
    -- Create an SSA scope containing externally defined variables
    external_vars =
      CF.externSSAScope $ map fst $ readInitGlobalVar parserGlobals

genUntypedStage :: Pipeline [CF.LCFunc CF.SSAID] DefGroup (ExportItem CF.SSAID) Export
genUntypedStage = Pipeline $ do
  scope_ref <- newIORef external_vars

  let withScope :: (CF.GenScope -> IO (a, CF.GenScope)) -> IO a
      withScope f =  do
        s <- readIORef scope_ref
        (x, s') <- f s
        writeIORef scope_ref s'
        return x

  let do_group fs =
        withScope $ \scope ->
        withTheNewVarIdentSupply $ \supply ->
        CF.genGroup supply scope fs
  let do_export e =
        withScope $ \scope ->
        withTheNewVarIdentSupply $ \supply ->
        CF.genExport supply scope e

  return (do_group, do_export, return ())  
  where
    -- Create an SSA scope containing externally defined variables
    external_vars =
      CF.externUntypedScope [(CF.externSSAVar v, b)
                            | (v, b) <- readInitGlobalVar parserGlobals]

generateCFG :: [[PFunc]] -> [ExportItem AST] -> IO ([DefGroup], [Export])
generateCFG fs es = do
  let pipeline =
        controlFlowStage `catPipeline` ssaStage `catPipeline` genUntypedStage
  runPipeline fs es pipeline

-- | The global variables recognized by the parser.
parserGlobals :: InitGlobalVar [(PVar, ParserVarBinding)]
{-# NOINLINE parserGlobals #-}
parserGlobals = defineInitGlobalVar ()

varBindingLevel :: ParserVarBinding -> Level
varBindingLevel (KindBinding _) = KindLevel
varBindingLevel (TypeBinding _) = TypeLevel
varBindingLevel (ObjectBinding _) = ValueLevel

-- | Parse a file.  Generates an untyped module.
parseFile :: FilePath -> String -> IO Untyped.Syntax.Module
parseFile file_path text = do
  pglobals <- readInitGlobalVarIO parserGlobals
  let predefined_vars :: [(PVar, Level)]
      predefined_vars = [(v, varBindingLevel b) | (v, b) <- pglobals]

  -- Parse and generate an AST
  parse_mod <-
    modifyStaticGlobalVar the_nextParserVarID $ \nextID -> do
      mast <- parseModule text file_path predefined_vars nextID
      case mast of
        Left errs -> do
          mapM_ putStrLn errs  
          fail "Parsing failed" 
        Right (nextID', mod) ->
          return (nextID', mod)

  -- Convert the AST to untyped expressions
  let Parser.ParserSyntax.Module module_name groups exports = parse_mod
  (groups', exports') <- generateCFG groups exports
  return $ Untyped.Syntax.Module (ModuleName module_name) groups' exports'
