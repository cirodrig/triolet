
module Parser.MakeCFG(buildControlFlow) where

import Compiler.Hoopl

import Common.SourcePos
import Common.Supply
import Unsafe.Coerce

import Parser.ParserSyntax(Loc(..), unLoc, AST,
                           Var(..), PVar, VarID,
                           Literal(..), Expr(..), LExpr, Parameter(..),
                           Annotation, Slice(..),
                           IterFor(..), IterIf(..), IterLet(..),
                           Comprehension(..),
                           ForallAnnotation)
import qualified Parser.ParserSyntax as PS
import qualified Parser.Control as CF

-------------------------------------------------------------------------------

data NameSupply = NameSupply
                  { labelSupply :: !(Supply Int)
                  }

newtype M a = M {unM :: NameSupply -> IO a}

instance Monad M where
  return x = M (\_ -> return x)
  M m >>= k = M (\e -> m e >>= \x -> unM (k x) e)

instance UniqueMonad M where
  freshUnique = M $ \s -> do
    n <- supplyValue $ labelSupply s
    return $ intToUnique n

-- | An expression that returns the constant 'None'
returnNone :: SourcePos -> CF.CFG AST O C
returnNone pos = mkLast $ CF.lStmt pos $ CF.Return none_exp
  where
    none_exp = Loc noSourcePos $ PS.Literal PS.NoneLit

-- | Create a control flow target.  Targets appear at the entry point of
--   a basic block.
mkTarget :: SourcePos -> M (Label, CF.CFG AST C O)
mkTarget pos = do
  l <- freshLabel
  let n = mkFirst $ CF.lStmt pos $ CF.Target l Nothing
  return (l, n)

mkControlFlowGraph :: SourcePos     -- ^ Location of the CFG's entry point
                   -> CF.CFG AST O C -- ^ Continuation to execute on
                                    --   the suite's fallthrough path
                   -> PS.Suite
                   -> M (Label, CF.CFG AST C C)
mkControlFlowGraph pos continuation ss = do
  (e, target) <- mkTarget pos
  cfg <- mkTail continuation ss
  return (e, target <*> cfg)

mkTail :: CF.CFG AST O C         -- ^ Continuation to execute on the suite's 
                                --   fallthrough path
       -> PS.Suite              -- ^ Statements to translate
       -> M (CF.CFG AST O C)
mkTail continuation (s:ss) =
  case s
  of PS.ExprStmt {} -> mkTail continuation ss
     PS.Assign pos lhs rhs -> do
       continue $ mkMiddle $ CF.lStmt pos (CF.Assign lhs rhs)
     PS.Assert pos es -> do
       continue $ mkMiddle $ CF.lStmt pos (CF.Assert es)
     PS.Require pos v t -> do
       continue $ mkMiddle $ CF.lStmt pos (CF.Require v t)
     PS.If pos c t f -> do
       -- Fallthrough path
       (ft_entry, ft_graph) <- mkControlFlowGraph pos continuation ss
       let ft_stmt = mkLast $ CF.lStmt pos (CF.Jump (CF.noSSAFlow ft_entry))

       -- True, false paths
       if_graph <- mkIf pos ft_stmt c t f
       return $ if_graph |*><*| ft_graph
     PS.DefGroup pos defs -> do
       defs' <- mapM mkControlFlowFunction defs
       continue $ mkMiddle $ CF.lStmt pos (CF.DefGroup defs' Nothing)
     PS.Return pos e ->
       return $ mkLast $ CF.lStmt pos (CF.Return e)
  where
    -- Build a subgraph out of node 'n' and suite 'ss'
    continue n = do
      g <- mkTail continuation ss
      return $ n <*> g

mkTail continuation [] = return continuation

-- | Create an if-else branch in the CFG
mkIf :: SourcePos -> CF.CFG AST O C -> PS.LExpr AST
     -> PS.Suite -> PS.Suite -> M (CF.CFG AST O C)
mkIf pos continuation c t f = do
  -- True and false paths
  (t_entry, t_graph) <- mkControlFlowGraph pos continuation t
  (f_entry, f_graph) <- mkControlFlowGraph pos continuation f

  -- Create 'if' node and connect graph
  let t_flow = CF.noSSAFlow t_entry
  let f_flow = CF.noSSAFlow f_entry
  let if_stmt = mkLast $ CF.lStmt pos (CF.If c t_flow f_flow)
  return $ if_stmt |*><*| t_graph |*><*| f_graph

mkControlFlowFunction :: PS.LFunc AST -> M (CF.LCFunc AST)
mkControlFlowFunction (Loc pos f) = do
  (entry, body) <- mkControlFlowGraph pos (returnNone pos) $ PS.funcBody f
  return $ Loc pos $
    CF.CFunc { CF.cfSignature = PS.funcSignature f
             , CF.cfLivenesses = Nothing
             , CF.cfEntry = entry
             , CF.cfBody = body
             }

-- | Convert a function to control flow graph form
buildControlFlow :: PS.LFunc AST -> IO (CF.LCFunc AST)
buildControlFlow f = do
  -- Create a new set of int IDs for this function
  supply1 <- newSupply 0 (1+)
  let name_supply = NameSupply supply1

  -- Generate control flow graph
  unM (mkControlFlowFunction f) name_supply