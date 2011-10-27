
module SystemF.LoopRewrite(parallelLoopRewrite)
where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Monad hiding(mapM)
import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Data.Traversable

import Builtins.Builtins
import Common.Identifier
import SystemF.IncrementalSubstitution
import SystemF.ReprDict
import SystemF.MemoryIR
import SystemF.Syntax
import SystemF.Simplifier.Rewrite
import Type.Environment
import Type.Type
import Globals
import GlobalVar

-- | The number of loops enclosing the current context.
--
--   We count stream consumers and explicit looping operators as loops.
--   Stream producers are not counted as loops.
--
--   Loops are detected when we see an application of a known looping operator
--   to a lambda function that's the loop body.  Other loops are not counted.
data LoopNesting =
  LoopNesting
  { -- | Number of parallel loops around the current context
    parLoops :: {-#UNPACK#-}!Int
    -- | Number of other loops around the current context
  , otherLoops :: {-#UNPACK#-}!Int
  }

data LREnv =
  LREnv
  { loopNesting :: {-#UNPACK#-}!LoopNesting
  , typeEnv :: TypeEnv
  , dictEnv :: SingletonValueEnv
  , varSupply :: !(IdentSupply Var)
  }

modifyLoopNesting f env = env {loopNesting = f $ loopNesting env}

-- | During loop rewriting, keep track of the current loop nesting
type LRW a = ReaderT LREnv IO a

incParLoopCount m = local (modifyLoopNesting inc_count) m 
  where
    inc_count n = n {parLoops = 1 + parLoops n}

incOtherLoopCount m = local (modifyLoopNesting inc_count) m
  where
    inc_count n = n {otherLoops = 1 + otherLoops n}

parLoopOperator, otherLoopOperator :: Var -> Bool
parLoopOperator v =
  v `elem` [pyonBuiltin The_parallel_doall,
            pyonBuiltin The_parallel_doall2,
            pyonBuiltin The_blocked_reduce,
            pyonBuiltin The_blocked_doall,
            pyonBuiltin The_blocked_doall2,
            pyonBuiltin The_parallel_dim1_reduce,
            pyonBuiltin The_parallel_dim1_reduce1,
            pyonBuiltin The_parallel_dim1_generate,
            pyonBuiltin The_parallel_dim2_reduce,
            pyonBuiltin The_parallel_dim2_generate
           ] 
  
otherLoopOperator v =
  v `elem` [pyonBuiltin The_for,
            pyonBuiltin The_doall,
            pyonBuiltin The_histogram,
            pyonBuiltin The_histogramArray,
            pyonBuiltin The_fun_reduce,
            pyonBuiltin The_fun_reduce_Stream,
            pyonBuiltin The_fun_reduce1,
            pyonBuiltin The_fun_reduce1_Stream,
            pyonBuiltin The_TraversableDict_list_build,
            pyonBuiltin The_primitive_dim1_reduce,
            pyonBuiltin The_primitive_dim1_reduce1,
            pyonBuiltin The_primitive_dim1_generate,
            pyonBuiltin The_primitive_dim2_reduce,
            pyonBuiltin The_primitive_dim2_generate
            ]

-- | Use rewrite rules on an application
useRewriteRules :: ExpInfo -> Var -> [Type] -> [ExpM] -> LRW (Maybe ExpM)
useRewriteRules inf op_var ty_args args = ReaderT $ \env ->
  rewriteApp parallelizingRewrites (intIndexEnv (dictEnv env)) (varSupply env) (typeEnv env)
  inf op_var ty_args (map deferEmptySubstitution args)

-- | Replace a function application with a parallel function application
--   if possible.
--
--   The function must have a known parallel form, and it must be
--   applied to all input arguments (output arguments are not required).
replaceWithParallelApp :: ExpInfo -> Var -> [Type] -> [ExpM]
                       -> LRW (Maybe ExpM)
replaceWithParallelApp inf op_var ty_args args = ReaderT $ \env ->
  return $! do
    -- Look up the parallel equivalent of this operator
    parallel_op <- lookup op_var parallel_function_table

    -- Ensure that the operator is fully applied
    t <- lookupType parallel_op (typeEnv env)
    guard (fully_applied t)

    return $ new_expr parallel_op
  where
    new_expr parallel_op =
      let op = ExpM $ VarE inf parallel_op
      in appE inf op ty_args args

    -- Verify that the function is fully applied, except possibly for
    -- some missing output pointer parameters
    fully_applied ty =
      let (ty_binders, domain, _) = fromForallFunType ty
      in length ty_args == length ty_binders &&
         all is_out_ptr (drop (length args) domain)
      where
        -- True if 't' is an 'OutPtr' type
        is_out_ptr t =
          case fromVarApp t
          of Just (op, _) -> op `isPyonBuiltin` The_OutPtr
             _ -> False

    parallel_function_table =
      [ (pyonBuiltin The_primitive_dim1_reduce,
         pyonBuiltin The_parallel_dim1_reduce)
      , (pyonBuiltin The_primitive_dim1_reduce1,
         pyonBuiltin The_parallel_dim1_reduce1)
      , (pyonBuiltin The_primitive_dim1_generate,
         pyonBuiltin The_parallel_dim1_generate)
      , (pyonBuiltin The_primitive_dim2_generate,
         pyonBuiltin The_parallel_dim2_generate)
      , (pyonBuiltin The_primitive_dim2_reduce,
         pyonBuiltin The_parallel_dim2_reduce)
      , (pyonBuiltin The_doall,
         pyonBuiltin The_parallel_doall)
      ]

-------------------------------------------------------------------------------
-- Traversal

rwExp :: ExpM -> LRW ExpM
rwExp expression =
  case fromExpM expression
  of VarE {} -> return expression
     LitE {} -> return expression
     ConE inf op args -> ExpM <$> ConE inf op <$> mapM rwExp args
     AppE inf op ty_args args -> rwApp inf op ty_args args 
     LamE inf f -> ExpM <$> LamE inf <$> rwFun f
     LetE inf b rhs body -> ExpM <$> (LetE inf b <$> rwExp rhs <*> rwExp body)
     LetfunE inf defs body -> ExpM <$> (LetfunE inf <$> mapM rwDef defs <*> rwExp body)
     CaseE inf scr alts -> ExpM <$> (CaseE inf <$> rwExp scr <*> mapM rwAlt alts)
     ExceptE _ _ -> return expression
     CoerceE inf arg ret body -> ExpM <$> (CoerceE inf arg ret <$> rwExp body)

rwApp inf (ExpM (VarE op_inf op_var)) ty_args args
  | parLoopOperator op_var =
    rwAppOper incParLoopCount inf op_inf op_var ty_args args

  | otherLoopOperator op_var =
    rwAppOper incOtherLoopCount inf op_inf op_var ty_args args

  | otherwise =
    rwAppOper id inf op_inf op_var ty_args args

rwApp inf op ty_args args = do
  op' <- rwExp op
  args' <- mapM rwExp args
  return $ ExpM $ AppE inf op' ty_args args'

rwAppOper subexpr_context inf op_inf op_var ty_args args = do
  loop_nesting <- asks loopNesting
  case parLoops loop_nesting of
    0 -> do
      rewritten <- replaceWithParallelApp inf op_var ty_args args
      rebuild_from_rewrite rewritten
    _ -> recurse
  where
    -- If the rewrite succeeded, continue processing the rewritten expression
    rebuild_from_rewrite (Just new_exp) = rwExp new_exp
    rebuild_from_rewrite Nothing = recurse

    -- Don't rewrite this application.  Rewrite subepressions.
    recurse = do
      args' <- subexpr_context $ mapM rwExp args
      return $ ExpM $ AppE inf (ExpM $ VarE op_inf op_var) ty_args args'

rwAlt (AltM alt) = do
  body <- rwExp $ altBody alt
  return $ AltM $ alt {altBody = body}

rwDef d = mapMDefiniens rwFun d

rwFun (FunM f) = do
  body <- rwExp $ funBody f
  return $ FunM $ f {funBody = body}

rwExport (Export pos spec f) = do
  f' <- rwFun f
  return (Export pos spec f')

rwTopLevel defss exports = do
  defss' <- mapM (mapM rwDef) defss
  exports' <- mapM rwExport exports
  return (defss', exports')

parallelLoopRewrite (Module modname imports defss exports) =
  withTheNewVarIdentSupply $ \var_supply -> do

    -- Set up globals
    tenv <- readInitGlobalVarIO the_memTypes
    dict_env <- runFreshVarM var_supply createDictEnv
    let global_context = LREnv (LoopNesting 0 0) tenv dict_env var_supply
        rewrite = rwTopLevel defss exports

    (defss', exports') <- runReaderT rewrite global_context
    return $ Module modname imports defss' exports'
