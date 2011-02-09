
module SystemF.Rewrite
       (rewriteApp)
where

import qualified Data.Map as Map
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Builtins.Builtins
import SystemF.Build
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import Type.Environment
import Type.Eval
import Type.Type

-------------------------------------------------------------------------------
-- Helper functions for writing code

-- | Create a case expression to inspect a list.
--
-- > case scrutinee
-- > of make_list list_type (n : intindex)
-- >                        (sz : IndexedInt n) 
-- >                        (p : Referenced (array n list_type)).
-- >      case p
-- >      of referenced ay. $(make_body n sz ay)
caseOfList :: TypeEnv
           -> MkExpM            -- ^ List to inspect
           -> TypM              -- ^ Type of list element
           -> (Var -> Var -> Var -> MkExpM)
              -- ^ Function from (list size index, list size, array reference)
              --   to expression
           -> MkExpM
caseOfList tenv scrutinee list_type mk_body =
  caseE scrutinee
  [mkAlt tenv (pyonBuiltin the_make_list) [list_type] $
   \ [size_index] [size, array_ref] ->
   caseE (varE array_ref)
   [mkAlt tenv (pyonBuiltin the_referenced) [array_type size_index] $
    \ [] [ay] -> mk_body size_index size ay]]
  where
    -- Create the type (array n list_type)
    array_type size_index =
      TypM $ varApp (pyonBuiltin the_array) [VarT size_index, fromTypM list_type]

-------------------------------------------------------------------------------
-- Rewrite rules

-- Given the arguments to an application, try to create a rewritten term
type RewriteRule = TypeEnv -> ExpInfo -> [TypM] -> [ExpM]
                -> FreshVarM (Maybe ExpM)

rewriteRules :: Map.Map Var RewriteRule
rewriteRules = Map.fromList table
  where
    table = [(pyonBuiltin the_TraversableDict_list_traverse, rwTraverseList)]

-- | Attempt to rewrite an application term.
--   If it can be rewritten, return the new expression.
rewriteApp :: TypeEnv -> ExpInfo -> Var -> [TypM] -> [ExpM]
           -> FreshVarM (Maybe ExpM)
rewriteApp tenv inf op_var ty_args args =
  case Map.lookup op_var rewriteRules
  of Just rw -> trace_rewrite $ rw tenv inf ty_args args
     Nothing -> return Nothing
  where
    trace_rewrite = traceShow $
                    text "rewrite" <+> pprExp (ExpM $ AppE defaultExpInfo (ExpM (VarE defaultExpInfo op_var)) ty_args args)

rwTraverseList :: RewriteRule
rwTraverseList tenv inf [elt_type] [elt_repr, list] = fmap Just $
  caseOfList tenv (return list) elt_type $ \size_index size_var array ->
    varAppE (pyonBuiltin the_generate)
    [TypM (VarT size_index), elt_type]
    [varE size_var,
     return elt_repr,
     lamE $ mkFun []
     (\ [] -> return ([ValPT Nothing ::: VarT (pyonBuiltin the_int),
                       OutPT ::: fromTypM elt_type],
                      SideEffectRT ::: fromTypM elt_type))
     (\ [] [index_var, ret_var] ->
         varAppE (pyonBuiltin the_copy)
         [elt_type]
         [return elt_repr,
          varAppE (pyonBuiltin the_subscript)
          [TypM (VarT size_index), elt_type]
          [return elt_repr, varE array, varE index_var],
          varE ret_var])]
  
rwTraverseList _ _ _ _ = return Nothing