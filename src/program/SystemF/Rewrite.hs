
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

caseOfTraversableDict :: TypeEnv
                      -> MkExpM
                      -> TypM
                      -> (Var -> Var -> MkExpM)
                      -> MkExpM
caseOfTraversableDict tenv scrutinee container_type mk_body =
  caseE scrutinee
  [mkAlt tenv (pyonBuiltin the_traversableDict) [container_type] $
   \ [] [trv, bld] -> mk_body trv bld]

-------------------------------------------------------------------------------
-- Rewrite rules

-- Given the arguments to an application, try to create a rewritten term
type RewriteRule = TypeEnv -> ExpInfo -> [TypM] -> [ExpM]
                -> FreshVarM (Maybe ExpM)

rewriteRules :: Map.Map Var RewriteRule
rewriteRules = Map.fromList table
  where
    table = [ (pyonBuiltin the_TraversableDict_list_traverse, rwTraverseList)
            , (pyonBuiltin the_TraversableDict_Stream_traverse, rwBuildTraverseStream)
            , (pyonBuiltin the_TraversableDict_Stream_build, rwBuildTraverseStream)
            , (pyonBuiltin the_fun_zip, rwZip)
            ]

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

-- | The Stream instances of 'build' and 'traverse' are identity functions
rwBuildTraverseStream :: RewriteRule
rwBuildTraverseStream tenv inf [_] [_, stream] = return $ Just stream
rwBuildTraverseStream _ _ _ _ = return Nothing

-- | Rewrite calls to @zip@ to call @zipStream@
--
-- > case t1 of TraversableDict trv1 _.
-- > case t2 of TraversableDict trv2 _.
-- > case t3 of TraversableDict _ bld3.
-- > bld3
-- >   (PyonTuple2 element1 element2)
-- >   (repr_PyonTuple2 element1 element2 repr1 repr2)
-- >   (zipStream element1 element2 repr1 repr2
-- >     (trv1 element1 repr1 input1)
-- >     (trv2 element2 repr2 input2))
rwZip :: RewriteRule
rwZip tenv inf
  [container1, container2, container3, element1, element2]
  (traversable1 : traversable2 : traversable3 : repr1 : repr2 :
   input1 : input2 : other_args) =
  fmap Just $
  caseOfTraversableDict tenv (return traversable1) container1 $ \trv1 _ ->
  caseOfTraversableDict tenv (return traversable2) container2 $ \trv2 _ ->
  caseOfTraversableDict tenv (return traversable3) container3 $ \_ bld3 ->
  let tuple_type = varApp (pyonBuiltin the_PyonTuple2)
                   [fromTypM element1, fromTypM element2]
      tuple_repr = varAppE (pyonBuiltin the_repr_PyonTuple2)
                   [element1, element2]
                   [return repr1, return repr2] 
      app_other_args = map return other_args
  in varAppE bld3
     [TypM tuple_type]
     ([tuple_repr,
       varAppE (pyonBuiltin the_fun_zip_Stream)
       [element1, element2]
       [return repr1, return repr2,
        varAppE trv1 [element1] [return repr1, return input1],
        varAppE trv2 [element2] [return repr2, return input2]]] ++
      app_other_args)
  
rwZip _ _ _ _ = return Nothing