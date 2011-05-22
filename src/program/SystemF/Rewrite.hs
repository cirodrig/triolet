
module SystemF.Rewrite
       (RewriteRuleSet,
        getVariableReplacements,
        generalRewrites,
        parallelizingRewrites,
        sequentializingRewrites,
        combineRuleSets,
        rewriteApp)
where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.MonadLogic
import Builtins.Builtins
import SystemF.Build
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import Type.Environment
import Type.Eval
import Type.Type

-- | Type index for stream expressions 
data Stream

liftFreshVarM :: FreshVarM a -> TypeEvalM a
liftFreshVarM m = TypeEvalM $ \supply _ -> runFreshVarM supply m

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
           -> TypeEvalM ExpM    -- ^ List to inspect
           -> TypM              -- ^ Type of list element
           -> (Var -> Var -> Var -> TypeEvalM ExpM)
              -- ^ Function from (list size index, list size, array reference)
              --   to expression
           -> TypeEvalM ExpM
caseOfList tenv scrutinee list_type mk_body =
  caseE scrutinee
  [mkAlt liftFreshVarM tenv (pyonBuiltin the_make_list) [list_type] $
   \ [size_index] [size, array_ref] ->
   caseE (varE array_ref)
   [mkAlt liftFreshVarM tenv (pyonBuiltin the_referenced) [array_type size_index] $
    \ [] [ay] -> mk_body size_index size ay]]
  where
    -- Create the type (array n list_type)
    array_type size_index =
      TypM $ varApp (pyonBuiltin the_array) [VarT size_index, fromTypM list_type]

caseOfTraversableDict :: TypeEnv
                      -> TypeEvalM ExpM
                      -> TypM
                      -> (Var -> Var -> TypeEvalM ExpM)
                      -> TypeEvalM ExpM
caseOfTraversableDict tenv scrutinee container_type mk_body =
  caseE scrutinee
  [mkAlt liftFreshVarM tenv (pyonBuiltin the_traversableDict) [container_type] $
   \ [] [trv, bld] -> mk_body trv bld]

caseOfSomeIndexedInt :: TypeEnv
                     -> TypeEvalM ExpM
                     -> (Var -> Var -> TypeEvalM ExpM)
                     -> TypeEvalM ExpM
caseOfSomeIndexedInt tenv scrutinee mk_body =
  caseE scrutinee
  [mkAlt liftFreshVarM tenv (pyonBuiltin the_someIndexedInt) [] $
   \ [intindex] [intvalue] -> mk_body intindex intvalue]

defineAndInspectIndexedInt tenv int_value mk_body =
  let define_indexed_int =
        varAppE (pyonBuiltin the_defineIntIndex) [] [int_value]
  in caseOfSomeIndexedInt tenv define_indexed_int mk_body

caseOfIndexedInt :: TypeEnv
                 -> TypeEvalM ExpM
                 -> Type
                 -> (Var -> TypeEvalM ExpM)
                 -> TypeEvalM ExpM
caseOfIndexedInt tenv scrutinee int_index mk_body =
  caseE scrutinee
  [mkAlt liftFreshVarM tenv (pyonBuiltin the_indexedInt) [TypM int_index] $
   \ [] [intvalue] -> mk_body intvalue]

-- | Create a list where each array element is a function of its index only
--
--   If no return pointer is given, a writer function is generated.
defineList :: TypM             -- Array element type
           -> TypM             -- Array size type index
           -> TypeEvalM ExpM    -- Array size
           -> TypeEvalM ExpM    -- Array element representation
           -> Maybe (TypeEvalM ExpM)     -- Optional return pointer
           -> (Var -> TypeEvalM ExpM -> TypeEvalM ExpM) -- Element writer code
           -> TypeEvalM ExpM
defineList elt_type size_ix size elt_repr rptr writer =
  varAppE (pyonBuiltin the_make_list)
  [elt_type, size_ix]
  ([size,
    varAppE (pyonBuiltin the_referenced) [TypM array_type]
    [defineArray elt_type size_ix size elt_repr writer]] ++
   maybeToList rptr)
  where
    array_type =
      varApp (pyonBuiltin the_array) [fromTypM size_ix, fromTypM elt_type]

-- | Create a writer function for an array where each array element
--   is a function of its index only.
defineArray :: TypM             -- Array element type
            -> TypM             -- Array size type index
            -> TypeEvalM ExpM   -- Array size
            -> TypeEvalM ExpM   -- Array element representation
            -> (Var -> TypeEvalM ExpM -> TypeEvalM ExpM) -- Element writer code
            -> TypeEvalM ExpM
defineArray elt_type size_ix size elt_repr writer =
  lamE $ mkFun []
  (\ [] -> return ([OutPT ::: array_type], SideEffectRT ::: array_type))
  (\ [] [out_ptr] ->
    varAppE (pyonBuiltin the_doall)
    [size_ix, TypM array_type, elt_type]
    [size,
     lamE $ mkFun []
     (\ [] -> return ([ValPT Nothing ::: intType],
                      SideEffectRT ::: fromTypM elt_type))
     (\ [] [index_var] ->
       let out_expr =
             varAppE (pyonBuiltin the_subscript_out) [size_ix, elt_type]
             [elt_repr, varE out_ptr, varE index_var]
       in writer index_var out_expr)])
  where
    array_type =
      varApp (pyonBuiltin the_array) [fromTypM size_ix, fromTypM elt_type]

intType = VarT (pyonBuiltin the_int)

shapeOfType :: TypM -> TypM
shapeOfType (TypM t) = TypM $ varApp (pyonBuiltin the_shape) [t]

-------------------------------------------------------------------------------
-- Rewrite rules

-- Given the arguments to an application, try to create a rewritten term
type RewriteRule = ExpInfo -> [TypM] -> [ExpM] -> TypeEvalM (Maybe ExpM)

-- | A set of rewrite rules
data RewriteRuleSet =
  RewriteRuleSet
  { -- | Rewrite rules for variable applications.  Given the variable and its
    --   arguments, the rule tries to replace it with a simpler expression.
    --
    --   These rules are processed by 'rewriteApp'.
    rewriteRules :: Map.Map Var RewriteRule

    -- | Rewrite rules for variables.
    --   Whenever the variable is seen, it is unconditionally replaced by the
    --   expression.  These rules are processed by "SystemF.Simplify".
  , rewriteVariables :: Map.Map Var ExpM
  }

-- | Combine multiple rule sets.  Rule sets earlier in the list take precedence
--   over later ones.
combineRuleSets :: [RewriteRuleSet] -> RewriteRuleSet
combineRuleSets rs =
  RewriteRuleSet
  (Map.unions $ map rewriteRules rs)
  (Map.unions $ map rewriteVariables rs)

-- | Get unconditional variable replacement rules.  For each
--   (variable, expression) pair in the list, any occurrence of the variable 
--   should be replaced by the corresponding expression.
getVariableReplacements :: RewriteRuleSet -> [(Var, ExpM)]
getVariableReplacements rs = Map.toList $ rewriteVariables rs

-- | General-purpose rewrite rules that should always be applied
generalRewrites :: RewriteRuleSet
generalRewrites = RewriteRuleSet (Map.fromList table) (Map.fromList exprs)
  where
    table = [ (pyonBuiltin the_convertToBare, rwConvertToBare)
            , (pyonBuiltin the_convertToBoxed, rwConvertToBoxed)
            , (pyonBuiltin the_range, rwRange)
            , (pyonBuiltin the_TraversableDict_list_traverse, rwTraverseList)
            , (pyonBuiltin the_TraversableDict_list_build, rwBuildList)
            , (pyonBuiltin the_TraversableDict_Stream_traverse, rwTraverseStream)
            , (pyonBuiltin the_TraversableDict_Stream_build, rwBuildStream)
            , (pyonBuiltin the_oper_GUARD, rwGuard)
            , (pyonBuiltin the_fun_map, rwMap)
            , (pyonBuiltin the_fun_zip, rwZip)
            , (pyonBuiltin the_fun_zip3, rwZip3)
            , (pyonBuiltin the_fun_zip4, rwZip4)
            , (pyonBuiltin the_fun_map_Stream, rwMapStream)
            , (pyonBuiltin the_fun_zip_Stream, rwZipStream) 
            , (pyonBuiltin the_fun_zip3_Stream, rwZip3Stream)
            , (pyonBuiltin the_fun_zip4_Stream, rwZip4Stream)
            , (pyonBuiltin the_histogram, rwHistogram)
            , (pyonBuiltin the_fun_reduce, rwReduce)
            , (pyonBuiltin the_fun_reduce1, rwReduce1)
              {- Rewrites temporarily disabled while we change Stream types
            , (pyonBuiltin the_oper_CAT_MAP, rwBindStream) -}
            , (pyonBuiltin the_for, rwFor)
            , (pyonBuiltin the_safeSubscript, rwSafeSubscript)
            ]

    exprs = [ {- Disabled because the new function, 'generate_forever', 
                 hasn't been written yet
                 (pyonBuiltin the_count, count_expr) -} ]
    
    -- The following expression represents the "count" stream:
    -- asList (array_shape pos_infty)
    -- (generate_forever int repr_int (store int))
    count_expr =
      ExpM $ AppE defaultExpInfo as_list [TypM array_shape, TypM intType]
      [generate_expr]
      where
        as_list =
          ExpM $ VarE defaultExpInfo (pyonBuiltin the_fun_asList_Stream)
        generate_f =
          ExpM $ VarE defaultExpInfo (pyonBuiltin the_generate_forever)

        array_shape = varApp (pyonBuiltin the_array_shape) [posInftyT]
        generate_expr =
          ExpM $ AppE defaultExpInfo generate_f [TypM intType]
          [ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_int),
           ExpM $ AppE defaultExpInfo (ExpM $ VarE defaultExpInfo (pyonBuiltin the_store)) [TypM intType] []]

-- | Rewrite rules that transform potentially parallel algorithms into
--   explicitly parallel algorithms.
parallelizingRewrites :: RewriteRuleSet
parallelizingRewrites = RewriteRuleSet (Map.fromList table) Map.empty
  where
    table = [ (pyonBuiltin the_fun_reduce_Stream, rwParallelReduceStream)
            , (pyonBuiltin the_fun_reduce1_Stream, rwParallelReduce1Stream)
            , (pyonBuiltin the_histogramArray, rwParallelHistogramArray)
            , (pyonBuiltin the_doall, rwParallelDoall)
            ]

-- | Rewrite rules that transform potentially parallel algorithms into
--   sequential algorithms.  The sequential algorithms are more efficient.
--   These rules should be applied after outer loops are parallelized.
sequentializingRewrites :: RewriteRuleSet
sequentializingRewrites = RewriteRuleSet (Map.fromList table) Map.empty
  where
    table = [ (pyonBuiltin the_histogramArray, rwHistogramArray)
            , (pyonBuiltin the_fun_reduce_Stream, rwReduceStream)
            , (pyonBuiltin the_fun_reduce1_Stream, rwReduce1Stream)
            , (pyonBuiltin the_fun_fold_Stream, rwFoldStream)
            ]

-- | Attempt to rewrite an application term.
--   If it can be rewritten, return the new expression.
--
--   The type environment is only used for looking up data types and
--   constructors.
rewriteApp :: RewriteRuleSet
           -> ExpInfo -> Var -> [TypM] -> [ExpM]
           -> TypeEvalM (Maybe ExpM)
rewriteApp ruleset inf op_var ty_args args =
  case Map.lookup op_var $ rewriteRules ruleset
  of Just rw -> trace_rewrite $ rw inf ty_args args
     Nothing -> return Nothing
  where
    trace_rewrite m = do 
      x <- m
      case x of
        Nothing -> return x
        Just e' -> traceShow (text "rewrite" <+> old_exp $$ text "    -->" <+> pprExp e') $ return x
    
    old_exp = pprExp (ExpM $ AppE defaultExpInfo (ExpM (VarE defaultExpInfo op_var)) ty_args args)

-- | Turn a call of 'convertToBare' into a constructor application or
--   case statement, if the type is known.  Also, cancel applications of
--   'convertToBare' with 'convertToBoxed'.
rwConvertToBare :: RewriteRule
rwConvertToBare inf [TypM bare_type] [repr, arg] 
  | Just (op, _, [_, arg']) <- unpackVarAppM arg,
    op `isPyonBuiltin` the_convertToBoxed =
      -- Cancel applications of these constructors 
      -- convertToBare (repr, convertToBoxed (_, e)) = copy repr e
      return $ Just $ copy_value arg'
  | otherwise = do
      -- If the bare type is "StoredBox t", then construct the value
      whnf_type <- reduceToWhnf bare_type
      case fromVarApp whnf_type of
        Just (ty_op, [boxed_type])
          | ty_op `isPyonBuiltin` the_StoredBox ->
              fmap Just $ construct_stored_box boxed_type
        _ -> do
          -- If the boxed type is "Boxed t", then
          -- deconstruct and copy the value
          boxed_type <-
            reduceToWhnf $ varApp (pyonBuiltin the_BoxedType) [whnf_type]
          case fromVarApp boxed_type of
            Just (ty_op, [_])
              | ty_op `isPyonBuiltin` the_Boxed ->
                  fmap Just $ deconstruct_boxed whnf_type
            _ ->
              -- Otherwise, cannot simplify
              return Nothing
  where
    copy_value e =
      ExpM $ AppE inf copy_op [TypM bare_type] [repr, e]
      where
        copy_op = ExpM $ VarE inf (pyonBuiltin the_copy)

    -- Create the expression
    --
    -- > storedBox boxed_type arg
    construct_stored_box boxed_type =
      varAppE (pyonBuiltin the_storedBox) [TypM boxed_type] [return arg]

    -- Create the expression
    --
    -- > case arg of boxed bare_type (x : bare_type) -> copy bare_type repr x
    deconstruct_boxed whnf_type = do
      tenv <- getTypeEnv
      caseE (return arg)
        [mkAlt undefined tenv (pyonBuiltin the_boxed)
         [TypM whnf_type]
         (\ [] [unboxed_ref] ->
           varAppE (pyonBuiltin the_copy) [TypM whnf_type] [varE unboxed_ref])]

rwConvertToBare _ _ _ = return Nothing

rwConvertToBoxed :: RewriteRule
rwConvertToBoxed inf [TypM bare_type] [repr, arg] 
  | Just (op, _, [_, arg']) <- unpackVarAppM arg,
    op `isPyonBuiltin` the_convertToBare = 
      -- Cancel applications of these constructors 
      -- convertToBoxed (_, convertToBare (_, e)) = e
      return $ Just arg'
  | otherwise = do
      -- If the bare type is "StoredBox t", then deconstruct the value
      whnf_type <- reduceToWhnf bare_type
      case fromVarApp whnf_type of
        Just (ty_op, [boxed_type])
          | ty_op `isPyonBuiltin` the_StoredBox ->
              fmap Just $ deconstruct_stored_box boxed_type
        _ -> do
          -- If the boxed type is "Boxed t", then construct the value
          boxed_type <-
            reduceToWhnf $ varApp (pyonBuiltin the_BoxedType) [whnf_type]
          case fromVarApp boxed_type of
            Just (ty_op, [_])
              | ty_op `isPyonBuiltin` the_Boxed ->
                  fmap Just $ construct_boxed whnf_type
            _ ->
              -- Otherwise, cannot simplify
              return Nothing
  where
    deconstruct_stored_box boxed_type = do
      tenv <- getTypeEnv
      caseE (return arg)
        [mkAlt undefined tenv (pyonBuiltin the_storedBox)
         [TypM boxed_type]
         (\ [] [boxed_ref] -> varE boxed_ref)]
    
    construct_boxed whnf_type = do
      varAppE (pyonBuiltin the_boxed) [TypM whnf_type] [return arg]

rwConvertToBoxed _ _ _ = return Nothing

-- | Convert 'range' into an explicitly indexed variant
rwRange :: RewriteRule
rwRange inf [] [count] = do
  tenv <- getTypeEnv
  fmap Just $
    defineAndInspectIndexedInt tenv (return count)
    (\intindex intvalue ->
      varAppE (pyonBuiltin the_fun_asList_Stream)
      [TypM $ varApp (pyonBuiltin the_array_shape) [VarT intindex], TypM intType]
      [varAppE (pyonBuiltin the_rangeIndexed) [TypM $ VarT intindex] [varE intvalue]])

rwRange _ _ _ = return Nothing

rwTraverseList :: RewriteRule
rwTraverseList inf [elt_type] [elt_repr, list] = do
  tenv <- getTypeEnv
  fmap Just $
    caseOfList tenv (return list) elt_type $ \size_index size_var array ->
    varAppE (pyonBuiltin the_fun_asList_Stream) 
    [TypM $ varApp (pyonBuiltin the_array_shape) [VarT size_index], elt_type]
    [varAppE (pyonBuiltin the_generate)
     [TypM (VarT size_index), elt_type]
     [varE size_var,
      return elt_repr,
      lamE $ mkFun []
      (\ [] -> return ([ValPT Nothing ::: intType,
                        OutPT ::: fromTypM elt_type],
                       SideEffectRT ::: fromTypM elt_type))
      (\ [] [index_var, ret_var] ->
          varAppE (pyonBuiltin the_copy)
          [elt_type]
          [return elt_repr,
           varAppE (pyonBuiltin the_subscript)
           [TypM (VarT size_index), elt_type]
           [return elt_repr, varE array, varE index_var],
           varE ret_var])]]
  
rwTraverseList _ _ _ = return Nothing

rwBuildList :: RewriteRule
rwBuildList inf [elt_type] (elt_repr : stream : other_args) =
  case interpretStream2 (VarT (pyonBuiltin the_list_shape))
       (fromTypM elt_type) elt_repr stream
  of Just s@(GenerateStream {})
       | Array1DShape size_arg size_val <- sexpShape s ->
           -- Statically known stream size.
           -- TODO: generalize to more stream constructors
           fmap Just $
           buildListDoall inf elt_type elt_repr other_args size_arg size_val
           (_sexpGenerator s)
     _ -> return Nothing

rwBuildList _ _ _ = return Nothing

rwTraverseStream :: RewriteRule
rwTraverseStream inf _ [_, stream] = return (Just stream)
rwTraverseStream _ _ _ = return Nothing

rwBuildStream :: RewriteRule
rwBuildStream inf _ [_, stream] = return (Just stream)
rwBuildStream _ _ _ = return Nothing

buildListDoall inf elt_type elt_repr other_args size count generator =
  let return_ptr =
        case other_args
        of [x] -> Just (return x)
           []  -> Nothing

      write_array index mk_dst =
        appE (generator (ExpM $ VarE defaultExpInfo index)) [] [mk_dst]

  in defineList elt_type size
     (return count) (return elt_repr) return_ptr write_array

{- Disabled while we change types

-- | Rewrite applications of the stream @bind@ operator when the producer
--   or transformer has a well-behaved data flow pattern.
--
--   * Transformer is rewritable to @\x -> return f(x)@: rewrite to a
--     mapStream
rwBindStream :: RewriteRule
rwBindStream tenv inf
  [elt1, elt2]
  [repr1, repr2, producer, transformer] =
  case unreturnStreamTransformer transformer
  of Just map_fn ->
       fmap Just $
       varAppE (pyonBuiltin the_fun_map_Stream)
       [TypM (VarT $ pyonBuiltin the_list), elt1, elt2]
       [return repr1, return repr2, return map_fn, return producer]
     _ -> return Nothing

rwBindStream _ _ _ _ = return Nothing

-}

-- > guard t r b s
--
-- becomes
--
-- > if b then oper_EMPTY t else s
rwGuard :: RewriteRule
rwGuard inf [elt_ty] [elt_repr, arg, stream] =
  liftFreshVarM $ fmap Just $
  ifE (return arg)
  (return stream)
  (varAppE (pyonBuiltin the_oper_EMPTY) [elt_ty] [return elt_repr])

rwGuard _ _ _ = return Nothing
  
rwMap :: RewriteRule
rwMap inf
  [container, element1, element2]
  (traversable : repr1 : repr2 :
   transformer : input : other_args) = do
  tenv <- getTypeEnv
  fmap Just $
    caseOfTraversableDict tenv (return traversable) container $ \trv bld ->
    varAppE bld [element2]
    (return repr2 :
     varAppE (pyonBuiltin the_fun_map_Stream)
     [shapeOfType container, element1, element2]
     [return repr1,
      return repr2,
      return transformer,
      varAppE trv [element1] [return repr1, return input]] :
     map return other_args)

rwMap _ _ _ = return Nothing

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
rwZip inf
  [container, element1, element2]
  (traversable : repr1 : repr2 :
   input1 : input2 : other_args) = do
  let zip_args = [ZipArg element1 repr1 input1,
                  ZipArg element2 repr2 input2]
  tenv <- getTypeEnv
  fmap Just $
    generalizedRewriteZip tenv inf zip_args container traversable other_args

rwZip _ _ _ = return Nothing

rwZip3 :: RewriteRule
rwZip3 inf
  [container, element1, element2, element3]
  (traversable : repr1 : repr2 : repr3 :
   input1 : input2 : input3 : other_args) = do
  let zip_args = [ZipArg element1 repr1 input1,
                  ZipArg element2 repr2 input2,
                  ZipArg element3 repr3 input3]
  tenv <- getTypeEnv
  fmap Just $
    generalizedRewriteZip tenv inf zip_args container traversable other_args

rwZip3 _ _ _ = return Nothing

rwZip4 :: RewriteRule
rwZip4 inf
  [container, element1, element2, element3, element4]
  (traversable : repr1 : repr2 : repr3 : repr4 :
   input1 : input2 : input3 : input4 : other_args) = do
  let zip_args = [ZipArg element1 repr1 input1,
                  ZipArg element2 repr2 input2,
                  ZipArg element3 repr3 input3,
                  ZipArg element4 repr4 input4]
  tenv <- getTypeEnv
  fmap Just $
    generalizedRewriteZip tenv inf zip_args container traversable other_args

rwZip4 _ _ _ = return Nothing

rwMapStream :: RewriteRule
rwMapStream inf
  ty_args@[shape_type, elt1, elt2]
  args@[repr1, repr2, transformer, producer]
  | Just s <- interpretStream2 (fromTypM shape_type) (fromTypM elt2) repr2 map_expr = do
      encodeStream2 shape_type s
  where
    map_op = ExpM $ VarE inf (pyonBuiltin the_fun_map_Stream)
    map_expr =
      ExpM $ AppE inf map_op ty_args args
              
{- Obsoleted by the new interpretStream function
rwMapStream tenv inf
  ty_args@[shape_type, elt1, elt2]
  args@[repr1, repr2, transformer, producer]
  | Just shape <- interpretStream repr1 producer =
    let new_shape =
          -- Fuse the transformer into the generator expression
          InterpretedStream
          { sShape = sShape shape
          , sType = fromTypM elt2
          , sRepr = repr2
          , sGenerator = \ix ->
              -- The generator takes an output pointer as a parameter
              lamE $ mkFun []
              (\ [] -> return ([OutPT ::: fromTypM elt2],
                               SideEffectRT ::: fromTypM elt2))
              (\ [] [outvar] -> do
                  tmpvar <- newAnonymousVar ObjectLevel
                  -- Compute the input to 'map'
                  rhs <- appE (sGenerator shape ix) [] [varE tmpvar]
                  -- Compute the output of 'map'
                  body <- appE (return transformer) [] [varE tmpvar, varE outvar]
                  let binder = localVarP tmpvar (fromTypM elt1) repr1
                      let_expr = ExpM $ LetE inf binder rhs body
                  return let_expr)}
    in traceShow (text "rwMapStream NO" <+> pprType (shapeType $ sShape shape)) $ encodeStream shape_type new_shape
-}

rwMapStream _ _ _ = return Nothing

-- | Rewrite calls to @zipStream@ when we know the size of the stream.
--
-- > zipStream(count, generate(n, f)) -> generate(n, \i -> (i, f i))
-- > zipStream(generate(n, f), count) -> generate(n, \i -> (f i, i))
-- > zipStream(generate(n1, f1), generate(n2, f2)) ->
--     generate(min(n1, n2), \i -> (f1 i, f2 i))
rwZipStream :: RewriteRule
rwZipStream inf
  [TypM shape_type, TypM elt1, TypM elt2]
  [repr1, repr2, stream1, stream2]
  | Just s1 <- interpretStream2 shape_type elt1 repr1 stream1,
    Just s2 <- interpretStream2 shape_type elt2 repr2 stream2 =
      generalizedZipStream2 (TypM shape_type) [s1, s2]

rwZipStream _ _ _ = return Nothing

rwZip3Stream :: RewriteRule
rwZip3Stream inf
  [TypM shape_type, TypM elt1, TypM elt2, TypM elt3]
  [repr1, repr2, repr3, stream1, stream2, stream3]
  | Just s1 <- interpretStream2 shape_type elt1 repr1 stream1,
    Just s2 <- interpretStream2 shape_type elt2 repr2 stream2,
    Just s3 <- interpretStream2 shape_type elt3 repr3 stream3 =
      generalizedZipStream2 (TypM shape_type) [s1, s2, s3]

rwZip3Stream _ _ _ = return Nothing

rwZip4Stream :: RewriteRule
rwZip4Stream inf
  [TypM shape_type, TypM elt1, TypM elt2, TypM elt3, TypM elt4]
  [repr1, repr2, repr3, repr4, stream1, stream2, stream3, stream4]
  | Just s1 <- interpretStream2 shape_type elt1 repr1 stream1,
    Just s2 <- interpretStream2 shape_type elt2 repr2 stream2,
    Just s3 <- interpretStream2 shape_type elt3 repr3 stream3,
    Just s4 <- interpretStream2 shape_type elt4 repr4 stream4 =
      generalizedZipStream2 (TypM shape_type) [s1, s2, s3, s4]

rwZip4Stream _ _ _ = return Nothing

generalizedZipStream2 :: TypM -> [ExpS] -> TypeEvalM (Maybe ExpM)
generalizedZipStream2 shape_type streams =
  case zipStreams2 streams -- Zip the streams
  of Just s -> encodeStream2 shape_type s
     Nothing -> return Nothing

-- | Turn a list-building histogram into an array-building histogram
--
-- > rwHistogram t size input
--
-- becomes
--
-- > case (defineIntIndex size)
-- > of SomeIntIndex n index.
-- >      make_list int n index
-- >        (referenced (array n int) (histogramArray t n index input)))
rwHistogram :: RewriteRule
rwHistogram inf [container] (size : input : other_args) = do
  tenv <- getTypeEnv
  fmap Just $
    defineAndInspectIndexedInt tenv (return size)
    (\n index ->
      varAppE (pyonBuiltin the_make_list)
      [TypM intType, TypM $ VarT n]
      (varE index :
       varAppE (pyonBuiltin the_referenced)
       [TypM $ varApp (pyonBuiltin the_array) [VarT n, intType]]
       [varAppE (pyonBuiltin the_histogramArray)
        [shapeOfType container, TypM $ VarT n]
        [varE index, return input]] :
       map return other_args))

rwHistogram _ _ _ = return Nothing

rwHistogramArray :: RewriteRule
rwHistogramArray inf [shape_type, size_ix] (size : input : other_args) =
  case interpretStream2 (fromTypM shape_type) intType repr_int input
  of Just s -> do
       tenv <- getTypeEnv
       fmap Just $
         varAppE (pyonBuiltin the_createHistogram)
         [size_ix]
         (return size :
          lamE (mkFun []
          (\ [] -> return ([BoxPT ::: funType [ ValPT Nothing ::: intType
                                              , OutPT ::: eff_type]
                                              (SideEffectRT ::: eff_type),
                            ReadPT ::: eff_type,
                            OutPT ::: eff_type],
                           SideEffectRT ::: eff_type))
          (\ [] [writer, in_eff, out_eff] ->
            make_histogram_writer tenv s writer in_eff out_eff)) :
          map return other_args)
     Nothing -> return Nothing
  where
    eff_type = VarT (pyonBuiltin the_EffTok)
    repr_int = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_int)
    repr_eff = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_EffTok)
    
    make_histogram_writer tenv s writer in_eff out_eff = do
      accumulator_fn <-
        lamE $ mkFun []
        (\ [] -> return ([ReadPT ::: eff_type, ReadPT ::: intType,
                          OutPT ::: eff_type], SideEffectRT ::: eff_type))
        (\ [] [in_eff2, index, out_eff2] -> do
            let fst_eff =
                  varAppE (pyonBuiltin the_propagateEffTok) []
                  [varE in_eff2]
                snd_eff =
                  varAppE writer [] [varAppE (pyonBuiltin the_load)
                                     [TypM intType]
                                     [varE index]]
            varAppE (pyonBuiltin the_seqEffTok) []
              [fst_eff, snd_eff, varE out_eff2])
      let in_eff_exp = ExpM $ VarE defaultExpInfo in_eff
      let out_eff_exp = ExpM $ VarE defaultExpInfo out_eff
      translateStreamToFold tenv eff_type repr_eff in_eff_exp accumulator_fn out_eff_exp s
      
rwHistogramArray _ _ _ = return Nothing

rwReduce :: RewriteRule
rwReduce inf
  [container, element]
  (traversable : repr : reducer : init : input : other_args) = do
  tenv <- getTypeEnv
  fmap Just $
    caseOfTraversableDict tenv (return traversable) container $ \trv _ ->
    let app_other_args = map return other_args
    in varAppE (pyonBuiltin the_fun_reduce_Stream)
       [shapeOfType container, element]
       ([return repr, return reducer, return init,
         varAppE trv [element] [return repr, return input]] ++
        app_other_args)

rwReduce _ _ _ = return Nothing

-- | @reduce1@ is just like @reduce@ except there's no initial value
rwReduce1 :: RewriteRule
rwReduce1 inf
  [container, element]
  (traversable : repr : reducer : input : other_args) = do
  tenv <- getTypeEnv
  fmap Just $
    caseOfTraversableDict tenv (return traversable) container $ \trv _ ->
    let app_other_args = map return other_args
    in varAppE (pyonBuiltin the_fun_reduce1_Stream)
       [shapeOfType container, element]
       ([return repr, return reducer,
         varAppE trv [element] [return repr, return input]] ++
        app_other_args)

rwReduce1 _ _ _ = return Nothing

-- | Parallelize a reduction.
--   This rewrite is nonterminating, so we must limit how often it's performed.
rwParallelReduceStream :: RewriteRule
rwParallelReduceStream inf
  [shape_type, elt]
  (elt_repr : reducer : init : stream : other_args) = do
  m_stream <- interpretAndBlockStream (fromTypM shape_type) (fromTypM elt) elt_repr stream
  case m_stream of
    Nothing -> return Nothing
    Just (size_var, count_var, base_var, bs, bs_size, bs_count) -> do
      -- > blocked_reduce elt bs_size elt_repr bs_count 0 reducer init
      -- >   (\ix ct b -> reduceStream list_shape elt elt_repr
      -- >                reducer init (asListShape bs))

      -- Create the worker function, which processes one block
      worker_stream <-
        encodeStream2 (TypM $ VarT $ pyonBuiltin the_list_shape) bs
      worker_retvar <- newAnonymousVar ObjectLevel
      case worker_stream of
        Nothing -> return Nothing
        Just ws -> liftFreshVarM $ do
          worker_body <-
            varAppE (pyonBuiltin the_fun_reduce_Stream)
            [TypM $ VarT (pyonBuiltin the_list_shape), elt]
            [return elt_repr,
             return reducer,
             return init,
             return ws,
             varE worker_retvar]
          
          let param1 = memVarP count_var $
                       ValPT Nothing :::
                       varApp (pyonBuiltin the_IndexedInt) [VarT size_var]
              param2 = memVarP base_var (ValPT Nothing ::: intType)
              param3 = memVarP worker_retvar (OutPT ::: fromTypM elt)
              worker_fn =
                FunM $
                Fun { funInfo = inf
                    , funTyParams = [TyPatM size_var intindexT]
                    , funParams = [param1, param2, param3]
                    , funReturn = RetM $ SideEffectRT ::: fromTypM elt
                    , funBody = worker_body}
                
          -- Create the blocked_reduce call
          call <-
            varAppE (pyonBuiltin the_blocked_reduce) [elt, bs_size]
            (return elt_repr : return bs_count : litE (IntL 0 intType) :
             return reducer : return init :
             return (ExpM $ LamE defaultExpInfo worker_fn) :
             map return other_args)
          return $ Just call

rwParallelReduceStream _ _ _ = return Nothing

-- | Parallelize a reduction.
--   This rewrite is nonterminating, so we must limit how often it's performed.
rwParallelReduce1Stream :: RewriteRule
rwParallelReduce1Stream inf
  [shape_type, elt]
  (elt_repr : reducer : stream : other_args) = do
  m_stream <- interpretAndBlockStream (fromTypM shape_type) (fromTypM elt) elt_repr stream
  case m_stream of
    Nothing -> return Nothing
    Just (size_var, count_var, base_var, bs, bs_size, bs_count) -> do
      -- > blocked_reduce1 elt bs_size elt_repr bs_count 0 reducer
      -- >   (\ix ct b -> reduce1Stream list_shape elt elt_repr
      -- >                reducer (asListShape bs))

      -- Create the worker function, which processes one block
      worker_stream <-
        encodeStream2 (TypM $ VarT $ pyonBuiltin the_list_shape) bs
      worker_retvar <- newAnonymousVar ObjectLevel
      case worker_stream of
        Nothing -> return Nothing
        Just ws -> do
          worker_body <-
            liftFreshVarM $
            varAppE (pyonBuiltin the_fun_reduce1_Stream)
            [TypM $ VarT (pyonBuiltin the_list_shape), elt]
            [return elt_repr,
             return reducer,
             return ws,
             varE worker_retvar]
          
          let param1 = memVarP count_var $
                       ValPT Nothing :::
                       varApp (pyonBuiltin the_IndexedInt) [VarT size_var]
              param2 = memVarP base_var (ValPT Nothing ::: intType)
              param3 = memVarP worker_retvar (OutPT ::: fromTypM elt)
              worker_fn =
                FunM $
                Fun { funInfo = inf
                    , funTyParams = [TyPatM size_var intindexT]
                    , funParams = [param1, param2, param3]
                    , funReturn = RetM $ SideEffectRT ::: fromTypM elt
                    , funBody = worker_body}
                
          -- Create the blocked_reduce call
          call <-
            liftFreshVarM $
            varAppE (pyonBuiltin the_blocked_reduce1) [elt, bs_size]
            (return elt_repr : return bs_count : litE (IntL 0 intType) :
             return reducer :
             return (ExpM $ LamE defaultExpInfo worker_fn) :
             map return other_args)
          return $ Just call

rwParallelReduce1Stream _ _ _ = return Nothing

-- | Parallelize a histogram computation.
--
--   The parallel part computes multiple, privatized histograms, then
--   sums them up.  A single privatized histogram is generated using the
--   same loop we started with, only traversing a smaller domain. 
rwParallelHistogramArray :: RewriteRule
rwParallelHistogramArray inf
  [shape_type, size_ix] (size : input : other_args) = do
  m_stream <- interpretAndBlockStream (fromTypM shape_type) intType int_repr input
  case m_stream of
    Nothing -> return Nothing
    Just (size_var, count_var, base_var, bs, bs_size, bs_count) -> do
      -- > local empty_hist = defineArray size_ix size int_repr
      -- >                    (\_ dst -> store int 0 dst) empty_hist
      -- > in blocked_reduce (array size_ix int) bs_size repr_int bs_count 0
      -- >    (\a b ret -> doall (\i -> store (load a[i] + load b[i]) ret[i]))
      -- >    empty_hist
      -- >    (\ix ct b -> histogramArray list_shape size_ix size
      -- >                 (asListShape bs))
      worker_stream <-
        encodeStream2 (TypM $ VarT $ pyonBuiltin the_list_shape) bs
      case worker_stream of
        Nothing -> return Nothing
        Just ws ->
          let write_into return_arg = do
                -- Define an empty histogram, i.e. a zero-filled array
                empty_hist <- newAnonymousVar ObjectLevel
                empty_hist_rhs <- appE zero_array [] [varE empty_hist]
                array_repr_exp <- array_repr
                let binder = localVarP empty_hist array_type array_repr_exp

                -- Compute the histogram
                compute_hist <-
                  varAppE (pyonBuiltin the_blocked_reduce) 
                  [TypM array_type, bs_size]
                  [array_repr,
                   return bs_count,
                   litE (IntL 0 intType),
                   elementwise_add,
                   varE empty_hist,
                   worker_fn size_var count_var base_var ws,
                   return_arg]

                return $ ExpM $
                  LetE defaultExpInfo binder empty_hist_rhs compute_hist
          in case other_args
             of [] ->
                  -- Return a writer funciton
                  fmap Just $
                  lamE $ mkFun []
                  (\ [] -> return ([OutPT ::: array_type],
                                   SideEffectRT ::: array_type))
                  (\ [] [ret_var] -> write_into (varE ret_var))
                [ret_val] ->
                  -- Write into the return argument
                  fmap Just $ write_into (return ret_val)
                _ ->
                  internalError "rwParallelHistogramArray"

  where
    array_type = varApp (pyonBuiltin the_array) [fromTypM size_ix, intType]
    array_shape = varApp (pyonBuiltin the_array_shape) [fromTypM size_ix]
    
    int_repr = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_int)
    array_repr = varAppE (pyonBuiltin the_repr_array)
                 [size_ix, TypM intType] [return size, return int_repr]

    -- A single parallel task
    --    
    -- > \ local_size local_count base ret.
    -- >     histogramArray list_shape histo_size histo_count stream ret
    worker_fn size_var count_var base_var bs = do
      retvar <- newAnonymousVar ObjectLevel
      fn_body <- varAppE (pyonBuiltin the_histogramArray)
                 [TypM $ VarT (pyonBuiltin the_list_shape), size_ix]
                 [return size, return bs, varE retvar]
      let param1 = memVarP count_var $
                   ValPT Nothing :::
                   varApp (pyonBuiltin the_IndexedInt) [VarT size_var]
          param2 = memVarP base_var $ ValPT Nothing ::: intType
          param3 = memVarP retvar $ OutPT ::: array_type
          ret = RetM $ SideEffectRT ::: array_type
      return $ ExpM $ LamE defaultExpInfo $ FunM $
        Fun { funInfo = inf
            , funTyParams = [TyPatM size_var intindexT]
            , funParams = [param1, param2, param3]
            , funReturn = ret
            , funBody = fn_body}
  
    -- Initialize an array with all zeros
    zero_array =
      defineArray (TypM intType) size_ix (return size) (return int_repr)
      (\_ out_expr -> varAppE (pyonBuiltin the_store) [TypM intType]
                      [litE $ IntL 0 intType, out_expr])
    
    -- Add two arrays, elementwise
    elementwise_add =
      lamE $ mkFun []
      (\ [] -> return ([ReadPT ::: array_type,
                        ReadPT ::: array_type,
                        OutPT ::: array_type],
                       SideEffectRT ::: array_type))
      (\ [] [a, b, ret_ptr] ->
        appE
        (defineArray (TypM intType) size_ix (return size) (return int_repr)
         (\index_var out_expr ->
           let load_element array_ptr_var =
                 -- Load an array element from array_ptr_var at index_var
                 varAppE (pyonBuiltin the_load) [TypM intType]
                 [varAppE (pyonBuiltin the_subscript)
                  [size_ix, TypM intType]
                  [return int_repr, varE array_ptr_var, varE index_var]]
           in varAppE (pyonBuiltin the_store) [TypM intType]
              [varAppE (pyonBuiltin the_AdditiveDict_int_add) []
               [load_element a, load_element b], out_expr]))
        []
        [varE ret_ptr])

rwParallelHistogramArray _ _ _ = return Nothing


rwParallelDoall :: RewriteRule
rwParallelDoall inf [size_ix, result_eff, element_eff] [size, worker] =
  -- Strip-mine a doall loop.  The new outer loop is parallel.  The new
  -- inner loop is the same as the original loop except that an offset is 
  -- added to the loop counter.
  liftFreshVarM $ fmap Just $
  varAppE (pyonBuiltin the_blocked_doall) [size_ix, result_eff, element_eff]
  [return size,
   litE (IntL 0 intType),
   lamE $ mkFun [intindexT]
   (\ [mindex] -> return ([ValPT Nothing :::
                           varApp (pyonBuiltin the_IndexedInt) [VarT mindex],
                           ValPT Nothing ::: intType],
                          SideEffectRT ::: fromTypM element_eff))
   (\ [mindex] [msize, offset] ->
     varAppE (pyonBuiltin the_doall) [TypM (VarT mindex), result_eff, element_eff]
     [varE msize,
      lamE $ mkFun []
      (\ [] -> return ([ValPT Nothing ::: intType],
                       SideEffectRT ::: fromTypM element_eff))
      (\ [] [ix] ->
        appE (return worker) []
        [varAppE (pyonBuiltin the_AdditiveDict_int_add) []
         [varE offset, varE ix]])])]
  
rwParallelDoall _ _ _ = return Nothing

rwReduceStream :: RewriteRule
rwReduceStream inf [shape_type, element]
  (elt_repr : reducer : init : stream : other_args) =
  case interpretStream2 (fromTypM shape_type) (fromTypM element) elt_repr stream
  of Just s -> do
       tenv <- getTypeEnv
       fmap Just $
         translateStreamToFoldWithExtraArgs tenv (fromTypM element) elt_repr init reducer s other_args
     Nothing -> return Nothing
  
rwReduceStream _ _ _ = return Nothing

rwFoldStream :: RewriteRule
rwFoldStream inf [elt_type, acc_type]
  (elt_repr : acc_repr : reducer : init : stream : other_args) =
  case interpretStream2 (VarT (pyonBuiltin the_list_shape)) (fromTypM elt_type)
       elt_repr stream
  of Just s -> do
       tenv <- getTypeEnv
       fmap Just $
         translateStreamToFoldWithExtraArgs tenv (fromTypM acc_type) acc_repr init reducer s other_args
     Nothing -> return Nothing

rwFoldStream _ _ _ = return Nothing

rwReduceGenerate :: ExpInfo -> TypM -> ExpM -> ExpM -> ExpM -> [ExpM]
                 -> TypM -> ExpM -> (ExpM -> MkExpM) -> TypeEvalM ExpM
rwReduceGenerate inf element elt_repr reducer init other_args size count producer =
  -- Create a sequential loop.
  -- In each loop iteration, generate a value and combine it with the accumulator.
  liftFreshVarM $
  varAppE (pyonBuiltin the_for) [size, element]
  (return elt_repr :
   return count :
   return init :
   (lamE $ mkFun []
   (\ [] -> return ([ValPT Nothing ::: intType, ReadPT ::: fromTypM element,
                     OutPT ::: fromTypM element],
                    SideEffectRT ::: fromTypM element))
   (\ [] [ix, acc, ret] -> do
       tmpvar <- newAnonymousVar ObjectLevel
       let tmpvar_binder = localVarP tmpvar (fromTypM element) elt_repr
       -- Produce a new value
       rhs <- appE (producer (ExpM $ VarE defaultExpInfo ix)) [] [varE tmpvar]
       -- Combine with accumulator
       body <- appE (return reducer) [] [varE acc, varE tmpvar, varE ret]
       return $ ExpM $ LetE defaultExpInfo tmpvar_binder rhs body)) :
   map return other_args)

rwReduce1Stream :: RewriteRule
rwReduce1Stream inf [shape_type, element]
  (elt_repr : reducer : stream : other_args) =
  case interpretStream2 (fromTypM shape_type) (fromTypM element)
       elt_repr stream
  of Just s@(GenerateStream {})
       | Array1DShape size_arg size_val <- sexpShape s ->
           fmap Just $
           rwReduce1Generate inf element elt_repr reducer other_args
           size_arg size_val (_sexpGenerator s)
     _ -> return Nothing

rwReduce1Stream _ _ _ = return Nothing

rwReduce1Generate inf element elt_repr reducer other_args size count producer = do
  producer_var <- newAnonymousVar ObjectLevel
  producer_fn <- mkFun []
    (\ [] -> return ([ValPT Nothing ::: intType],
                     BoxRT ::: FunT (OutPT ::: fromTypM element) (SideEffectRT ::: fromTypM element)))
    (\ [] [index] -> producer $ ExpM $ VarE defaultExpInfo index)

  -- Get the first value.
  -- The code may crash at runtime if there aren't any values.
  tmpvar <- newAnonymousVar ObjectLevel
  let tmpvar_binder = localVarP tmpvar (fromTypM element) elt_repr
  rhs <- liftFreshVarM $ varAppE producer_var [] [litE (IntL 0 intType), varE tmpvar]
  
  -- Loop over the remaining values
  let producer_plus_1 index =
        varAppE producer_var []
        [varAppE (pyonBuiltin the_AdditiveDict_int_add) []
         [return index, litE (IntL 1 intType)]]
  
  let size_minus_1 = TypM $ varApp (pyonBuiltin the_minus_i)
                     [fromTypM size, IntT 1]
  count_minus_1 <-
    liftFreshVarM $ 
    varAppE (pyonBuiltin the_minus_ii)
    [size, TypM $ IntT 1]
    [return count, varE (pyonBuiltin the_one_ii)]

  body <- rwReduceGenerate inf element elt_repr reducer
          (ExpM $ VarE defaultExpInfo tmpvar) other_args size_minus_1 count_minus_1 producer_plus_1
          
  -- Build a let expression
  return $ ExpM $ LetfunE defaultExpInfo (NonRec (mkDef producer_var producer_fn)) $
           ExpM $ LetE defaultExpInfo tmpvar_binder rhs body

-- | Inline a call of \'for\'.
--
-- > for (n, a, repr, count, init, f, ret)
--
-- -->
--
-- > case count of IndexedInt bound.
-- >   letrec loop i acc ret' =
-- >     if i == bound
-- >     then copy (a, repr, acc, ret')
-- >     else local acc2 = f i acc acc2
-- >          loop (i + 1) acc2 ret'
-- >   loop 0 init ret'
rwFor :: RewriteRule
rwFor inf [TypM size_ix, TypM acc_type] args =
  case args
  of [acc_repr, size, init, fun, ret] -> do
       tenv <- getTypeEnv
       fmap Just $
         rewrite_for_loop tenv acc_repr size init fun (Just ret)
     [acc_repr, size, init, fun] -> do
       tenv <- getTypeEnv
       fmap Just $
         rewrite_for_loop tenv acc_repr size init fun Nothing
     _ -> return Nothing
  where
    rewrite_for_loop tenv acc_repr size init fun maybe_ret =
      caseOfIndexedInt tenv (return size) size_ix $ \bound -> do
        loop_var <- newAnonymousVar ObjectLevel
        loop_fun <-
          mkFun []
          (\ [] -> return ([ ValPT Nothing ::: intType
                           , ReadPT ::: acc_type
                           , OutPT ::: acc_type],
                           SideEffectRT ::: acc_type))
          (\ [] [i, acc, retvar] -> do
              ifE (varAppE (pyonBuiltin the_EqDict_int_eq) []
                   [varE i, varE bound])
                (varAppE (pyonBuiltin the_copy) [TypM acc_type]
                 [return acc_repr, varE acc, varE retvar])
                (localE (TypM acc_type) acc_repr
                 (\lv -> appE (return fun) [] [varE i, varE acc, return lv])
                 (\lv -> varAppE loop_var []
                         [varAppE (pyonBuiltin the_AdditiveDict_int_add) []
                          [varE i, litE $ IntL 1 intType],
                          return lv,
                          varE retvar])))
        let loop_arguments = litE (IntL 0 intType) :
                             return init :
                             maybeToList (fmap return maybe_ret)
        loop_call <- varAppE loop_var [] loop_arguments
        return $ letfunE (Rec [mkDef loop_var loop_fun]) loop_call

-- | Inline a definition of the safeSubscript function
--
-- > if (i < 0 || i >= size)
-- > then exception 
-- > else array[i]
rwSafeSubscript :: RewriteRule
rwSafeSubscript inf [elt_type] [elt_repr, list, ix] = do
  -- Create a function taking the un-applied parameters
  tenv <- getTypeEnv
  fmap Just $
    lamE $ mkFun []
    (\ [] -> return ([OutPT ::: fromTypM elt_type],
                     SideEffectRT ::: fromTypM elt_type))
    (\ [] [out_ptr] ->
      rwSafeSubscriptBody tenv inf elt_type elt_repr list ix (varE out_ptr))
 
rwSafeSubscript inf [elt_type] [elt_repr, list, ix, dst] = do
  tenv <- getTypeEnv
  fmap Just $
    rwSafeSubscriptBody tenv inf elt_type elt_repr list ix (return dst)
 
rwSafeSubscript _ _ _ = return Nothing

rwSafeSubscriptBody :: TypeEnv -> ExpInfo -> TypM -> ExpM
                    -> ExpM -> ExpM -> TypeEvalM ExpM -> TypeEvalM ExpM
rwSafeSubscriptBody tenv inf elt_type elt_repr list ix ret =
  caseOfList tenv (return list) elt_type $ \size_ix size array ->
  caseOfIndexedInt tenv (varE size) (VarT size_ix) $ \size_int -> do
    ix_var <- newAnonymousVar ObjectLevel
    subscript_expr <-
      ifE (varAppE (pyonBuiltin the_or) []
           [varAppE (pyonBuiltin the_OrdDict_int_lt) []
            [varE ix_var, litE (IntL 0 intType)],
            varAppE (pyonBuiltin the_OrdDict_int_ge) []
            [varE ix_var, varE size_int]])
      (exceptE (SideEffectRT ::: fromTypM elt_type))
      (varAppE (pyonBuiltin the_copy) [elt_type]
       [return elt_repr,
        varAppE (pyonBuiltin the_subscript) [TypM (VarT size_ix), elt_type]
        [return elt_repr, varE array, varE ix_var],
        ret])
      
    return $
      letE (memVarP ix_var (ValPT Nothing ::: intType)) ix subscript_expr

-------------------------------------------------------------------------------

-- | An argument to one of the 'zip' family of functions.
data ZipArg =
  ZipArg
  { zipElementType     :: TypM  -- ^ The data type stored in the contianer
  , zipElementDict     :: ExpM  -- ^ @Repr@ of the element
  , zipContainerValue  :: ExpM  -- ^ The container value
  }
     
-- | Generalized rewriting of zip_N to zipStream_N.  Takes a list of inputs
--   and the output as parameters.
generalizedRewriteZip :: TypeEnv -> ExpInfo -> [ZipArg] -> TypM -> ExpM
                      -> [ExpM]
                      -> TypeEvalM ExpM
generalizedRewriteZip tenv inf inputs container traversable other_args =
  caseOfTraversableDict tenv (return traversable) container $ \trv bld ->
  let tuple_size = length inputs
      field_types = map zipElementType inputs
      tuple_type = varApp (pyonTupleTypeCon tuple_size) (map fromTypM field_types)
      tuple_repr = varAppE (pyonTupleReprCon tuple_size) field_types
                   (map (return . zipElementDict) inputs)
      app_other_args = map return other_args
  in varAppE bld [TypM tuple_type]
     (tuple_repr :
      varAppE (zipper tuple_size) (shapeOfType container : field_types)
      ([return $ zipElementDict input | input <- inputs] ++
       [varAppE trv [zipElementType input]
        [return $ zipElementDict input, return $ zipContainerValue input] 
       | input <- inputs]) :
      app_other_args)

zipper 2 = pyonBuiltin the_fun_zip_Stream
zipper 3 = pyonBuiltin the_fun_zip3_Stream
zipper 4 = pyonBuiltin the_fun_zip4_Stream
zipper n = internalError $ "zipper: Cannot zip " ++ show n ++ " streams"

-- | The iteration domain of a stream
data Shape =
    -- | An unbounded stream
    UnboundedShape
    -- | A 1D array stream with a type index and size expression
  | Array1DShape TypM ExpM
    -- | An unknown iteration domain that has the given shape index
  | UnknownShape TypM

-- | Return a type that is a valid type index for the given shape.
shapeType :: Shape -> Type
shapeType shp = 
  case shp
  of UnboundedShape              -> VarT $ pyonBuiltin the_list_shape
     Array1DShape (TypM index) _ -> varApp (pyonBuiltin the_array_shape) [index]
     UnknownShape (TypM s_index) -> s_index
  
-- | Get the shape encoded in a type.
typeShape :: Type -> Shape
typeShape ty = UnknownShape (TypM ty)

listShape = UnknownShape (TypM (VarT $ pyonBuiltin the_list_shape))

-- | The interpreted value of a stream.
data instance Exp Stream =
    GenerateStream
    { -- | The stream's shape
      _sexpShape :: !Shape

      -- | The type of a stream element
    , _sexpType :: Type

      -- | The representation dictionary of a stream element
    , _sexpRepr :: ExpM

      -- | Given an expression that evaluates to the index of the desired
      --   stream element (with type @val int@), produce an expression that
      --   evaluates to the desired stream element, as a write reference. 
    , _sexpGenerator :: ExpM -> TypeEvalM ExpM
    }
  | BindStream
    { -- | The source stream
      _sexpSrcStream :: ExpS

      -- | The transformer,
      --   which is a one-parameter function returning a stream
    , _sexpTransStream :: (PatM, ExpS)
    }
  | CaseStream
    { -- | The stream's shape
      _sexpShape :: !Shape
    , _sexpScrutinee :: ExpM
    , _sexpAlternatives :: [AltS]
    }
    -- | A stream with exactly one element.
    -- The expression is a writer function.
  | ReturnStream
    { _sexpType :: Type
    , _sexpRepr :: ExpM
    , _sexpWriter :: TypeEvalM ExpM
    }
    -- | An empty stream.  The stream has list shape.
  | EmptyStream
    { _sexpType :: Type
    , _sexpRepr :: ExpM
    }
    -- | An unrecognized stream expression.  We can't transform the expression,
    --   but if it occurs inside a larger stream expression we may still be
    --   able to transform the parts that can be interpreted.
  | UnknownStream
    { _sexpShape :: Shape
    , _sexpType :: Type
    , _sexpRepr :: ExpM
    , _sexpExp :: ExpM
    }

-- | Get the shape of a stream
sexpShape :: ExpS -> Shape
sexpShape (GenerateStream {_sexpShape = s}) = s
sexpShape (BindStream _ _) = UnknownShape (TypM $ VarT $ pyonBuiltin the_list_shape)
sexpShape (CaseStream {_sexpShape = s}) = s
sexpShape (ReturnStream {}) = UnknownShape (TypM $ VarT $ pyonBuiltin the_list_shape)
sexpShape (EmptyStream {}) = UnknownShape (TypM $ VarT $ pyonBuiltin the_list_shape)
sexpShape (UnknownStream {_sexpShape = s}) = s

-- | Get the type of a stream element
sexpElementType :: ExpS -> Type
sexpElementType (GenerateStream {_sexpType = t}) = t
sexpElementType (BindStream _ (_, s)) = sexpElementType s
sexpElementType (CaseStream {_sexpAlternatives = alt:_}) =
  sexpElementType $ altBody $ fromAltS alt
sexpElementType (ReturnStream {_sexpType = t}) = t
sexpElementType (EmptyStream {_sexpType = t}) = t
sexpElementType (UnknownStream {_sexpType = t}) = t

-- | Get the representation dictionary of a stream element
sexpElementRepr :: ExpS -> ExpM
sexpElementRepr (GenerateStream {_sexpRepr = e}) = e
sexpElementRepr (BindStream _ (_, s)) = sexpElementRepr s
sexpElementRepr (CaseStream {_sexpAlternatives = alt:_}) =
  sexpElementRepr $ altBody $ fromAltS alt
sexpElementRepr (ReturnStream {_sexpRepr = e}) = e
sexpElementRepr (EmptyStream {_sexpRepr = e}) = e
sexpElementRepr (UnknownStream {_sexpRepr = e}) = e

newtype instance Alt Stream = AltS {fromAltS :: BaseAlt Stream}

newtype instance Typ Stream = TypS {fromTypS :: Type}
newtype instance TyPat Stream = TyPatS {fromTyPatS :: TyPatM}
newtype instance Pat Stream = PatS {fromPatS :: PatM}

type ExpS = Exp Stream
type TypS = Typ Stream
type TyPatS = TyPat Stream
type PatS = Pat Stream
type AltS = Alt Stream

pprExpS :: ExpS -> Doc
pprExpS stream =
  case stream
  of GenerateStream shp ty repr gen ->
       text "generate" <+> parens (pprType ty) <+> text "(...)"
     BindStream src (pat, trans) ->
       text "bind" $$
       pprPat pat <+> text "<-" $$
       nest 4 (pprExpS src) $$
       pprExpS trans
     CaseStream shp scr alts ->
       text "case" <+> pprExp scr $$
       text "of" <+> vcat (map pprAltS alts)
     ReturnStream ty repr writer ->
       text "return" <+> parens (pprType ty) <+> text "(...)"
     EmptyStream ty repr ->
       text "empty" <+> parens (pprType ty)
     UnknownStream shp ty repr exp ->
       text "unknown" <+> parens (pprType ty) $$
       nest 4 (braces $ pprExp exp)

pprAltS (AltS alt) =
  let con_doc = pprVar $ altConstructor alt
      args_doc = pprParenList [pprType t | TypS t <- altTyArgs alt]
      ex_types_doc = map (parens . pprTyPat . fromTyPatS) $ altExTypes alt
      params_doc = map (parens . pprPat . fromPatS) $ altParams alt
      body_doc = pprExpS $ altBody alt
  in con_doc <+> sep (args_doc : ex_types_doc ++ params_doc) <> text "." $$
     nest 2 body_doc

-- | Given a stream and the type and repr of a stream element, get its shape.
--
--   We may change the stream's type by ignoring functions that only
--   affect the advertised stream shape.
interpretStream2 :: Type -> Type -> ExpM -> ExpM -> Maybe ExpS
interpretStream2 shape_type elt_type repr expression =
  -- If we didn't interpret anything useful, then return Nothing
  case interpretStream2' shape_type elt_type repr expression
  of s@(UnknownStream {}) -> Nothing
     s -> Just s

interpretStream2' shape_type elt_type repr expression =
  case unpackVarAppM expression
  of Just (op_var, ty_args, args)
       | op_var `isPyonBuiltin` the_TraversableDict_Stream_traverse ||
         op_var `isPyonBuiltin` the_TraversableDict_Stream_build ->
         -- These are identity functions
         case args
         of [_, stream_arg] ->
              interpretStream2' shape_type elt_type repr stream_arg
       | op_var `isPyonBuiltin` the_fun_asList_Stream ->
         case (ty_args, args)
         of ([shape_type2, _], [stream_arg]) ->
              interpretStream2' shape_type2 elt_type repr stream_arg
       | op_var `isPyonBuiltin` the_generate ->
         let [size_arg, type_arg] = ty_args
             [size_val, repr, writer] = args
         in GenerateStream
            { _sexpShape = Array1DShape (TypM size_arg) size_val
            , _sexpType = type_arg
            , _sexpRepr = repr
            , _sexpGenerator = \ix ->
                appE (return writer) [] [return ix]}
       | op_var `isPyonBuiltin` the_count ->
           GenerateStream
           { _sexpShape = UnboundedShape
           , _sexpType = intType
           , _sexpRepr = repr
           , _sexpGenerator = counting_generator}
       | op_var `isPyonBuiltin` the_rangeIndexed ->
         let [size_index] = ty_args
             [size_val] = args
         in GenerateStream
            { _sexpShape = Array1DShape (TypM size_index) size_val
            , _sexpType = intType
            , _sexpRepr = repr
            , _sexpGenerator = counting_generator}
       | op_var `isPyonBuiltin` the_oper_CAT_MAP ->
         let [src_type, tr_type] = ty_args
         in case args
            of [src_repr, _, src, transformer] ->
                 -- Transformer must be a single-parameter lambda function
                 case transformer
                 of ExpM (LamE _ (FunM (Fun { funTyParams = []
                                            , funParams = [param]
                                            , funBody = body}))) ->
                      let src_stream =
                            interpretStream2' list_shape src_type src_repr src
                          body_stream =
                            interpretStream2' list_shape tr_type repr body
                      in BindStream src_stream (param, body_stream)
                    _ -> no_interpretation
               _ -> no_interpretation
       | op_var `isPyonBuiltin` the_oper_DO ->
         let [type_arg] = ty_args
         in case args
            of [repr, writer] ->
                 ReturnStream type_arg repr (return writer)
               _ -> no_interpretation
       | op_var `isPyonBuiltin` the_oper_EMPTY ->
         let [type_arg] = ty_args
         in case args
            of [repr] -> EmptyStream type_arg repr
               _ -> no_interpretation
       | op_var `isPyonBuiltin` the_fun_map_Stream ->
         let [_, src_type, out_type] = ty_args
         in case args
            of [src_repr, out_repr, transformer, producer] ->
                 mapStream out_type out_repr transformer $
                 interpretStream2' shape_type src_type src_repr producer
               _ -> no_interpretation
     _ -> case fromExpM expression
          of CaseE _ scr alts ->
               let alts' = map (interpretStreamAlt shape_type elt_type repr) alts
                   shape = case alts'
                           of [alt] -> sexpShape $ altBody $ fromAltS alt
                              _ -> typeShape shape_type
               in CaseStream shape scr alts'
             _ -> no_interpretation
  where
    list_shape = VarT $ pyonBuiltin the_list_shape

    -- A generator for the sequence [0, 1, 2, ...]
    counting_generator ix =
      varAppE (pyonBuiltin the_store) [TypM intType] [return ix]

    no_interpretation =
      UnknownStream (typeShape shape_type) elt_type repr expression

-- | Map a function over the interpreted stream
mapStream :: Type               -- ^ Transformed type
          -> ExpM               -- ^ Transformed repr
          -> ExpM               -- ^ Transformer
          -> ExpS               -- ^ Producer stream
          -> ExpS               -- ^ Transformed stream
mapStream out_type out_repr transformer producer = transform producer
  where
    transform (GenerateStream shape ty repr gen) =
      -- Fuse the transformer into the generator expression
      let gen' ix = apply_transformer ty repr (gen ix)
      in GenerateStream shape out_type out_repr gen'

    transform (BindStream src (binder, body)) =
      BindStream src (binder, transform body)

    transform (CaseStream shp scr alts) =
      CaseStream shp scr (map transform_alt alts)
        
    transform (ReturnStream ty repr writer) =
      let writer' = apply_transformer ty repr writer
      in ReturnStream out_type out_repr writer'

    transform (EmptyStream _ _) =
      EmptyStream out_type out_repr

    transform (UnknownStream shp in_type in_repr expr) =
      -- Can't simplify; build a "map" expression
      UnknownStream shp out_type out_repr $
      ExpM $ AppE defaultExpInfo (ExpM $ VarE defaultExpInfo (pyonBuiltin the_fun_map_Stream))
      [TypM (shapeType shp), TypM in_type, TypM out_type]
      [in_repr, out_repr, transformer, expr]

    transform_alt (AltS alt) =
      let body = transform $ altBody alt
      in AltS $ alt {altBody = body}

    -- Apply the transformer function to the given expression's result.
    -- The given expression and the returned expression are both writer
    -- functions.
    apply_transformer :: Type -> ExpM -> TypeEvalM ExpM -> TypeEvalM ExpM
    apply_transformer producer_ty producer_repr producer_expr =
      lamE $ mkFun []
      (\ [] -> return ([OutPT ::: out_type], SideEffectRT ::: out_type))
      (\ [] [outvar] -> do
          tmpvar <- newAnonymousVar ObjectLevel

          -- Compute the input to 'map'
          rhs <- appE producer_expr [] [varE tmpvar]

          -- Compute the output of 'map'
          body <- appE (return transformer) [] [varE tmpvar, varE outvar]
          let binder = localVarP tmpvar producer_ty producer_repr
              let_expr = ExpM $ LetE defaultExpInfo binder rhs body
          return let_expr)

interpretStreamAlt :: Type -> Type -> ExpM -> AltM -> AltS
interpretStreamAlt shape_type elt_type repr (AltM alt) =
  let body = interpretStream2' shape_type elt_type repr $ altBody alt
  in AltS $ Alt { altConstructor = altConstructor alt
                , altTyArgs = map (TypS . fromTypM) $ altTyArgs alt
                , altExTypes = map TyPatS $ altExTypes alt
                , altParams = map PatS $ altParams alt
                , altBody = body}

-- | Produce program code of an interpreted stream.  The generated code
--   will have the specified shape.  If code cannot be generated,
--   return Nothing.
encodeStream2 :: TypM -> ExpS -> TypeEvalM (Maybe ExpM)
encodeStream2 expected_shape stream = runMaybeT $ do
  encoded <-
    case stream
    of GenerateStream {_sexpGenerator = gen} ->
         case sexpShape stream
         of Array1DShape size_ix size_val ->
              lift $
              varAppE (pyonBuiltin the_generate)
              [size_ix, TypM elt_type]
              [return size_val,
               return elt_repr,
               lamE $ mkFun []
               (\ [] -> return ([ValPT Nothing ::: intType],
                                BoxRT ::: FunT (OutPT ::: elt_type)
                                               (SideEffectRT ::: elt_type)))
               (\ [] [index_var] ->
                 gen (ExpM $ VarE defaultExpInfo index_var))]

       BindStream src (pat, dst) -> do
         src' <- MaybeT $ encodeStream2 (TypM list_shape) src
         dst' <- MaybeT $ encodeStream2 (TypM list_shape) dst
         let oper = ExpM $ VarE defaultExpInfo (pyonBuiltin the_oper_CAT_MAP)
         return $
           ExpM $ AppE defaultExpInfo oper
           [TypM $ sexpElementType src, TypM $ sexpElementType dst]
           [sexpElementRepr src, sexpElementRepr dst,
            src',
            ExpM $ LamE defaultExpInfo $
            FunM $ Fun { funInfo = defaultExpInfo
                       , funTyParams = []
                       , funParams = [pat]
                       , funReturn =
                         RetM $ BoxRT :::
                         varApp (pyonBuiltin the_Stream)
                         [list_shape, sexpElementType dst]
                       , funBody = dst'}]

       CaseStream shp scr alts -> do
         alts' <- mapM (encode_alt (TypM $ shapeType shp)) alts
         return $ ExpM $ CaseE defaultExpInfo scr alts'

       ReturnStream ty repr writer -> do
         let oper = ExpM $ VarE defaultExpInfo (pyonBuiltin the_oper_DO)
         writer_exp <- lift writer
         return $ ExpM $ AppE defaultExpInfo oper [TypM ty] [repr, writer_exp]

       EmptyStream ty repr -> do
         let oper = ExpM $ VarE defaultExpInfo (pyonBuiltin the_oper_EMPTY)
         return $ ExpM $ AppE defaultExpInfo oper [TypM ty] [repr]

       UnknownStream _ _ _ expr -> return expr

       _ -> mzero

  -- Cast the shape type to the one that the code expects
  let given_shape = shapeType s_shape
  MaybeT $ castStreamExpressionShape (fromTypM expected_shape) given_shape elt_type elt_repr encoded
  where
    list_shape = VarT (pyonBuiltin the_list_shape)
    s_shape = sexpShape stream
    elt_type = sexpElementType stream
    elt_repr = sexpElementRepr stream
    
    encode_alt expected_shape (AltS alt) = do
      body <- MaybeT $ encodeStream2 expected_shape $ altBody alt
      return $ AltM $ Alt { altConstructor = altConstructor alt
                          , altTyArgs = map (TypM . fromTypS) $ altTyArgs alt
                          , altExTypes = map fromTyPatS $ altExTypes alt
                          , altParams = map fromPatS $ altParams alt
                          , altBody = body}

-- | Convert a stream over an integer domain into a stream over
--   an arbitrary, contiguous subset of the integer domain.
--   Return the new stream and the size (type index and value)
--   of the original domain.
--   The variables are the size of the subset (a type index),
--   the size of the subset (an indexed int), and the first element of the
--   subset (an ordinary int).
--
--   The returned stream will have an array shape.
blockStream :: Var -> Var -> Var -> ExpS -> Maybe (ExpS, TypM, ExpM)
blockStream size_var count_var base_var stream =
  case stream
  of GenerateStream (Array1DShape orig_size orig_count) ty repr gen ->
       -- We don't generate values starting from zero, but rather starting
       -- from the given base.  Add the base to the index.
       let gen' ix = do
             ix' <- varAppE (pyonBuiltin the_AdditiveDict_int_add) []
                    [return ix, varE base_var]
             gen ix'
       
           shape = Array1DShape (TypM (VarT size_var))
                   (ExpM $ VarE defaultExpInfo count_var)
       in return (GenerateStream shape ty repr gen', orig_size, orig_count)

     BindStream src tf -> do
       -- block the source stream
       (src', orig_size, orig_count) <-
         blockStream size_var count_var base_var src
       return (BindStream src' tf, orig_size, orig_count)

     CaseStream _ scr [AltS alt] -> do
       -- block the single alternative
       (body, orig_size, orig_count) <-
         blockStream size_var count_var base_var $ altBody alt
       let alt' = alt {altBody = body}
           shp = sexpShape body
       return (CaseStream shp scr [AltS alt'], orig_size, orig_count)
     
     CaseStream (Array1DShape orig_size orig_count) scr alts -> do
       -- Block each branch of the case statement.  All branches must 
       -- have the same shape. 
       alts' <- forM alts $ \ (AltS alt) -> do 
         (body, _, _) <- blockStream size_var count_var base_var $ altBody alt
         return $ AltS $ alt {altBody = body}
       let shp = Array1DShape (TypM (VarT size_var))
                 (ExpM $ VarE defaultExpInfo count_var)
       return (CaseStream shp scr alts', orig_size, orig_count)

     _ ->
       -- The stream's shape is unknown, so we can't decompose it into blocks
       Nothing

-- | Interpret a stream and attempt to create a blocked version of it.
interpretAndBlockStream :: Type -> Type -> ExpM -> ExpM
                        -> TypeEvalM (Maybe (Var, Var, Var, ExpS, TypM, ExpM))
interpretAndBlockStream shape_type elt_type elt_repr stream_exp =  
  case interpretStream2 shape_type elt_type elt_repr stream_exp
  of Just s -> do
       -- Create a block-wise version of the stream
       size_var <- newAnonymousVar TypeLevel
       count_var <- newAnonymousVar ObjectLevel
       base_var <- newAnonymousVar ObjectLevel
       
       case blockStream size_var count_var base_var s of
         Nothing ->
           return Nothing
         Just (bs, bs_size, bs_count) ->
           return $ Just (size_var, count_var, base_var, bs, bs_size, bs_count)
     Nothing -> return Nothing

-- | Zip together a list of two or more streams
zipStreams2 :: [ExpS] -> Maybe ExpS
zipStreams2 [] = internalError "zipStreams: Need at least one stream"
zipStreams2 [s] = Just s
zipStreams2 ss
  | Just shape <- zipped_shape =
      let elt_types = map sexpElementType ss
          typ = varApp (pyonTupleTypeCon num_streams) elt_types
          repr = ExpM $ AppE defaultExpInfo
                 (ExpM $ VarE defaultExpInfo (pyonTupleReprCon num_streams))
                 (map TypM elt_types)
                 (map sexpElementRepr ss)
          gen ix = varAppE (pyonTupleCon num_streams)
                   (map TypM elt_types)
                   [_sexpGenerator stream ix | stream <- ss] -- FIXME: Handle other stream types
      in Just $ GenerateStream shape typ repr gen
  | otherwise = Nothing         -- Can't determine length of stream
  where
    num_streams = length ss

    zipped_shape = foldr combine_shapes (Just UnboundedShape) $ map sexpShape ss
          
    -- Combine shapes if possible. 
    -- Array shapes are combined using the "min" operator to get the
    -- minimum value.
    combine_shapes _              Nothing = Nothing 
    combine_shapes shp'           (Just UnboundedShape) = Just shp'
    combine_shapes UnboundedShape (Just shp) = Just shp
    combine_shapes shp'           (Just (Array1DShape typ1 val1)) =
      case shp'
      of Array1DShape typ2 val2 ->
           let typ = TypM $
                     varApp (pyonBuiltin the_min_i) [fromTypM typ1, fromTypM typ2]
               val = ExpM $ AppE defaultExpInfo min_ii [typ1, typ2] [val1, val2] 
           in Just $ Array1DShape typ val
         _ -> Nothing
    combine_shapes shp'           mshp@(Just (UnknownShape _)) =
      case shp'
      of UnknownShape _ -> mshp
         _ -> Nothing
    
    min_ii = ExpM $ VarE defaultExpInfo (pyonBuiltin the_min_ii)

-- | Translate a stream to a sequential \'fold\' operation.
--   This function deals with variability in the number of given arguments. 
translateStreamToFoldWithExtraArgs ::
    TypeEnv
 -> Type   -- ^ Accumulator type
 -> ExpM   -- ^ Accumulator representation
 -> ExpM   -- ^ Initial value
 -> ExpM   -- ^ Accumulator function
 -> ExpS   -- ^ Stream to be translated
 -> [ExpM]                      -- ^ Zero or one extra arguments
 -> TypeEvalM ExpM -- ^ Translated expression
translateStreamToFoldWithExtraArgs
  tenv acc_ty acc_repr init acc_f stream [out_ptr] =
    translateStreamToFold tenv acc_ty acc_repr init acc_f out_ptr stream

translateStreamToFoldWithExtraArgs
  tenv acc_ty acc_repr init acc_f stream [] =
    lamE $ mkFun []
    (\ [] -> return ([OutPT ::: acc_ty], SideEffectRT ::: acc_ty))
    (\ [] [out_ptr] ->
      let out_arg = ExpM $ VarE defaultExpInfo out_ptr
      in translateStreamToFold tenv acc_ty acc_repr init acc_f out_arg stream)

translateStreamToFoldWithExtraArgs
  tenv acc_ty acc_repr init acc_f stream _ =
    -- Other numbers of arguments are ill-typed
    internalError "translateStreamToFoldWithExtraArgs"

-- | Translate a stream to a sequential \'fold\' operation.  The generated
--   code returns the final accumulator value after folding over all stream
--   elements.
--
--   The accumulator function has type @(read acc -> read a -> write acc)@
--   where @a@ is the stream's element type and @acc@ is the accumulator type.
--
--   The translated expression is a writer that writes a value of the
--   accumulator type.
translateStreamToFold :: TypeEnv
                      -> Type   -- ^ Accumulator type
                      -> ExpM   -- ^ Accumulator representation
                      -> ExpM   -- ^ Initial value
                      -> ExpM   -- ^ Accumulator function
                      -> ExpM   -- ^ Output pointer
                      -> ExpS   -- ^ Stream to be translated
                      -> TypeEvalM ExpM -- ^ Translated expression
translateStreamToFold tenv acc_ty acc_repr init acc_f out_ptr stream =
  case stream
  of GenerateStream {} ->
       case sexpShape stream
       of Array1DShape size_ix size_val ->
            varAppE (pyonBuiltin the_for)
            [size_ix, TypM acc_ty]
            [return acc_repr,
             return size_val,
             return init,
             lamE $ mkFun []
             (\ [] -> return ([ValPT Nothing ::: intType,
                               ReadPT ::: acc_ty,
                               OutPT ::: acc_ty],
                              SideEffectRT ::: acc_ty))
             (\ [] [index_var, acc_in, acc_out] ->
               -- Call the generator function,
               -- bind its result to a local variable
               let ix = ExpM $ VarE defaultExpInfo index_var
               in localE (TypM $ sexpElementType stream) (sexpElementRepr stream)
                  (\lv -> appE (_sexpGenerator stream ix) [] [return lv])
                  (\lv -> appE (return acc_f) []
                          [varE acc_in, return lv, varE acc_out])),
             return out_ptr]

     BindStream src (binder, trans) -> do
       let src_out_ty = sexpElementType src

       -- Create a new accumulator function that runs the transformer stream 
       -- and folds over it.  It will be used as the source stream's  
       -- accumulator.  The accumulator function has 'binder' as one of
       -- its parameters.
       consumer <- do
         acc_in_var <- newAnonymousVar ObjectLevel
         let m_producer_var = patMVar binder
         acc_out_var <- newAnonymousVar ObjectLevel
         let params = [memVarP acc_in_var (ReadPT ::: acc_ty),
                       binder,
                       memVarP acc_out_var (OutPT ::: acc_ty)]
             retn = RetM (SideEffectRT ::: acc_ty)
         let local_init = ExpM $ VarE defaultExpInfo acc_in_var
         let local_out = ExpM $ VarE defaultExpInfo acc_out_var
         body <- translateStreamToFold tenv acc_ty acc_repr local_init acc_f local_out trans
         return $ ExpM $ LamE defaultExpInfo $
           FunM $ Fun { funInfo = defaultExpInfo
                      , funTyParams = []
                      , funParams = params
                      , funReturn = retn
                      , funBody = body}

       -- Fold over the source stream
       translateStreamToFold tenv acc_ty acc_repr init consumer out_ptr src

     CaseStream shp scr alts -> do
       -- Translate each case alternative
       alts' <- forM alts $ \(AltS alt) -> do
         new_body <-
           translateStreamToFold tenv acc_ty acc_repr init acc_f out_ptr (altBody alt)
         return $ AltM $ Alt { altConstructor = altConstructor alt
                             , altTyArgs = 
                                 map (TypM . fromTypS) $ altTyArgs alt
                             , altExTypes = map fromTyPatS $ altExTypes alt
                             , altParams = map fromPatS $ altParams alt
                             , altBody = new_body}

       return $ ExpM $ CaseE defaultExpInfo scr alts'

     ReturnStream ty repr writer -> do
       -- Run the writer, bind its result to a local variable
       localE (TypM ty) repr
         (\lv -> appE writer [] [return lv])
         (\lv -> appE (return acc_f) []
                 [return init, return lv, return out_ptr])

     EmptyStream ty repr -> do
       -- Just return the initial value of the accumulator
       let copy_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_copy)
       return $ ExpM $
         AppE defaultExpInfo copy_op [TypM acc_ty] [acc_repr, init, out_ptr]
         
     UnknownStream shp ty repr expr -> do
       -- Fold over this uninterpreted stream
       let op = ExpM $ VarE defaultExpInfo $ pyonBuiltin the_fun_fold_Stream
           
       -- Cast to list shape, which always succeeds
       Just list_stream <-
         castStreamExpressionShape (VarT $ pyonBuiltin the_list_shape) (shapeType shp) ty repr expr
       return $ ExpM $ AppE defaultExpInfo op [TypM ty, TypM acc_ty]
          [repr, acc_repr, acc_f, init, list_stream, out_ptr]       
         
-- | Cast a stream of type @Stream given elt@ to a stream of type
--   @Stream expected elt@.
castStreamExpressionShape :: Type -> Type -> Type -> ExpM -> ExpM -> TypeEvalM (Maybe ExpM)
castStreamExpressionShape expected_shape given_shape elt_type elt_repr expr = do
  e_whnf <- reduceToWhnf expected_shape
  g_whnf <- reduceToWhnf given_shape
  return $ subcast e_whnf g_whnf expr
  where
    subcast e_shape g_shape expr =
      case fromVarApp e_shape
      of Just (e_op, e_args)
           | e_op `isPyonBuiltin` the_list_shape ->
             case fromVarApp g_shape
             of Just (g_op, g_args)
                  | g_op `isPyonBuiltin` the_list_shape -> Just expr
                  | otherwise ->
                      -- Reinterpret as a list
                      Just $ cast (pyonBuiltin the_fun_asList_Stream)
                             [TypM g_shape, TypM elt_type] [expr]
                _ -> Nothing

           | e_op `isPyonBuiltin` the_array_shape ->
               case fromVarApp g_shape
               of Just (g_op, g_args)
                    | g_op `isPyonBuiltin` the_array_shape ->
                        -- Should verify that array size matches here.
                        -- Since the input program was well-typed, array size
                        -- /should/ match.
                        Just expr
                  _ -> Nothing
         _ -> Nothing
                  
    cast op ty_args args =
      ExpM $ AppE defaultExpInfo (ExpM $ VarE defaultExpInfo op) ty_args args

{-
-- | Convert a stream transformer that produces a singleton stream
--   into a function that writes its result.
unreturnStreamTransformer :: ExpM -> Maybe ExpM
unreturnStreamTransformer expr =
  case expr
  of ExpM (LamE inf (FunM f)) -> do
       -- The function takes a single parameter, which is a readable
       -- reference to a value of type @elt_type@.
       new_ret_type <- unreturn_return $ funReturn f
       new_body <- unreturnExp $ funBody f
       return $ ExpM $ LamE inf $ FunM $ f { funReturn = new_ret_type
                                           , funBody = new_body}
     _ -> mzero
  where
    -- Convert a return type of @box Stream a@ to @out a -> SideEffect a@
    unreturn_return (RetM (BoxRT ::: rt))
      | Just (op_var, [elt_type]) <- fromVarApp rt,
        op_var `isPyonBuiltin` the_Stream =
          return $ RetM (BoxRT ::: FunT (OutPT ::: elt_type) 
                                        (SideEffectRT ::: elt_type))

    unreturn_return _ = mzero

-- | Convert an expression whose return value is @return x@ stream into
--   an expression whose return value is @x@.
unreturnExp expression =
  case fromExpM expression
  of VarE {} -> Nothing
     LitE {} -> Nothing
     AppE inf (ExpM (VarE _ op_var)) ty_args [_, arg]
       | op_var `isPyonBuiltin` the_oper_DO -> Just arg
     AppE {} -> Nothing
     LetE inf bind rhs body -> 
       fmap ExpM $ fmap (LetE inf bind rhs) $ unreturnExp body
     LetfunE inf defs body ->
       fmap ExpM $ fmap (LetfunE inf defs) $ unreturnExp body
     CaseE inf scr alts ->
       fmap ExpM $ fmap (CaseE inf scr) $ mapM unreturnAlt alts

unreturnAlt (AltM alt) = do
  body <- unreturnExp $ altBody alt
  return $ AltM (alt {altBody = body})

-}