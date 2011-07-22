
module SystemF.Rewrite
       (insertGlobalSystemFFunctions,
        RewriteRuleSet,
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
import Type.Compare
import Type.Eval
import Type.Type
import GlobalVar
import Globals

-- | Insert the global, predefined function definitions into the module
insertGlobalSystemFFunctions :: Module Mem -> IO (Module Mem)
insertGlobalSystemFFunctions mod = do
  core_mod <- readInitGlobalVarIO the_coreModule
  let Module _ core_defs _ = core_mod
  let Module mod_name defs exports = mod
  return $ Module mod_name (core_defs ++ defs) exports

-- | Type index for stream expressions 
data Stream

liftFreshVarM :: FreshVarM a -> TypeEvalM a
liftFreshVarM m = TypeEvalM $ \supply _ -> runFreshVarM supply m

-------------------------------------------------------------------------------
-- Helper functions for writing code

-- | Load a value.
--
-- > case x of stored t (y : t). y
load :: TypeEnv
     -> TypM                    -- ^ Value type to load
     -> TypeEvalM ExpM          -- ^ Expression to load
     -> TypeEvalM ExpM
load tenv ty val =
  caseE val
  [mkAlt liftFreshVarM tenv (pyonBuiltin the_stored) [ty] $
   \ [] [val] -> varE val]

-- | Create a case expression to inspect a list.
--
-- > case scrutinee
-- > of make_list list_type (n : intindex)
-- >                        (sz : FinIndInt n) 
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

-- | Create a case expression to inspect a matrix.
--
-- > case scrutinee
-- > of make_matrix elt_type (m n : intindex)
-- >                         (s : FinIndInt m)
-- >                         (t : FinIndInt n)
-- >                         (p : Referenced (array m (array n elt_type))).
-- >      case p
-- >      of referenced ay. $(make_body m n s t ay)
caseOfMatrix tenv scrutinee elt_type mk_body =
  caseE scrutinee
  [mkAlt liftFreshVarM tenv (pyonBuiltin the_make_matrix) [elt_type] $
   \ [size_y_index, size_x_index] [size_y, size_x, array_ref] ->
   caseE (varE array_ref)
   [mkAlt liftFreshVarM tenv (pyonBuiltin the_referenced) [array_type size_y_index size_x_index] $
    \ [] [ay] -> mk_body size_y_index size_x_index size_y size_x ay]]
  where
    -- Create the type (array m (array n elt_type))
    array_type size_y_index size_x_index =
      TypM $ varApp (pyonBuiltin the_array) [VarT size_y_index,
                                             varApp (pyonBuiltin the_array) [VarT size_x_index, fromTypM elt_type]]

caseOfTraversableDict :: TypeEnv
                      -> TypeEvalM ExpM
                      -> TypM
                      -> (Var -> Var -> TypeEvalM ExpM)
                      -> TypeEvalM ExpM
caseOfTraversableDict tenv scrutinee container_type mk_body =
  caseE scrutinee
  [mkAlt liftFreshVarM tenv (pyonBuiltin the_traversableDict) [container_type] $
   \ [] [trv, bld] -> mk_body trv bld]

caseOfSomeIndInt :: TypeEnv
                 -> TypeEvalM ExpM
                 -> (Var -> Var -> TypeEvalM ExpM)
                 -> TypeEvalM ExpM
caseOfSomeIndInt tenv scrutinee mk_body =
  caseE scrutinee
  [mkAlt liftFreshVarM tenv (pyonBuiltin the_someIndInt) [] $
   \ [intindex] [intvalue] -> mk_body intindex intvalue]

defineAndInspectIndInt tenv int_value mk_body =
  let define_indexed_int =
        varAppE (pyonBuiltin the_defineIntIndex) [] [int_value]
  in caseOfSomeIndInt tenv define_indexed_int mk_body

caseOfFinIndInt :: TypeEnv
                -> TypeEvalM ExpM
                -> Type
                -> (Var -> Var -> TypeEvalM ExpM)
                -> TypeEvalM ExpM
caseOfFinIndInt tenv scrutinee int_index mk_body =
  caseE scrutinee
  [mkAlt liftFreshVarM tenv (pyonBuiltin the_finIndInt) [TypM int_index] $
   \ [] [pf, intvalue] -> mk_body pf intvalue]

caseOfIndInt :: TypeEnv
             -> TypeEvalM ExpM
             -> Type
             -> (Var -> TypeEvalM ExpM)
             -> (Var -> TypeEvalM ExpM)
             -> TypeEvalM ExpM
caseOfIndInt tenv scrutinee int_index mk_finite mk_infinite =
  caseE scrutinee
  [mkAlt liftFreshVarM tenv (pyonBuiltin the_indInt) [TypM int_index] $
   \ [] [fin] -> mk_finite fin,
   mkAlt liftFreshVarM tenv (pyonBuiltin the_indOmega) [TypM int_index] $
   \ [] [pf] -> mk_infinite pf]

caseOfIndInt' :: TypeEnv
              -> TypeEvalM ExpM
              -> Type
              -> (Var -> Var -> TypeEvalM ExpM)
              -> (Var -> TypeEvalM ExpM)
              -> TypeEvalM ExpM
caseOfIndInt' tenv scrutinee int_index mk_finite mk_infinite =
  caseE scrutinee
  [mkAlt liftFreshVarM tenv (pyonBuiltin the_indInt) [TypM int_index] $
   \ [] [fin] -> caseOfFinIndInt tenv (varE fin) int_index mk_finite,
   mkAlt liftFreshVarM tenv (pyonBuiltin the_indOmega) [TypM int_index] $
   \ [] [pf] -> mk_infinite pf]

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
            -> TypM             -- Array size type index (FinIntIndex)
            -> TypeEvalM ExpM   -- Array size
            -> TypeEvalM ExpM   -- Array element representation
            -> (Var -> TypeEvalM ExpM -> TypeEvalM ExpM) -- Element writer code
            -> TypeEvalM ExpM
defineArray elt_type size_ix size elt_repr writer =
  lamE $ mkFun []
  (\ [] -> return ([outType array_type], initEffectType array_type))
  (\ [] [out_ptr] ->
    varAppE (pyonBuiltin the_doall)
    [size_ix, TypM array_type, elt_type]
    [size,
     lamE $ mkFun []
     (\ [] -> return ([intType], initEffectType $ fromTypM elt_type))
     (\ [] [index_var] ->
       let out_expr =
             varAppE (pyonBuiltin the_subscript_out) [size_ix, elt_type]
             [elt_repr, varE out_ptr, varE index_var]
       in writer index_var out_expr)])
  where
    array_type =
      varApp (pyonBuiltin the_array) [fromTypM size_ix, fromTypM elt_type]

intType = VarT (pyonBuiltin the_int)
storedIntType = storedType intType

shapeOfType :: TypM -> TypM
shapeOfType (TypM t) = TypM $ varApp (pyonBuiltin the_shape) [t]

array1Shape :: Type -> Type
array1Shape size =
  varApp (pyonBuiltin the_array_shape)
  [size, VarT $ pyonBuiltin the_unit_shape]

arrayShape :: [Type] -> Type
arrayShape (size : sizes) =
  varApp (pyonBuiltin the_array_shape)
  [size, arrayShape sizes]

arrayShape [] = VarT (pyonBuiltin the_unit_shape)

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
            -- , (pyonBuiltin the_range, rwRange)
            -- , (pyonBuiltin the_TraversableDict_list_traverse, rwTraverseList)
            , (pyonBuiltin the_TraversableDict_list_build, rwBuildList)
            , (pyonBuiltin the_TraversableDict_matrix_traverse, rwTraverseMatrix)
            , (pyonBuiltin the_TraversableDict_matrix_build, rwBuildMatrix)
            -- , (pyonBuiltin the_TraversableDict_Stream_traverse, rwTraverseStream)
            -- , (pyonBuiltin the_TraversableDict_Stream_build, rwBuildStream)
            , (pyonBuiltin the_build_array, rwBuildArray)
            -- , (pyonBuiltin the_oper_GUARD, rwGuard)
            , (pyonBuiltin the_chunk, rwChunk)
            -- , (pyonBuiltin the_fun_map, rwMap)
            -- , (pyonBuiltin the_fun_zip, rwZip)
            -- , (pyonBuiltin the_fun_zip3, rwZip3)
            -- , (pyonBuiltin the_fun_zip4, rwZip4)
            , (pyonBuiltin the_fun_map_Stream, rwMapStream)
            , (pyonBuiltin the_fun_zip_Stream, rwZipStream) 
            , (pyonBuiltin the_fun_zip3_Stream, rwZip3Stream)
            , (pyonBuiltin the_fun_zip4_Stream, rwZip4Stream)
            -- , (pyonBuiltin the_histogram, rwHistogram)
            -- , (pyonBuiltin the_fun_reduce, rwReduce)
            -- , (pyonBuiltin the_fun_reduce1, rwReduce1)
            {- , (pyonBuiltin the_oper_CAT_MAP, rwCatMap) -}
            -- , (pyonBuiltin the_for, rwFor)
            -- , (pyonBuiltin the_safeSubscript, rwSafeSubscript)
            ]

    exprs = [ {- Disabled because the new function, 'generate_forever', 
                 hasn't been written yet
                 (pyonBuiltin the_count, count_expr) -} ]
    
    -- The following expression represents the "count" stream:
    -- asList (array_shape pos_infty)
    -- (generate_forever int repr_int (store int))
    count_expr =
      ExpM $ AppE defaultExpInfo as_list [TypM array_shape, TypM storedIntType]
      [generate_expr]
      where
        as_list =
          ExpM $ VarE defaultExpInfo (pyonBuiltin the_fun_asList_Stream)
        generate_f =
          ExpM $ VarE defaultExpInfo (pyonBuiltin the_generate_forever)
        store_f =
          ExpM $ VarE defaultExpInfo (pyonBuiltin the_stored)

        array_shape = array1Shape posInftyT
        generate_expr =
          ExpM $ AppE defaultExpInfo generate_f [TypM storedIntType]
          [ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_int),
           ExpM $ AppE defaultExpInfo store_f [TypM storedIntType] []]

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
      -- convertToBare (repr, convertToBoxed (_, e)) = e
      return $ Just arg'
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
           varAppE (pyonBuiltin the_copy) [TypM whnf_type]
           [return repr, varE unboxed_ref])]

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
    -- Argument is an initializer expression whose output has 'StoredBox' type.
    -- Bind it to a temporary value, then deconstruct it.
    deconstruct_stored_box boxed_type = do
      tenv <- getTypeEnv
      localE (TypM bare_type) (return arg)
        (\arg_val ->
          caseE (varE arg_val) 
          [mkAlt undefined tenv (pyonBuiltin the_storedBox)
           [TypM boxed_type]
           (\ [] [boxed_ref] -> varE boxed_ref)])
    
    construct_boxed whnf_type = do
      varAppE (pyonBuiltin the_boxed) [TypM whnf_type] [return arg]

rwConvertToBoxed _ _ _ = return Nothing

{-
-- | Convert 'range' into an explicitly indexed variant
rwRange :: RewriteRule
rwRange inf [] [count] = do
  tenv <- getTypeEnv
  fmap Just $
    defineAndInspectIndInt tenv (return count)
    (\intindex intvalue ->
      varAppE (pyonBuiltin the_fun_asList_Stream)
      [TypM $ array1Shape (VarT intindex),
       TypM storedIntType]
      [varAppE (pyonBuiltin the_rangeIndexed) [TypM $ VarT intindex]
       [varAppE (pyonBuiltin the_indInt) [TypM $ VarT intindex]
        [varE intvalue]]])

rwRange _ _ _ = return Nothing-}

{- rwTraverseList :: RewriteRule
rwTraverseList inf [elt_type] [elt_repr, list] = do
  tenv <- getTypeEnv
  fmap Just $
    caseOfList tenv (return list) elt_type $ \size_index size_var array ->
    varAppE (pyonBuiltin the_fun_asList_Stream) 
    [TypM $ array1Shape (VarT size_index), elt_type]
    [varAppE (pyonBuiltin the_generate)
     [TypM (VarT size_index), elt_type]
     [varAppE (pyonBuiltin the_indInt) [TypM $ VarT size_index] [varE size_var],
      return elt_repr,
      lamE $ mkFun []
      (\ [] -> return ([intType, outType (fromTypM elt_type)],
                       initEffectType (fromTypM elt_type)))
      (\ [] [index_var, ret_var] ->
          varAppE (pyonBuiltin the_copy)
          [elt_type]
          [return elt_repr,
           varAppE (pyonBuiltin the_subscript)
           [TypM (VarT size_index), elt_type]
           [return elt_repr, varE array, varE index_var],
           varE ret_var])]]
  
rwTraverseList _ _ _ = return Nothing -}

rwBuildList :: RewriteRule
rwBuildList inf [elt_type] (elt_repr : stream : other_args) = do
  m_stream <- interpretStream2 (VarT (pyonBuiltin the_list_shape))
              (fromTypM elt_type) elt_repr stream
  case m_stream of
    Just (GenerateStream { _sexpSize = size_arg
                         , _sexpCount = size_val
                         , _sexpGenerator = g}) ->
      -- Statically known stream size.
      -- TODO: generalize to more stream constructors
      fmap Just $
      buildListDoall inf elt_type elt_repr other_args (TypM size_arg) size_val g
    _ -> return Nothing

rwBuildList _ _ _ = return Nothing

--
-- > case matrix
-- > of make_matrix elt_type (m n : intindex)
-- >        (size_y : FinIndInt m) (size_x : FinIndInt n) (a : array m (array n elt_type)).
-- >      bind m (array_shape n unit_shape) (Stored int) elt_type
-- >      repr_int elt_repr (generate m (Stored int) size_y (copy (Stored int) int_repr))
-- >      (\(y : int). generate n elt_type size_x (\(x : int).
-- >          copy elt_type elt_repr (subscript n elt_type elt_repr 
-- >                                  (subscript m (array n elt_type) 
-- >                                   (repr_array n elt_type size_x elt_repr) y) x)))
rwTraverseMatrix :: RewriteRule
rwTraverseMatrix inf [elt_type] [elt_repr, matrix] = do
  tenv <- getTypeEnv
  fmap Just $
    caseOfMatrix tenv (return matrix) elt_type $ \size_y_index size_x_index size_y_var size_x_var array ->
    varAppE (pyonBuiltin the_fun_asList_Stream) 
    [TypM $ arrayShape [VarT size_y_index, VarT size_x_index], elt_type]
    [varAppE (pyonBuiltin the_bind)
     [TypM $ VarT size_y_index, TypM $ array1Shape (VarT size_x_index),
      TypM storedIntType, elt_type]
     [return int_repr,
      return elt_repr,
      -- Generate array indices in the Y dimension
      varAppE (pyonBuiltin the_generate)
      [TypM (VarT size_y_index), TypM storedIntType]
      [varAppE (pyonBuiltin the_indInt) [TypM $ VarT size_y_index] [varE size_y_var],
       return int_repr,
       lamE $ mkFun []
       (\ [] -> return ([intType, outType storedIntType],
                        initEffectType storedIntType))
       (\ [] [y_var, ret_var] ->
         varAppE (pyonBuiltin the_stored) [TypM intType] [varE y_var, varE ret_var])],

      -- For each Y index, generate array elements for the row
      lamE $ mkFun []
      (\ [] -> return ([storedIntType],
                       varApp (pyonBuiltin the_Stream)
                       [varApp (pyonBuiltin the_array_shape) [VarT size_x_index, VarT (pyonBuiltin the_unit_shape)], fromTypM elt_type]))
      (\ [] [y_var] ->
        varAppE (pyonBuiltin the_generate)
        [TypM (VarT size_x_index), elt_type]
        [varAppE (pyonBuiltin the_indInt) [TypM $ VarT size_x_index] [varE size_x_var],
         return elt_repr,
         lamE $ mkFun []
         (\ [] -> return ([intType, outType (fromTypM elt_type)],
                          initEffectType (fromTypM elt_type)))
         (\ [] [x_var, ret_var] ->
           varAppE (pyonBuiltin the_copy)
           [elt_type]
           [return elt_repr,
            subscript2D (VarT size_y_index) (VarT size_x_index)
            size_y_var size_x_var
            (varE array)
            (load tenv (TypM intType) $ varE y_var)
            (varE x_var),
            varE ret_var])])]]
  where
    int_repr = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_int) 
    
    subscript2D :: Type -> Type -> Var -> Var -> TypeEvalM ExpM -> TypeEvalM ExpM -> TypeEvalM ExpM
                -> TypeEvalM ExpM
    subscript2D y_ix x_ix y_var x_var ay y x =
      varAppE (pyonBuiltin the_subscript)
      [TypM x_ix, elt_type]
      [return elt_repr,
       varAppE (pyonBuiltin the_subscript)
       [TypM y_ix, TypM $ varApp (pyonBuiltin the_array) [x_ix, fromTypM elt_type]]
       [varAppE (pyonBuiltin the_repr_array)
        [TypM x_ix, elt_type]
        [varE x_var, return elt_repr],
        ay,
        y],
       x]
  
rwTraverseMatrix _ _ _ = return Nothing

rwBuildMatrix :: RewriteRule
rwBuildMatrix inf [elt_type] (elt_repr : stream : other_args) = do
  m_stream <- interpretStream2 (VarT (pyonBuiltin the_list_shape))
              (fromTypM elt_type) elt_repr stream
  case m_stream of
    Just stream ->
      -- Shape should be a 2D array shape
      case sexpShape stream
      of sh@(ArrayShape [(y_t, y_v), (x_t, x_v)]) -> do
           m_stream' <- encodeStream2 (TypM $ shapeType sh) stream
           case m_stream' of
             Just stream' -> do
               tenv <- getTypeEnv
               fmap Just $ build_matrix_expr tenv y_t y_v x_t x_v stream' other_args
             Nothing -> return Nothing
         ArrayShape _ ->
           -- Array shape, but not 2D
           internalError "rwBuildMatrix: Stream has wrong dimensionality"
         _ -> return Nothing    -- Unknown shape
    _ -> return Nothing         -- Cannot interpret stream
    where
      build_matrix_expr tenv y_t y_v x_t x_v stream other_args =
        -- > case x_v of
        -- > indInt x_t x_fv.
        -- >   case y_v of
        -- >   indInt y_t y_fv.
        -- >     ...
        -- >   indOmega y_t _. except (Writer (matrix elt_type))
        -- > indOmega x_t _. except (Writer (matrix elt_type))
        let result_type =
              writerType $ varApp (pyonBuiltin the_matrix) [fromTypM elt_type]
        in caseOfIndInt tenv (return x_v) (fromTypM x_t)
           (\x_fv -> caseOfIndInt tenv (return y_v) (fromTypM y_t)
                     (\y_fv ->
                       build_matrix_fin_expr tenv y_t y_fv x_t x_fv stream other_args)
                  (\_ -> exceptE result_type))
           (\_ -> exceptE result_type)
      build_matrix_fin_expr tenv y_t y_fv x_t x_fv stream other_args =
        -- >     make_matrix elt_type y_t x_t y_fv x_fv
        -- >       (referenced (array y_t (array x_t elt_type))
        -- >        (build_array y_t (array x_t elt_type) y_fv
        -- >         (repr_array x_t elt_type x_fv elt_repr)
        -- >         (chunk y_t (array_shape x_t unit_shape) elt_type
        -- >          (array x_t elt_type) elt_repr
        -- >          (repr_array x_t elt_type x_fv elt_repr)G
        -- >          stream
        -- >          (build_array x_t elt_type x_fv elt_repr))))
        varAppE (pyonBuiltin the_make_matrix) [elt_type, y_t, x_t]
        (varE y_fv :
         varE x_fv :
         varAppE (pyonBuiltin the_referenced)
         [TypM array_2d_type]
         [varAppE (pyonBuiltin the_build_array)
          [y_t, TypM array_1d_type]
          [varE y_fv,
           array_1d_repr,
           varAppE (pyonBuiltin the_chunk)
           [y_t, TypM array_1d_shape, elt_type, TypM array_1d_type]
           [return elt_repr,
            array_1d_repr,
            return stream,
            varAppE (pyonBuiltin the_build_array)
            [x_t, elt_type]
            [varE x_fv, return elt_repr]]]] :
         map return other_args)
        where
          array_2d_type = varApp (pyonBuiltin the_array)
                          [fromTypM y_t, array_1d_type]
          array_1d_type = varApp (pyonBuiltin the_array)
                          [fromTypM x_t, fromTypM elt_type]
          array_1d_shape = varApp (pyonBuiltin the_array_shape)
                           [fromTypM x_t, VarT (pyonBuiltin the_unit_shape)]
          array_1d_repr = varAppE (pyonBuiltin the_repr_array)
                          [x_t, elt_type] [varE x_fv, return elt_repr]

rwBuildMatrix _ _ _ = return Nothing

rwTraverseStream :: RewriteRule
rwTraverseStream inf _ [_, stream] = return (Just stream)
rwTraverseStream _ _ _ = return Nothing

rwBuildStream :: RewriteRule
rwBuildStream inf _ [_, stream] = return (Just stream)
rwBuildStream _ _ _ = return Nothing

rwBuildArray :: RewriteRule
rwBuildArray inf [size, elt_type] (count : elt_repr : stream : other_args) = do
  m_stream <- interpretStream2 (VarT $ pyonBuiltin the_list_shape) (fromTypM elt_type) elt_repr stream
  case m_stream of
    Just (GenerateStream { _sexpSize = size_arg
                         , _sexpCount = size_val
                         , _sexpGenerator = g}) -> do
      -- Statically known stream size.
      -- TODO: generalize to more stream constructors
      build_array <-
        buildArrayDoall inf elt_type elt_repr (TypM size_arg) size_val g
      let retval = appE inf build_array [] other_args
      return $ Just retval

    _ -> return Nothing

buildListDoall inf elt_type elt_repr other_args size count generator = do
  let return_ptr =
        case other_args
        of [x] -> Just (return x)
           []  -> Nothing
      
      return_type =
        case other_args
        of [x] -> initEffectType list_type
           [] -> writerType list_type
        where
          list_type = varApp (pyonBuiltin the_list) [fromTypM elt_type]

      write_array index mk_dst =
        appExp (generator (ExpM $ VarE defaultExpInfo index)) [] [mk_dst]

      define_list finite_size =
        defineList elt_type size
        (varE finite_size) (return elt_repr) return_ptr write_array
      
      undef_list _ =
        exceptE return_type

  tenv <- getTypeEnv 
  caseOfIndInt tenv (return count) (fromTypM size) define_list undef_list

buildArrayDoall inf elt_type elt_repr size count generator = do
  let array_type = varApp (pyonBuiltin the_array) [fromTypM size, fromTypM elt_type]
      return_type = writerType array_type

      write_array index mk_dst =
        appExp (generator (ExpM $ VarE defaultExpInfo index)) [] [mk_dst]

      define_array finite_size =
        defineArray elt_type size
        (varE finite_size) (return elt_repr) write_array
      
      undef_array _ =
        exceptE array_type

  tenv <- getTypeEnv
  caseOfIndInt tenv (return count) (fromTypM size) define_array undef_array

{-
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

{-
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

rwGuard _ _ _ = return Nothing-}

-- Try to simplify applications of 'chunk'.
--
-- 'Chunk' can create nested loops.
rwChunk :: RewriteRule
rwChunk inf [n_chunks, chunk_shape, elt_ty, result_ty]
  [elt_repr, result_repr, stream, consumer] = do
  -- The source stream is expected to be a multidimensional array stream
  let shape = varApp (pyonBuiltin the_array_shape)
              [fromTypM n_chunks, fromTypM chunk_shape]
      shape_1d = varApp (pyonBuiltin the_array_shape)
                 [fromTypM n_chunks, VarT (pyonBuiltin the_unit_shape)]
  m_stream <- interpretStream2 shape (fromTypM elt_ty) elt_repr stream
  case m_stream of
    Just (NestedLoopStream src_stream (binder, producer_stream)) -> do
      -- Map over the source stream
      -- mapStream (\x. consumer (producer x)) stream
      producer_exp <- encodeStream2 chunk_shape producer_stream
      case producer_exp of
        Nothing -> return Nothing
        Just pe ->
          let transformer = mk_transformer binder pe consumer
              new_stream =
                mapStream (fromTypM result_ty) result_repr transformer src_stream
      
          -- Return the new stream
          in encodeStream2 (TypM shape_1d) new_stream
    _ -> return Nothing
  where
    mk_transformer binder producer consumer =
      ExpM $ LamE defaultExpInfo $
      FunM $ Fun { funInfo = defaultExpInfo
                 , funTyParams = []
                 , funParams = [binder]
                 , funReturn = TypM $ writerType $ fromTypM result_ty
                 , funBody = ExpM $ AppE defaultExpInfo consumer [] [producer]}
   

rwChunk _ _ _ = return Nothing

{-
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

rwZip4 _ _ _ = return Nothing-}

rwMapStream :: RewriteRule
rwMapStream inf
  ty_args@[shape_type, elt1, elt2]
  args@[repr1, repr2, transformer, producer] = do
    m_stream <- interpretStream2 (fromTypM shape_type) (fromTypM elt2) repr2 map_expr
    case m_stream of
      Just s -> traceShow (text "rwMapStream" <+> pprExpS s) $ encodeStream2 shape_type s
      Nothing -> return Nothing
  where
    map_op = ExpM $ VarE inf (pyonBuiltin the_fun_map_Stream)
    map_expr =
      ExpM $ AppE inf map_op ty_args args

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
  [repr1, repr2, stream1, stream2] = runMaybeT $ do
    s1 <- MaybeT $ interpretStream2 shape_type elt1 repr1 stream1
    s2 <- MaybeT $ interpretStream2 shape_type elt2 repr2 stream2
    MaybeT $ generalizedZipStream2 (TypM shape_type) [s1, s2]

rwZipStream _ _ _ = return Nothing

rwZip3Stream :: RewriteRule
rwZip3Stream inf
  [TypM shape_type, TypM elt1, TypM elt2, TypM elt3]
  [repr1, repr2, repr3, stream1, stream2, stream3] = runMaybeT $ do
    s1 <- MaybeT $ interpretStream2 shape_type elt1 repr1 stream1
    s2 <- MaybeT $ interpretStream2 shape_type elt2 repr2 stream2
    s3 <- MaybeT $ interpretStream2 shape_type elt3 repr3 stream3
    MaybeT $ generalizedZipStream2 (TypM shape_type) [s1, s2, s3]

rwZip3Stream _ _ _ = return Nothing

rwZip4Stream :: RewriteRule
rwZip4Stream inf
  [TypM shape_type, TypM elt1, TypM elt2, TypM elt3, TypM elt4]
  [repr1, repr2, repr3, repr4, stream1, stream2, stream3, stream4] = runMaybeT $ do
    s1 <- MaybeT $ interpretStream2 shape_type elt1 repr1 stream1
    s2 <- MaybeT $ interpretStream2 shape_type elt2 repr2 stream2
    s3 <- MaybeT $ interpretStream2 shape_type elt3 repr3 stream3
    s4 <- MaybeT $ interpretStream2 shape_type elt4 repr4 stream4
    MaybeT $ generalizedZipStream2 (TypM shape_type) [s1, s2, s3, s4]

rwZip4Stream _ _ _ = return Nothing

generalizedZipStream2 :: TypM -> [ExpS] -> TypeEvalM (Maybe ExpM)
generalizedZipStream2 shape_type streams = do
  zipped <- zipStreams2 streams
  case zipped of
    Just s -> encodeStream2 shape_type s
    Nothing -> return Nothing

{-
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
    defineAndInspectIndInt tenv (return size)
    (\n index ->
      varAppE (pyonBuiltin the_make_list)
      [TypM storedIntType, TypM $ VarT n]
      (varE index :
       varAppE (pyonBuiltin the_referenced)
       [TypM $ varApp (pyonBuiltin the_array) [VarT n, storedIntType]]
       [varAppE (pyonBuiltin the_histogramArray)
        [shapeOfType container, TypM $ VarT n]
        [varE index, return input]] :
       map return other_args))

rwHistogram _ _ _ = return Nothing -}

rwHistogramArray :: RewriteRule
rwHistogramArray inf [shape_type, size_ix] (size : input : other_args) = do
  m_stream <- interpretStream2 (fromTypM shape_type) intType repr_int input
  case m_stream of
    Just s -> do
      tenv <- getTypeEnv
      fmap Just $
        varAppE (pyonBuiltin the_createHistogram)
        [size_ix]
        (return size :
         lamE (mkFun []
         (\ [] -> return ([funType [intType] eff_type, eff_type], eff_type))
         (\ [] [writer, in_eff] ->
           make_histogram_writer tenv s writer in_eff)) :
         map return other_args)
    Nothing -> return Nothing
  where
    eff_type = VarT (pyonBuiltin the_EffTok)
    stored_eff_type = storedType $ VarT (pyonBuiltin the_EffTok)
    repr_int = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_int)
    repr_eff = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_EffTok)
    
    -- The argument to createHistogram is a fold operation.
    --
    -- > lambda f z.
    -- >   case case boxed (stored z)
    -- >        of boxed (initval).
    -- >             boxed (fun_fold_stream (Stored EffTok, Stored int)
    -- >                     (repr_EffTok, repr_int,
    -- >                      (lambda acc intval.
    -- >                         case intval
    -- >                         of stored (n).
    -- >                             case acc
    -- >                             of stored (etok).
    -- >                                  stored (seqEffTok (etok, f (n)))),
    -- >                      initval, s))
    -- >   of boxed (stored_out_tok).
    -- >        case stored_out_tok of stored (out_tok) -> out_tok
    make_histogram_writer :: TypeEnv -> ExpS -> Var -> Var
                          -> TypeEvalM ExpM
    make_histogram_writer tenv s writer initial_eff = do
      -- The accumulator function passes an integer value to the
      -- histogram writer function
      accumulator_fn <-
        lamE $ mkFun []
        (\ [] -> return ([stored_eff_type, storedIntType],
                         writerType stored_eff_type))
        (\ [] [in_eff_ptr, index_ptr] ->
            -- Call function and return a new effect token
            varAppE (pyonBuiltin the_stored) [TypM eff_type]
              [varAppE (pyonBuiltin the_seqEffTok) []
               [load tenv (TypM eff_type) (varE in_eff_ptr),
                varAppE writer []
                [load tenv (TypM intType) (varE index_ptr)]]])

      -- Store the input effect token in a temporary variable
      localE (TypM $ stored_eff_type)
        (varAppE (pyonBuiltin the_stored) [TypM eff_type] [varE initial_eff])
        (\initial_eff_ptr ->
          -- Generate the main loop here and load the effect token that's
          -- generated
          let initial_eff_exp = ExpM $ VarE defaultExpInfo initial_eff_ptr
          in localE (TypM $ stored_eff_type)
             (translateStreamToFoldWithExtraArgs
              tenv stored_eff_type repr_eff initial_eff_exp
              accumulator_fn s [])
             (\out_eff_ptr -> load tenv (TypM eff_type) (varE out_eff_ptr)))
      
rwHistogramArray _ _ _ = return Nothing

{-
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

rwReduce1 _ _ _ = return Nothing -}

-- | Parallelize a reduction.
--   This rewrite is nonterminating, so we must limit how often it's performed.
rwParallelReduceStream :: RewriteRule
rwParallelReduceStream inf
  [shape_type, elt]
  (elt_repr : reducer : init : stream : other_args) = do
  m_stream <- interpretAndBlockStream (fromTypM shape_type) (fromTypM elt)
              elt_repr stream
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
        Just ws -> do
          worker_body <-
            varAppE (pyonBuiltin the_fun_reduce_Stream)
            [TypM $ VarT (pyonBuiltin the_list_shape), elt]
            [return elt_repr,
             return reducer,
             return init,
             return ws,
             varE worker_retvar]
          
          let param1 = patM (count_var :::
                       varApp (pyonBuiltin the_FinIndInt) [VarT size_var])
              param2 = patM (base_var ::: intType)
              param3 = patM (worker_retvar ::: outType (fromTypM elt))
              worker_fn =
                FunM $
                Fun { funInfo = inf
                    , funTyParams = [TyPatM (size_var ::: intindexT)]
                    , funParams = [param1, param2, param3]
                    , funReturn = TypM $ initEffectType (fromTypM elt)
                    , funBody = worker_body}
                
          -- Create the blocked_reduce call
          tenv <- getTypeEnv
          call <-
            -- Check whether stream is finite
            caseOfIndInt tenv (return bs_count) (fromTypM bs_size)
            (\fin_count ->
                -- Finite case
                varAppE (pyonBuiltin the_blocked_reduce) [elt, bs_size]
                (return elt_repr : varE fin_count : litE (IntL 0 intType) :
                 return reducer : return init :
                 return (ExpM $ LamE defaultExpInfo worker_fn) :
                 map return other_args))
            (\_ ->
                -- Infinite case
              let exc_type = case other_args
                             of [t] -> initEffectType $ fromTypM elt
                                [] -> writerType $ fromTypM elt
              in exceptE exc_type)
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
            varAppE (pyonBuiltin the_fun_reduce1_Stream)
            [TypM $ VarT (pyonBuiltin the_list_shape), elt]
            [return elt_repr,
             return reducer,
             return ws,
             varE worker_retvar]
          
          let param1 = patM (count_var :::
                       varApp (pyonBuiltin the_FinIndInt) [VarT size_var])
              param2 = patM (base_var ::: intType)
              param3 = patM (worker_retvar ::: outType (fromTypM elt))
              worker_fn =
                FunM $
                Fun { funInfo = inf
                    , funTyParams = [TyPatM (size_var ::: intindexT)]
                    , funParams = [param1, param2, param3]
                    , funReturn = TypM $ initEffectType $ fromTypM elt
                    , funBody = worker_body}
                
          -- Create the blocked_reduce call
          tenv <- getTypeEnv
          call <-
            -- Check whether stream is finite
            caseOfIndInt tenv (return bs_count) (fromTypM bs_size)
            (\fin_count ->
                -- Finite case
                varAppE (pyonBuiltin the_blocked_reduce1) [elt, bs_size]
                (return elt_repr : varE fin_count : litE (IntL 0 intType) :
                 return reducer :
                 return (ExpM $ LamE defaultExpInfo worker_fn) :
                 map return other_args))
            (\_ ->
                -- Infinite case
              let exc_type = case other_args
                             of [t] -> initEffectType $ fromTypM elt
                                [] -> writerType $ fromTypM elt
              in exceptE exc_type)
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
  m_stream <- interpretAndBlockStream (fromTypM shape_type) storedIntType int_repr input
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
        Just ws -> do
          tenv <- getTypeEnv
          code <-
            -- Get the finite stream size 
            caseOfIndInt tenv (return bs_count) (fromTypM bs_size)
            (\finite ->
                make_parallel_histogram
                size_var count_var base_var bs bs_size finite ws)
            (\_ -> 
              let exc_type = case other_args
                             of [t] -> initEffectType array_type
                                [] -> writerType array_type
              in exceptE exc_type)

          return $ Just code
  where
    -- Create a parallel loop that initializes a histogram
    make_parallel_histogram
      size_var count_var base_var bs orig_size orig_count ws =
        case other_args
        of [] ->
             -- Return a writer funciton
             lamE $ mkFun []
             (\ [] -> return ([outType array_type],
                              initEffectType array_type))
             (\ [] [ret_var] -> write_into (varE ret_var))
           [ret_val] ->
             -- Write into the return argument
             write_into (return ret_val)
           _ ->
             internalError "rwParallelHistogramArray"
        where 
          write_into :: TypeEvalM ExpM -> TypeEvalM ExpM
          write_into return_arg =
            -- Define an empty histogram, i.e. a zero-filled array
            localE (TypM array_type) zero_array
            (\empty_hist ->
                -- Compute the histogram
                varAppE (pyonBuiltin the_blocked_reduce)
                [TypM array_type, orig_size]
                [array_repr,
                 varE orig_count,
                 litE (IntL 0 intType),
                 elementwise_add,
                 varE empty_hist,
                 worker_fn size_var count_var base_var ws,
                 return_arg])

    array_type = varApp (pyonBuiltin the_array) [fromTypM size_ix, storedIntType]
    array_shape = array1Shape (fromTypM size_ix)
    
    int_repr = ExpM $ VarE defaultExpInfo (pyonBuiltin the_repr_int)
    array_repr :: TypeEvalM ExpM
    array_repr = varAppE (pyonBuiltin the_repr_array)
                 [size_ix, TypM storedIntType] [return size, return int_repr]

    -- A single parallel task
    --    
    -- > \ local_size local_count base ret.
    -- >     histogramArray list_shape histo_size histo_count stream ret
    worker_fn size_var count_var base_var bs = do
      retvar <- newAnonymousVar ObjectLevel
      fn_body <- varAppE (pyonBuiltin the_histogramArray)
                 [TypM $ VarT (pyonBuiltin the_list_shape), size_ix]
                 [return size, return bs, varE retvar]
      let param1 = patM (count_var :::
                            varApp (pyonBuiltin the_FinIndInt) [VarT size_var])
          param2 = patM (base_var ::: intType)
          param3 = patM (retvar ::: outType array_type)
          ret = TypM $ initEffectType array_type
      return $ ExpM $ LamE defaultExpInfo $ FunM $
        Fun { funInfo = inf
            , funTyParams = [TyPatM (size_var ::: intindexT)]
            , funParams = [param1, param2, param3]
            , funReturn = ret
            , funBody = fn_body}
  
    -- Initialize an array with all zeros
    zero_array =
      defineArray (TypM storedIntType) size_ix (return size) (return int_repr)
      (\_ out_expr -> varAppE (pyonBuiltin the_stored) [TypM intType]
                      [litE $ IntL 0 intType, out_expr])
    
    -- Add two arrays, elementwise
    elementwise_add =
      lamE $ mkFun []
      (\ [] -> return ([array_type, array_type, outType array_type],
                       initEffectType array_type))
      (\ [] [a, b, ret_ptr] ->
        appExp
        (defineArray (TypM storedIntType) size_ix (return size) (return int_repr)
         (\index_var out_expr ->
           let load_element array_ptr_var = do
                 -- Load an array element from array_ptr_var at index_var
                 tenv <- getTypeEnv
                 load tenv (TypM intType)
                   (varAppE (pyonBuiltin the_subscript)
                    [size_ix, TypM storedIntType]
                    [return int_repr, varE array_ptr_var, varE index_var])
           in varAppE (pyonBuiltin the_stored) [TypM intType]
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
   (\ [mindex] -> return ([varApp (pyonBuiltin the_FinIndInt) [VarT mindex],
                           intType],
                          initEffectType (fromTypM element_eff)))
   (\ [mindex] [msize, offset] ->
     -- The outer loop body contains another loop that initializes some
     -- part of the output array.  We use 'element_effect' as the effect label
     -- for the inner loop.
     varAppE (pyonBuiltin the_doall)
     [TypM (VarT mindex), element_eff, element_eff]
     [varE msize,
      lamE $ mkFun []
      (\ [] -> return ([intType], initEffectType (fromTypM element_eff)))
      (\ [] [ix] ->
        appExp (return worker) []
        [varAppE (pyonBuiltin the_AdditiveDict_int_add) []
         [varE offset, varE ix]])])]
  
rwParallelDoall _ _ _ = return Nothing

rwReduceStream :: RewriteRule
rwReduceStream inf [shape_type, element]
  (elt_repr : reducer : init : stream : other_args) = do
  m_stream <- interpretStream2 (fromTypM shape_type) (fromTypM element)
              elt_repr stream
  case m_stream of
    Just s -> do
      tenv <- getTypeEnv
      fmap Just $
        translateStreamToFoldWithExtraArgs tenv (fromTypM element) elt_repr init reducer s other_args
    Nothing -> return Nothing
  
rwReduceStream _ _ _ = return Nothing

rwFoldStream :: RewriteRule
rwFoldStream inf [elt_type, acc_type]
  (elt_repr : acc_repr : reducer : init : stream : other_args) = do
  m_stream <- interpretStream2 (VarT (pyonBuiltin the_list_shape)) (fromTypM elt_type)
              elt_repr stream
  case m_stream of
    Just s -> do
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
   (\ [] -> return ([intType, fromTypM element, outType (fromTypM element)],
                    initEffectType (fromTypM element)))
   (\ [] [ix, acc, ret] ->
       localE element (producer (ExpM $ VarE defaultExpInfo ix))
       (\tmpvar -> do
           -- Combine with accumulator
           appExp (return reducer) [] [varE acc, varE tmpvar, varE ret]))) :
   map return other_args)

rwReduce1Stream :: RewriteRule
rwReduce1Stream inf [shape_type, element]
  (elt_repr : reducer : stream : other_args) = do
  m_stream <- interpretStream2 (fromTypM shape_type) (fromTypM element)
              elt_repr stream
  case m_stream of
    Just (GenerateStream { _sexpSize = size_arg
                         , _sexpCount = size_val
                         , _sexpGenerator = g}) ->
      fmap Just $
      rwReduce1Generate inf element elt_repr reducer other_args
      (TypM size_arg) size_val g
    _ -> return Nothing

rwReduce1Stream _ _ _ = return Nothing

rwReduce1Generate inf element elt_repr reducer other_args size count producer = do
  producer_var <- newAnonymousVar ObjectLevel
  producer_fn <- mkFun []
    (\ [] -> return ([intType],
                     outType (fromTypM element) `FunT` initEffectType (fromTypM element)))
    (\ [] [index] -> producer $ ExpM $ VarE defaultExpInfo index)

  reduce1_expr <-
    -- Get the first value.
    -- The code may crash at runtime if there aren't any values.
    localE element (varAppE producer_var [] [litE (IntL 0 intType)]) $ \var1 -> do
  
    -- Loop over the remaining values
    let producer_plus_1 index =
          varAppE producer_var []
          [varAppE (pyonBuiltin the_AdditiveDict_int_add) []
           [return index, litE (IntL 1 intType)]]
  
    let size_minus_1 = TypM $ varApp (pyonBuiltin the_minus_i)
                       [fromTypM size, IntT 1]

    -- The number of loop iterations is (size - 1)
    count_minus_1 <-
      varAppE (pyonBuiltin the_minus_ii)
      [size, TypM $ IntT 1]
      [return count, varE (pyonBuiltin the_one_ii)]

    -- The main loop
    rwReduceGenerate inf element elt_repr reducer
      (ExpM $ VarE defaultExpInfo var1) other_args
      size_minus_1 count_minus_1 producer_plus_1
          
  -- Build a let expression
  let producer_group = NonRec (mkDef producer_var producer_fn)
  return $ ExpM $ LetfunE defaultExpInfo producer_group reduce1_expr

{-
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
      caseOfIndInt' tenv (return size) size_ix finite_case infinite_case
      where
        infinite_case _ =
          case maybe_ret
          of Just _  -> exceptE (initEffectType acc_type)
             Nothing -> exceptE (writerType acc_type)

        finite_case _ bound = do
          loop_var <- newAnonymousVar ObjectLevel
          loop_fun <-
            mkFun []
            (\ [] -> return ([intType, acc_type, outType acc_type],
                             initEffectType acc_type))
            (\ [] [i, acc, retvar] -> do
                ifE (varAppE (pyonBuiltin the_EqDict_int_eq) []
                     [varE i, varE bound])
                  (varAppE (pyonBuiltin the_copy) [TypM acc_type]
                   [return acc_repr, varE acc, varE retvar])
                  (localE (TypM acc_type)
                   (appExp (return fun) [] [varE i, varE acc])
                   (\lv -> varAppE loop_var []
                           [varAppE (pyonBuiltin the_AdditiveDict_int_add) []
                            [varE i, litE $ IntL 1 intType],
                            varE lv,
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
    (\ [] -> return ([outType $ fromTypM elt_type],
                     initEffectType $ fromTypM elt_type))
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
  caseOfFinIndInt tenv (varE size) (VarT size_ix) $ \_ size_int -> do
      ix_var <- newAnonymousVar ObjectLevel
      subscript_expr <-
        ifE (varAppE (pyonBuiltin the_or) []
             [varAppE (pyonBuiltin the_OrdDict_int_lt) []
              [varE ix_var, litE (IntL 0 intType)],
              varAppE (pyonBuiltin the_OrdDict_int_ge) []
              [varE ix_var, varE size_int]])
        (exceptE (initEffectType $ fromTypM elt_type))
        (varAppE (pyonBuiltin the_copy) [elt_type]
         [return elt_repr,
          varAppE (pyonBuiltin the_subscript) [TypM (VarT size_ix), elt_type]
          [return elt_repr, varE array, varE ix_var],
          ret])
        
      return $ letE (patM (ix_var ::: intType)) ix subscript_expr
-}

-------------------------------------------------------------------------------
{-
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
-}

-- | The iteration domain of a stream
data Shape =
    -- | A list stream, corresponding to @list_shape@.  The size is unknown.
    ListShape
    -- | A statically sized stream, corresponding to nested applications of
    --   @array_shape@.  The first term is the outermost application.
    --   Each size index has kind @intindex@.
    --   Each expression has type @IndInt n@ where @n@ is the type index.
  | ArrayShape [(TypM, ExpM)]
    -- | An unknown iteration domain that has the given shape index
  | UnknownShape TypM

-- | Return a type that is a valid type index for the given shape.
shapeType :: Shape -> Type
shapeType shp = 
  case shp
  of ListShape                 -> VarT $ pyonBuiltin the_list_shape
     ArrayShape dim            -> arrayShape [i | (TypM i, _) <- dim]
     UnknownShape (TypM shape) -> shape
  
-- | Get the shape encoded in a type.
--
--   A non-unit array shape is never returned because this function cannot find
--   the integer variable that holds the array size.
typeShape :: Type -> Shape
typeShape ty =
  case fromVarApp ty
  of Just (v, []) | v `isPyonBuiltin` the_list_shape -> ListShape
                  | v `isPyonBuiltin` the_unit_shape -> ArrayShape []
     _ -> UnknownShape (TypM ty)

listShape = ListShape

-- | Decide whether the given shapes are equal
compareShapes :: Shape -> Shape -> TypeEvalM Bool
compareShapes ListShape ListShape = return True
compareShapes (ArrayShape dim1) (ArrayShape dim2) =
  compare_dimensions dim1 dim2
  where
    compare_dimensions ((TypM t1, _) : dim1') ((TypM t2, _) : dim2') =
      compareTypes t1 t2 >&&> compare_dimensions dim1' dim2'
    compare_dimensions [] [] = return True
    compare_dimensions _ _ = return False

compareShapes (UnknownShape (TypM t1)) (UnknownShape (TypM t2)) =
  compareTypes t1 t2

compareShapes _ _ = return False

-- | The interpreted value of a stream.
data instance Exp Stream =
    GenerateStream
    { -- | The stream's length; an integer index
      _sexpSize :: Type
      
      -- | The stream's length as a value
    , _sexpCount :: ExpM

      -- | The type of a stream element
    , _sexpType :: Type

      -- | The representation dictionary of a stream element
    , _sexpRepr :: ExpM

      -- | Given an expression that evaluates to the index of the desired
      --   stream element (with type @val int@), produce an expression that
      --   evaluates to the desired stream element, as a write reference. 
    , _sexpGenerator :: ExpM -> TypeEvalM ExpM
    }
    -- | List 'bind' operator
  | BindStream
    { -- | The source stream
      _sexpSrcStream :: ExpS

      -- | The transformer,
      --   which is a one-parameter function returning a stream
    , _sexpTransStream :: (PatM, ExpS)
    }
    -- | Counted loop 'bind' operator
  | NestedLoopStream
    { -- | The source stream
      _sexpSrcStream :: ExpS

      -- | The transformer,
      --   which is a one-parameter function returning a stream
    , _sexpTransStream :: (PatM, ExpS)
    }
    -- | Let expression in a stream
  | LetStream
    { _sexpBinder :: PatM
    , _sexpValue :: ExpM
    , _sexpStream :: ExpS
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
sexpShape (GenerateStream {_sexpSize = t, _sexpCount = n}) =
  ArrayShape [(TypM t, n)]
sexpShape (BindStream _ _) = ListShape
sexpShape (NestedLoopStream src (_, dst)) =
  case sexpShape src
  of ArrayShape [dim1] ->
       case sexpShape dst
       of ArrayShape dims -> ArrayShape (dim1 : dims)
sexpShape (LetStream {_sexpStream = s}) = sexpShape s
sexpShape (CaseStream {_sexpShape = s}) = s
sexpShape (ReturnStream {}) = ListShape
sexpShape (EmptyStream {}) = ListShape
sexpShape (UnknownStream {_sexpShape = s}) = s

-- | Get the type of a stream element
sexpElementType :: ExpS -> Type
sexpElementType (GenerateStream {_sexpType = t}) = t
sexpElementType (BindStream _ (_, s)) = sexpElementType s
sexpElementType (NestedLoopStream _ (_, s)) = sexpElementType s
sexpElementType (LetStream {_sexpStream = s}) = sexpElementType s
sexpElementType (CaseStream {_sexpAlternatives = alt:_}) =
  sexpElementType $ altBody $ fromAltS alt
sexpElementType (ReturnStream {_sexpType = t}) = t
sexpElementType (EmptyStream {_sexpType = t}) = t
sexpElementType (UnknownStream {_sexpType = t}) = t

-- | Get the representation dictionary of a stream element
sexpElementRepr :: ExpS -> ExpM
sexpElementRepr (GenerateStream {_sexpRepr = e}) = e
sexpElementRepr (BindStream _ (_, s)) = sexpElementRepr s
sexpElementRepr (NestedLoopStream _ (_, s)) = sexpElementRepr s
sexpElementRepr (LetStream {_sexpStream = s}) = sexpElementRepr s
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
  of GenerateStream sz ct ty repr gen ->
       text "generate" <+> parens (pprType sz) <+> parens (pprExp ct) <+>
       text "(...)"
     BindStream src (pat, trans) ->
       text "bind" $$
       pprPat pat <+> text "<-" $$
       nest 4 (pprExpS src) $$
       pprExpS trans
     NestedLoopStream src (pat, trans) ->
       text "bindarray" $$
       pprPat pat <+> text "<-" $$
       nest 4 (pprExpS src) $$
       pprExpS trans
     LetStream b v s ->
       text "let" <+> pprPat b <+> text "=" <+> pprExp v $$
       pprExpS s
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

pprAltS (AltS (DeCon con ty_args ex_types params body)) =
  let con_doc = pprVar con
      args_doc = pprParenList [pprType t | TypS t <- ty_args]
      ex_types_doc = map (parens . pprTyPat . fromTyPatS) ex_types
      params_doc = map (parens . pprPat . fromPatS) params
      body_doc = pprExpS body
  in con_doc <+> sep (args_doc : ex_types_doc ++ params_doc) <> text "." $$
     nest 2 body_doc

pprAltS (AltS (DeTuple params body)) =
  let params_doc =
        parens $ sep $ punctuate (text ",") $ map (pprPat . fromPatS) params
      body_doc = pprExpS body
  in params_doc <> text "." $$ nest 2 body_doc

-- | Given a stream and the type and repr of a stream element, get its shape.
--
--   We may change the stream's type by ignoring functions that only
--   affect the advertised stream shape.
interpretStream2 :: Type -> Type -> ExpM -> ExpM -> TypeEvalM (Maybe ExpS)
interpretStream2 shape_type elt_type repr expression = do
  s <- interpretStream2' shape_type elt_type repr expression

  -- If interpretation produced nothing useful, then return Nothing
  return $! case s of {UnknownStream {} -> Nothing; _ -> Just s}

interpretStream2' shape_type elt_type repr expression =
  traceShow (text "IS2" <+> pprExp expression) $
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
         in return $ GenerateStream
            { _sexpSize = size_arg
            , _sexpCount = size_val
            , _sexpType = type_arg
            , _sexpRepr = repr
            , _sexpGenerator = \ix ->
                appExp (return writer) [] [return ix]}
       | op_var `isPyonBuiltin` the_count ->
           return $ GenerateStream
           { _sexpSize = posInftyT
           , _sexpCount = omega_count
           , _sexpType = storedIntType
           , _sexpRepr = repr
           , _sexpGenerator = counting_generator}
       | op_var `isPyonBuiltin` the_rangeIndexed ->
         let [size_index] = ty_args
             [size_val] = args
         in return $ GenerateStream
            { _sexpSize = size_index 
            , _sexpCount = size_val
            , _sexpType = storedIntType
            , _sexpRepr = repr
            , _sexpGenerator = counting_generator}
       | op_var `isPyonBuiltin` the_bind ->
         let [src_dim, tr_shape, src_type, tr_type] = ty_args
         in case args
            of [src_repr, _, src, transformer] ->
                 -- Transformer must be a single-parameter lambda function
                 case transformer
                 of ExpM (LamE _ (FunM (Fun { funTyParams = []
                                            , funParams = [param]
                                            , funBody = body}))) -> do
                      let src_shape =
                            varApp (pyonBuiltin the_array_shape)
                            [src_dim, VarT $ pyonBuiltin the_unit_shape]
                      src_stream <-
                        interpretStream2' src_shape src_type src_repr src
                      body_stream <-
                        interpretStream2' tr_shape tr_type repr body
                      
                      return $ NestedLoopStream src_stream (param, body_stream)
                    _ -> no_interpretation
               _ -> no_interpretation
       | op_var `isPyonBuiltin` the_oper_CAT_MAP ->
         let [src_type, tr_type] = ty_args
         in case args
            of [src_repr, _, src, transformer] ->
                 -- Transformer must be a single-parameter lambda function
                 case transformer
                 of ExpM (LamE _ (FunM (Fun { funTyParams = []
                                            , funParams = [param]
                                            , funBody = body}))) -> do
                      src_stream <-
                        interpretStream2' list_shape src_type src_repr src
                      body_stream <-
                        interpretStream2' list_shape tr_type repr body
                      
                      -- Convert to a nested loop stream if it has suitable
                      -- shape
                      case (sexpShape src_stream, sexpShape body_stream) of
                        (ArrayShape [dim1], ArrayShape dims) ->
                          return $ NestedLoopStream src_stream (param, body_stream)
                        _ -> return $ BindStream src_stream (param, body_stream)
                    _ -> no_interpretation
               _ -> no_interpretation
       | op_var `isPyonBuiltin` the_oper_DO ->
         let [type_arg] = ty_args
         in case args
            of [repr, writer] ->
                 return $ ReturnStream type_arg repr (return writer)
               _ -> no_interpretation
       | op_var `isPyonBuiltin` the_oper_EMPTY ->
         let [type_arg] = ty_args
         in case args
            of [repr] -> return $ EmptyStream type_arg repr
               _ -> no_interpretation
       | op_var `isPyonBuiltin` the_fun_map_Stream ->
         let [_, src_type, out_type] = ty_args
         in case args
            of [src_repr, out_repr, transformer, producer] ->
                 liftM (mapStream out_type out_repr transformer) $
                 interpretStream2' shape_type src_type src_repr producer
               _ -> no_interpretation
     _ -> case fromExpM expression
          of LetE _ binder rhs body -> do  
               body' <- interpretStream2' shape_type elt_type repr body
               return $ LetStream binder rhs body'
             CaseE _ scr alts -> do
               alts' <- mapM (interpretStreamAlt shape_type elt_type repr) alts
               let alt_shapes = map (sexpShape . altBody . fromAltS) alts'

               -- If all case alternatives have the same shape, then use
               -- the shape.  Otherwise use the original shape type assigned 
               -- to this expression.
               shapes_equal <- all_types_equal alt_shapes
               shape <- if shapes_equal
                        then return $ head alt_shapes
                        else liftM typeShape $ reduceToWhnf shape_type
               return $ CaseStream shape scr alts'
             _ -> no_interpretation
  where
    list_shape = VarT $ pyonBuiltin the_list_shape

    -- | The value \omega.
    omega_count =
      ExpM $ AppE defaultExpInfo
      (ExpM $ VarE defaultExpInfo (pyonBuiltin the_indOmega))
      [TypM posInftyT]
      [ExpM $ AppE defaultExpInfo (ExpM $ VarE defaultExpInfo (pyonBuiltin the_eqZ_refl))
       [TypM posInftyT] []]

    -- A generator for the sequence [0, 1, 2, ...]
    counting_generator ix =
      varAppE (pyonBuiltin the_stored) [TypM intType] [return ix]

    no_interpretation = do
      whnf_st <- reduceToWhnf shape_type
      return $ UnknownStream (typeShape whnf_st) elt_type repr expression

    all_types_equal [s] = return True
    all_types_equal (s:s':ss) =
      ifM (compareShapes s s') (all_types_equal (s':ss)) (return False)

-- | Map a function over the interpreted stream
mapStream :: Type               -- ^ Transformed type
          -> ExpM               -- ^ Transformed repr
          -> ExpM               -- ^ Transformer
          -> ExpS               -- ^ Producer stream
          -> ExpS               -- ^ Transformed stream
mapStream out_type out_repr transformer producer = transform producer
  where
    transform (GenerateStream sz ct ty repr gen) =
      -- Fuse the transformer into the generator expression
      let gen' ix = apply_transformer ty repr (gen ix)
      in GenerateStream sz ct out_type out_repr gen'

    transform (BindStream src (binder, body)) =
      BindStream src (binder, transform body)

    transform (NestedLoopStream src (binder, body)) =
      NestedLoopStream src (binder, transform body)

    transform (LetStream binder rhs body) =
      LetStream binder rhs (transform body)

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
      (\ [] -> return ([outType out_type], initEffectType out_type))
      (\ [] [outvar] ->
          -- Run the producer, then pass its results to the consumer
          localE (TypM producer_ty) producer_expr $ \tmpvar ->
          appExp (return transformer) [] [varE tmpvar, varE outvar])

interpretStreamAlt :: Type -> Type -> ExpM -> AltM -> TypeEvalM AltS
interpretStreamAlt shape_type elt_type repr (AltM alt) = do
  body <- interpretStream2' shape_type elt_type repr $ altBody alt
  return $ AltS $ DeCon { altConstructor = altConstructor alt
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
    of GenerateStream { _sexpSize = size_ix
                      , _sexpCount = size_val
                      , _sexpGenerator = gen} ->
         lift $
         varAppE (pyonBuiltin the_generate)
         [TypM size_ix, TypM elt_type]
         [return size_val,
          return elt_repr,
          lamE $ mkFun []
          (\ [] -> return ([intType], writerType elt_type))
          (\ [] [index_var] ->
            gen (ExpM $ VarE defaultExpInfo index_var))]

       NestedLoopStream src (pat, dst) ->
         case (sexpShape src, sexpShape dst)
         of (src_shape@(ArrayShape [dim1]), dst_shape@(ArrayShape dims)) -> do
              -- This is a nested counted loop
              let dst_shape_type = shapeType dst_shape
              src' <- MaybeT $ encodeStream2 (TypM $ shapeType src_shape) src
              dst' <- MaybeT $ encodeStream2 (TypM dst_shape_type) dst
              let oper = ExpM $ VarE defaultExpInfo (pyonBuiltin the_bind)
                  (outer_size, outer_count) = dim1
              return $
                ExpM $ AppE defaultExpInfo oper
                [outer_size,
                 TypM dst_shape_type,
                 TypM $ sexpElementType src,
                 TypM $ sexpElementType dst]
                [sexpElementRepr src, sexpElementRepr dst,
                 src',
                 ExpM $ LamE defaultExpInfo $
                 FunM $ Fun { funInfo = defaultExpInfo
                            , funTyParams = []
                            , funParams = [pat]
                            , funReturn =
                              TypM $ varApp (pyonBuiltin the_Stream)
                              [dst_shape_type, sexpElementType dst]
                            , funBody = dst'}]

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
                              TypM $ varApp (pyonBuiltin the_Stream)
                              [list_shape, sexpElementType dst]
                            , funBody = dst'}]

       LetStream binder rhs body -> do
         body' <- MaybeT $ encodeStream2 expected_shape body
         return $ ExpM $ LetE defaultExpInfo binder rhs body'

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
      return $ AltM $ DeCon { altConstructor = altConstructor alt
                          , altTyArgs = map (TypM . fromTypS) $ altTyArgs alt
                          , altExTypes = map fromTyPatS $ altExTypes alt
                          , altParams = map fromPatS $ altParams alt
                          , altBody = body}

-- | Convert a stream over an integer domain into a stream over
--   an arbitrary, contiguous subset of the integer domain.
--   Return the new stream and the size (type index and value)
--   of the original domain.
--   The variables are the size of the subset (a type index),
--   the size of the subset (a finite indexed int),
--   and the first element of the subset (an ordinary int).
--
--   The returned stream will have an array shape.
blockStream :: Var -> Var -> Var -> ExpS -> Maybe (ExpS, TypM, ExpM)
blockStream size_var count_var base_var stream =
  case stream
  of GenerateStream orig_size orig_count ty repr gen ->
       -- We don't generate values starting from zero, but rather starting
       -- from the given base.  Add the base to the index.
       let gen' ix = do
             ix' <- varAppE (pyonBuiltin the_AdditiveDict_int_add) []
                    [return ix, varE base_var]
             gen ix'
       
       in return (GenerateStream (VarT size_var) block_size ty repr gen',
                  TypM orig_size, orig_count)

     BindStream src tf -> do
       -- block the source stream
       (src', orig_size, orig_count) <-
         blockStream size_var count_var base_var src
       return (BindStream src' tf, orig_size, orig_count)

     LetStream binder rhs body -> do
       -- block the source stream
       (body', orig_size, orig_count) <-
         blockStream size_var count_var base_var body
       return (LetStream binder rhs body', orig_size, orig_count)

     CaseStream _ scr [AltS alt] -> do
       -- block the single alternative
       (body, orig_size, orig_count) <-
         blockStream size_var count_var base_var $ altBody alt
       let alt' = alt {altBody = body}
           shp = sexpShape body
       return (CaseStream shp scr [AltS alt'], orig_size, orig_count)
     
     CaseStream (ArrayShape ((orig_size, orig_count):sizes)) scr alts -> do
       -- Block each branch of the case statement.  All branches must 
       -- have the same shape. 
       alts' <- forM alts $ \ (AltS alt) -> do
         (body, _, _) <- blockStream size_var count_var base_var $ altBody alt
         return $ AltS $ alt {altBody = body}
       return (CaseStream (block_shape sizes) scr alts', orig_size, orig_count)

     _ ->
       -- The stream's shape is unknown, so we can't decompose it into blocks
       Nothing
  where
    -- The shape of a blocked stream.
    -- The stream has a known, 1D shape.
    block_shape sizes = ArrayShape ((TypM (VarT size_var), block_size) : sizes)

    block_size =
      ExpM $ AppE defaultExpInfo
      (ExpM $ VarE defaultExpInfo (pyonBuiltin the_indInt))
      [TypM (VarT size_var)]
      [ExpM $ VarE defaultExpInfo count_var]

-- | Interpret a stream and attempt to create a blocked version of it.
--
--   The blocked stream is returned along with the original stream's shape.
--   Variables holding the blocked stream's size index, size, and starting
--   counter value are returned.  These are new variables that aren't defined 
--   in the program.  The caller should generate definitions of these
--   variables.  By choosing the definitions of these variables, the caller
--   controls how the stream is blocked.
--
--   The return values are:
--
--   * block_size : intindex
--   * block_count : FinIndInt block_size
--   * start_index : int
--   * bs : Stream (array_shape block_size) elt_type
--   * full_size : intindex
--   * full_count : IndInt full_size
interpretAndBlockStream :: Type -> Type -> ExpM -> ExpM
                        -> TypeEvalM (Maybe (Var, Var, Var, ExpS, TypM, ExpM))
interpretAndBlockStream shape_type elt_type elt_repr stream_exp = do
  m_stream <- interpretStream2 shape_type elt_type elt_repr stream_exp
  case m_stream of
    Just s -> do
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
zipStreams2 :: [ExpS] -> TypeEvalM (Maybe ExpS)
zipStreams2 [] = internalError "zipStreams: Need at least one stream"
zipStreams2 [s] = return (Just s)
zipStreams2 ss
  | Just (zipped_size, zipped_count) <- zipped_shape =
      let elt_types = map sexpElementType ss
          typ = varApp (pyonTupleTypeCon num_streams) elt_types
          repr = ExpM $ AppE defaultExpInfo
                 (ExpM $ VarE defaultExpInfo (pyonTupleReprCon num_streams))
                 (map TypM elt_types)
                 (map sexpElementRepr ss)
          gen ix = varAppE (pyonTupleCon num_streams)
                   (map TypM elt_types)
                   [_sexpGenerator stream ix | stream <- ss] -- FIXME: Handle other stream types
      in return $ Just $ GenerateStream zipped_size zipped_count typ repr gen
  | otherwise = return Nothing
  where
    num_streams = length ss

    zipped_shape =
      case sequence $ map (from_array_shape . sexpShape) ss
      of Just shapes -> Just $ foldr1 zip_array_shapes shapes 
         Nothing -> Nothing
      where
        -- We can only simplify 1D array zip
        from_array_shape (ArrayShape [(ix, sz)]) = Just (fromTypM ix, sz)
        from_array_shape _ = Nothing
        
        -- Compute the shape of zipped arrays.
        -- Use the "min" operator to get the minimum length.
        zip_array_shapes (ix1, sz1) (ix2, sz2) =
          let typ = varApp (pyonBuiltin the_min_i) [ix1, ix2]
              val = ExpM $ AppE defaultExpInfo min_ii [TypM ix1, TypM ix2]
                    [sz1, sz2] 
          in (typ, val)
    
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
    (\ [] -> return ([outType acc_ty], initEffectType acc_ty))
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
       of ArrayShape [(size_ix, size_val)] ->
            varAppE (pyonBuiltin the_for)
            [size_ix, TypM acc_ty]
            [return acc_repr,
             return size_val,
             return init,
             lamE $ mkFun []
             (\ [] -> return ([intType, acc_ty, outType acc_ty],
                              initEffectType acc_ty))
             (\ [] [index_var, acc_in, acc_out] ->
               -- Call the generator function,
               -- bind its result to a local variable
               let ix = ExpM $ VarE defaultExpInfo index_var
               in localE (TypM $ sexpElementType stream)
                  (_sexpGenerator stream ix)
                  (\lv -> appExp (return acc_f) []
                          [varE acc_in, varE lv, varE acc_out])),
             return out_ptr]

     BindStream src (binder, trans) ->
       translate_nested_loop src binder trans
       
     NestedLoopStream src (binder, trans) ->
       translate_nested_loop src binder trans

     LetStream binder rhs body -> do
       -- Assign the local variable
       new_body <-
         translateStreamToFold tenv acc_ty acc_repr init acc_f out_ptr stream
       return $ ExpM $ LetE defaultExpInfo binder rhs new_body

     CaseStream shp scr alts -> do
       -- Translate each case alternative
       alts' <- forM alts $ \(AltS alt) -> do
         new_body <-
           translateStreamToFold tenv acc_ty acc_repr init acc_f out_ptr (altBody alt)
         return $ AltM $ DeCon { altConstructor = altConstructor alt
                             , altTyArgs = 
                                 map (TypM . fromTypS) $ altTyArgs alt
                             , altExTypes = map fromTyPatS $ altExTypes alt
                             , altParams = map fromPatS $ altParams alt
                             , altBody = new_body}

       return $ ExpM $ CaseE defaultExpInfo scr alts'

     ReturnStream ty repr writer -> do
       -- Run the writer, bind its result to a local variable
       localE (TypM ty) writer
         (\lv -> appExp (return acc_f) []
                 [return init, varE lv, return out_ptr])

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
  where
    -- Create a loop that takes values from 'src' and passes them to 'trans'. 
    -- The loop implements 'bind'.
    translate_nested_loop src binder trans = do
      let src_out_ty = sexpElementType src

      -- Create a new accumulator function that runs the transformer stream 
      -- and folds over it.  It will be used as the source stream's  
      -- accumulator.  The accumulator function has 'binder' as one of
      -- its parameters.
      consumer <- do
        acc_in_var <- newAnonymousVar ObjectLevel
        let m_producer_var = patMVar binder
        acc_out_var <- newAnonymousVar ObjectLevel
        let params = [patM (acc_in_var ::: acc_ty),
                      binder,
                      patM (acc_out_var ::: outType acc_ty)]
            retn = TypM $ initEffectType acc_ty
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
                        trace "castStreamExpressionShape: Unsafe shape assumption" $ Just expr
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