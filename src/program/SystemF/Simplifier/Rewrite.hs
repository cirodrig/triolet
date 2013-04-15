
{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving #-}
module SystemF.Simplifier.Rewrite
       (insertGlobalSystemFFunctions,
        RewriteRuleSet,
        getVariableReplacements,
        generalRewrites,
        parallelizingRewrites,
        sequentializingRewrites,
        combineRuleSets,
        rewriteApp)
where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Common.MonadLogic
import Builtins.Builtins
import SystemF.Build
import SystemF.IncrementalSubstitution
import SystemF.ReprDict
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
  
  -- FIXME: avoid redundant imports
  let Module {modDefs = core_defs} = core_mod
      Module { modName = mod_name
             , modImports = imports
             , modDefs = defs
             , modExports = exports} = mod
      new_imports = imports ++ concatMap defGroupMembers core_defs
  return $ Module mod_name new_imports defs exports

-- | Type index for stream expressions 
data Stream

-------------------------------------------------------------------------------
-- The rewrite monad maintains type and integer index information

data RWEnv =
  RWEnv
  { rwIdentSupply :: {-#UNPACK#-}!(IdentSupply Var)
  , rwTypeEnv     :: TypeEnv
  }

newtype RW a = RW {unRW :: ReaderT RWEnv IO a}
             deriving(Functor, Applicative, Monad, MonadIO)

runRW :: RW a -> IdentSupply Var -> TypeEnv -> IO a
runRW (RW (ReaderT f)) var_supply tenv =
  f (RWEnv var_supply tenv)

instance Supplies RW (Ident Var) where
  fresh = RW (ReaderT (\env -> supplyValue (rwIdentSupply env)))

instance TypeEnvMonad RW where
  type EvalBoxingMode RW = UnboxedMode
  getTypeEnv = RW (ReaderT (\env -> return $ rwTypeEnv env))

instance EvalMonad RW where
  liftTypeEvalM m = RW $ ReaderT $ \env ->
    runTypeEvalM m (rwIdentSupply env) (rwTypeEnv env)

liftFreshVarM :: FreshVarM a -> RW a
liftFreshVarM m = RW $ ReaderT $ \env -> runFreshVarM (rwIdentSupply env) m

-------------------------------------------------------------------------------
-- Helper functions for writing code

{-
-- | Load a value.
--
-- > case x of stored t (y : t). y
load :: Type                    -- ^ Value type to load
     -> RW ExpM                 -- ^ Expression to load
     -> RW ExpM
load ty val =
  caseE val
  [mkAlt (coreBuiltin The_stored) [ty] $
   \ [] [val] -> mkVarE val]

-- | Create a case expression to inspect a list.
--
-- > case scrutinee
-- > of make_list list_type (n : intindex)
-- >                        (sz : FinIndInt n) 
-- >                        (p : Referenced (array n list_type)).
-- >      case p
-- >      of referenced ay. $(make_body n sz ay)
caseOfList :: TypeEnv
           -> RW ExpM           -- ^ List to inspect
           -> Type              -- ^ Type of list element
           -> (Var -> Var -> Var -> RW ExpM)
              -- ^ Function from (list size index, list size, array reference)
              --   to expression
           -> RW ExpM
caseOfList tenv scrutinee list_type mk_body =
  caseE scrutinee
  [mkAlt tenv (coreBuiltin The_make_list) [list_type] $
   \ [size_index] [size, array_ref] ->
   caseE (mkVarE array_ref)
   [mkAlt tenv (coreBuiltin The_referenced) [array_type size_index] $
    \ [] [ay] -> mk_body size_index size ay]]
  where
    -- Create the type (array n list_type)
    array_type size_index =
      varApp (coreBuiltin The_arr) [VarT size_index, list_type]

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
  [mkAlt tenv (coreBuiltin The_mk_array2) [elt_type] $
   \ [size_y_index, size_x_index] [size_y, size_x, array_ref] ->
   caseE (mkVarE array_ref)
   [mkAlt tenv (coreBuiltin The_referenced) [array_type size_y_index size_x_index] $
    \ [] [ay] -> mk_body size_y_index size_x_index size_y size_x ay]]
  where
    -- Create the type (array m (array n elt_type))
    array_type size_y_index size_x_index =
      varApp (coreBuiltin The_arr) [VarT size_y_index,
                                    varApp (coreBuiltin The_arr) [VarT size_x_index, elt_type]]

caseOfTraversableDict :: RW ExpM
                      -> Type
                      -> (Var -> Var -> RW ExpM)
                      -> RW ExpM
caseOfTraversableDict scrutinee container_type mk_body =
  caseE scrutinee
  [mkAlt (coreBuiltin The_traversableDict) [container_type] $
   \ [] [trv, bld] -> mk_body trv bld]

caseOfSomeIndInt :: RW ExpM
                 -> (Var -> Var -> RW ExpM)
                 -> RW ExpM
caseOfSomeIndInt scrutinee mk_body =
  caseE scrutinee
  [mkAlt (coreBuiltin The_someIInt) [] $
   \ [intindex] [intvalue] -> mk_body intindex intvalue]

defineAndInspectIndInt int_value mk_body =
  let define_indexed_int =
        mkVarAppE (coreBuiltin The_defineIntIndex) [] [int_value]
  in caseOfSomeIndInt define_indexed_int mk_body

caseOfFinIndInt :: RW ExpM
                -> Type
                -> (Var -> RW ExpM)
                -> RW ExpM
caseOfFinIndInt scrutinee int_index mk_body =
  caseE scrutinee
  [mkAlt (coreBuiltin The_fiInt) [int_index] $
   \ [] [intvalue] -> mk_body intvalue]

caseOfIndInt :: RW ExpM
             -> Type
             -> (Var -> RW ExpM)
             -> (Var -> RW ExpM)
             -> RW ExpM
caseOfIndInt scrutinee int_index mk_finite mk_infinite =
  caseE scrutinee
  [mkAlt (coreBuiltin The_iInt) [int_index] $
   \ [] [fin] -> mk_finite fin,
   mkAlt (coreBuiltin The_iPosInfty) [int_index] $
   \ [] [pf] -> mk_infinite pf,
   mkAlt (coreBuiltin The_iNegInfty) [int_index] $
   \ [] [pf] -> mk_infinite pf]

caseOfIndInt' :: RW ExpM
              -> Type
              -> (Var -> RW ExpM)
              -> (Var -> RW ExpM)
              -> RW ExpM
caseOfIndInt' scrutinee int_index mk_finite mk_infinite =
  caseE scrutinee
  [mkAlt (coreBuiltin The_iInt) [int_index] $
   \ [] [fin] -> caseOfFinIndInt (mkVarE fin) int_index mk_finite,
   mkAlt (coreBuiltin The_iPosInfty) [int_index] $
   \ [] [pf] -> mk_infinite pf,
   mkAlt (coreBuiltin The_iNegInfty) [int_index] $
   \ [] [pf] -> mk_infinite pf]

-- | Create a list where each array element is a function of its index only
--
--   If no return pointer is given, a writer function is generated.
defineList :: Type             -- Array element type
           -> Type             -- Array size type index
           -> RW ExpM    -- Array size
           -> RW ExpM    -- Array element representation
           -> Maybe (RW ExpM)     -- Optional return pointer
           -> (Var -> RW ExpM -> RW ExpM) -- Element writer code
           -> RW ExpM
defineList elt_type size_ix size elt_repr rptr writer =
  varAppE (coreBuiltin The_make_list)
  [elt_type, size_ix]
  ([size,
    varAppE (coreBuiltin The_referenced) [array_type]
    [defineArray elt_type size_ix size elt_repr writer]] ++
   maybeToList rptr)
  where
    array_type =
      varApp (coreBuiltin The_arr) [size_ix, elt_type]

-- | Create a writer function for an array where each array element
--   is a function of its index only.
defineArray :: Type             -- Array element type
            -> Type             -- Array size type index (FinIntIndex)
            -> RW ExpM   -- Array size
            -> RW ExpM   -- Array element representation
            -> (Var -> RW ExpM -> RW ExpM) -- Element writer code
            -> RW ExpM
defineArray elt_type size_ix size elt_repr writer =
  lamE $ mkFun []
  (\ [] -> return ([outType array_type], initEffectType array_type))
  (\ [] [out_ptr] ->
    varAppE (coreBuiltin The_doall)
    [size_ix, array_type, elt_type]
    [size,
     lamE $ mkFun []
     (\ [] -> return ([intType], initEffectType elt_type))
     (\ [] [index_var] ->
       let out_expr =
             varAppE (coreBuiltin The_subscript_out) [size_ix, elt_type]
             [elt_repr, mkVarE out_ptr, mkVarE index_var]
       in writer index_var out_expr)])
  where
    array_type =
      varApp (coreBuiltin The_arr) [size_ix, elt_type] -}

storedIntType = storedType intT
boxedIntType = varApp (coreBuiltin The_Boxed) [storedIntType]

shapeOfType :: Type -> Type
shapeOfType t = varApp (coreBuiltin The_shape) [t]

array1Shape :: Type -> Type
array1Shape size =
  varApp (coreBuiltin The_arr_shape)
  [size, VarT $ coreBuiltin The_dim0]

arrayShape :: [Type] -> Type
arrayShape (size : sizes) =
  varApp (coreBuiltin The_arr_shape)
  [size, arrayShape sizes]

arrayShape [] = VarT (coreBuiltin The_dim0)

minIntIndex a b = varApp (coreBuiltin The_min_i) [a, b]

-------------------------------------------------------------------------------
-- Rewrite rules

-- Given the arguments to an application, try to create a rewritten term
type RewriteRule = ExpInfo -> [Type] -> [ExpM] -> RW (Maybe ExpM)

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
  , rewriteVariables :: Map.Map Var MkExpM
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
getVariableReplacements :: RewriteRuleSet -> FreshVarM [(Var, ExpM)]
getVariableReplacements rs =
  forM (Map.toList $ rewriteVariables rs) $ \(v, mk_e) -> do
    e <- mk_e
    return (v, e)

-- | General-purpose rewrite rules that should always be applied
generalRewrites :: RewriteRuleSet
generalRewrites = RewriteRuleSet (Map.fromList table) (Map.fromList exprs)
  where
    table = [ (coreBuiltin The_asbare, rwAsBare)
            , (coreBuiltin The_asbox, rwAsBox)
            -- , (coreBuiltin The_stencil2D, rwStencil2D)
            --, (coreBuiltin The_darr1_reduce, rwDarr1Reduce)
            --, (coreBuiltin The_darr1_reduce1, rwDarr1Reduce1)
            --, (coreBuiltin The_darr2_reduce, rwDarr2Reduce)
            --, (coreBuiltin The_arr1D_build, rwArr1DBuild)
            --, (coreBuiltin The_arr2D_build, rwArr2DBuild)
            --, (coreBuiltin The_view1ToDarr1, rwView1ToDarr1)
            -- , (coreBuiltin The_range, rwRange)
            -- , (coreBuiltin The_TraversableDict_list_traverse, rwTraverseList)
            --, (coreBuiltin The_TraversableDict_list_build, rwBuildList)
            --, (coreBuiltin The_TraversableDict_array2_traverse, rwTraverseMatrix)
            -- , (coreBuiltin The_TraversableDict_matrix_build, rwBuildMatrix)
            -- , (coreBuiltin The_TraversableDict_Stream_traverse, rwTraverseStream)
            -- , (coreBuiltin The_TraversableDict_Stream_build, rwBuildStream)
            --, (coreBuiltin The_array_build, rwBuildArray)
            --, (coreBuiltin The_chunk, rwChunk)
            --, (coreBuiltin The_outerproduct, rwOuterProduct)
            --, (coreBuiltin The_LinStream_map, rwMapStream)
            --, (coreBuiltin The_LinStream_zipWith, rwZipStream) 
            --, (coreBuiltin The_LinStream_zipWith3, rwZip3Stream)
            --, (coreBuiltin The_LinStream_zipWith4, rwZip4Stream)
            --, (coreBuiltin The_LinStream_zipWith_array, rwZipArrayStream) 
            --, (coreBuiltin The_LinStream_zipWith3_array, rwZip3ArrayStream)
            --, (coreBuiltin The_LinStream_zipWith4_array, rwZip4ArrayStream)
            , (coreBuiltin The_defineIntIndex, rwDefineIntIndex)
            , (coreBuiltin The_fromintF, rwFloatFromInt)
            , (coreBuiltin The_neI, rwIntComparison (/=))
            , (coreBuiltin The_ltI, rwIntComparison (<))
            , (coreBuiltin The_leI, rwIntComparison (<=))
            , (coreBuiltin The_gtI, rwIntComparison (>))
            , (coreBuiltin The_geI, rwIntComparison (>=))
              -- No rewrite rule for integer (==).  It's handled by
              -- the 'rwIntEqApp' function.
            , (coreBuiltin The_gcd, rwGcd)
            
            , (coreBuiltin The_negI, rwNegateInt)
            , (coreBuiltin The_addI, rwAddInt)
            , (coreBuiltin The_subI, rwSubInt)
            , (coreBuiltin The_mulI, rwMulInt)
            , (coreBuiltin The_floordivI, rwFloorDivInt)
            , (coreBuiltin The_modI, rwModInt)
            ]

    exprs = [(coreBuiltin The_count, count_expr)]
    
    -- Turn 'count' into a call to 'count_helper'
    count_expr =
      mkVarAppE (coreBuiltin The_count_helper) []
      [return $ valConE' (VarCon (coreBuiltin The_None) [] []) []]

    int0_expr = return $ litE' $ IntL 0 intT
    int1_expr = return $ litE' $ IntL 1 intT
    float0_expr = return $ litE' $ FloatL 0 floatT
    float1_expr = return $ litE' $ FloatL 1 floatT
    floatpi_expr = return $ litE' $ FloatL pi floatT

-- | Rewrite rules that transform potentially parallel algorithms into
--   explicitly parallel algorithms.
parallelizingRewrites :: RewriteRuleSet
parallelizingRewrites = RewriteRuleSet (Map.fromList table) Map.empty
  where
    table = [ --(coreBuiltin The_primitive_darr1_reduce, rwParallelDim1Reduce)
            --, (coreBuiltin The_primitive_darr1_reduce1, rwParallelDim1Reduce1)
            --, (coreBuiltin The_doall, rwParallelDoall)
            --, (coreBuiltin The_histogramArray, rwParallelHistogramArray)
            ]

-- | Rewrite rules that transform potentially parallel algorithms into
--   sequential algorithms.  The sequential algorithms are more efficient.
--   These rules should be applied after outer loops are parallelized.
sequentializingRewrites :: RewriteRuleSet
sequentializingRewrites = RewriteRuleSet (Map.fromList table) Map.empty
  where
    table = [ --(coreBuiltin The_histogramArray, rwHistogramArray)
            --, (coreBuiltin The_LinStream_reduce, rwReduceStream)
            --, (coreBuiltin The_LinStream_reduce1, rwReduce1Stream)
            --, (coreBuiltin The_LinStream_fold, rwFoldStream)
            ]

-- | Attempt to rewrite an application term.
--   If it can be rewritten, return the new expression.
--
--   The type environment is only used for looking up data types and
--   constructors.
rewriteApp :: RewriteRuleSet
           -> IdentSupply Var
           -> TypeEnv
           -> ExpInfo -> Var -> [Type] -> [ExpSM]
           -> IO (Maybe ExpM)
rewriteApp ruleset id_supply tenv inf op_var ty_args args =
  case Map.lookup op_var $ rewriteRules ruleset
  of Just rw -> let do_rewrite = do
                      subst_args <- mapM applySubstitution args
                      trace_rewrite subst_args $ rw inf ty_args subst_args
                in runRW do_rewrite id_supply tenv
     Nothing -> return Nothing
  where
    trace_rewrite _ m = m
    {-trace_rewrite subst_args m = do
      x <- m
      case x of
        Nothing -> return x
        Just e' -> do
          let old_exp = pprExp $ appE defaultExpInfo (ExpM (VarE defaultExpInfo op_var)) ty_args subst_args
          traceShow (text "rewrite" <+> old_exp $$ text "    -->" <+> pprExp e') $ return x-}

-- | Turn a call of 'asbare' into a constructor application or
--   case statement, if the type is known.  Also, cancel applications of
--   'asbare' with 'asbox'.
rwAsBare :: RewriteRule
rwAsBare inf [bare_type] [repr, arg] 
  | Just (op, _, [_, arg']) <- unpackVarAppM arg,
    op `isCoreBuiltin` The_asbox =
      -- Cancel applications of these constructors 
      -- asbare (repr, asbox (_, e)) = e
      return $ Just arg'
{-
  | otherwise = do
      -- If the bare type is "Ref t", then construct the value
      whnf_type <- reduceToWhnf bare_type
      case fromVarApp whnf_type of
        Just (ty_op, [boxed_type])
          | ty_op == refV ->
              return $ Just $ construct_stored_box boxed_type
        _ -> do
          -- If the boxed type is "Boxed t", then
          -- deconstruct and copy the value
          boxed_type <-
            reduceToWhnf $ varApp (coreBuiltin The_AsBox) [whnf_type]
          case fromVarApp boxed_type of
            Just (ty_op, [_])
              | ty_op `isCoreBuiltin` The_Boxed ->
                  fmap Just $ deconstruct_boxed whnf_type repr
            _ ->
              -- Otherwise, cannot simplify
              return Nothing
  where
    -- Create the expression
    --
    -- > storedBox boxed_type arg
    construct_stored_box boxed_type =
      conE inf (VarCon ref_conV [boxed_type] []) Nothing [] [arg]

    -- Create the expression
    --
    -- > case arg of boxed bare_type (x : bare_type) -> copy bare_type repr x
    deconstruct_boxed whnf_type repr = do
      caseE (return arg)
        [mkVarAppE (coreBuiltin The_reprSizeAlign) [whnf_type] [return repr]]
        [mkAlt (coreBuiltin The_boxed)
         [whnf_type]
         (\ [] [unboxed_ref] ->
           mkVarAppE (coreBuiltin The_copy) [whnf_type]
           [return repr, mkVarE unboxed_ref])]-}

rwAsBare inf [ty] [repr, arg, ret] = do
  -- Convert the partial application
  m_result <- rwAsBare inf [ty] [repr, arg]

  -- If successful, apply the converted expression to the return value
  return $! case m_result
            of Nothing -> Nothing
               Just e  -> Just $ appE inf e [] [ret]

rwAsBare _ _ _ = return Nothing

rwAsBox :: RewriteRule
rwAsBox inf [bare_type] [repr, arg] 
  | Just (op, _, [_, arg']) <- unpackVarAppM arg,
    op `isCoreBuiltin` The_asbare = 
      -- Cancel applications of these constructors 
      -- asbox (_, asbare (_, e)) = e
      return $ Just arg'
{-  | otherwise = do
      -- If the bare type is "Ref t", then deconstruct the value
      whnf_type <- reduceToWhnf bare_type
      case fromVarApp whnf_type of
        Just (ty_op, [boxed_type])
          | ty_op == refV ->
              fmap Just $ deconstruct_stored_box boxed_type repr
        _ -> do
          -- If the boxed type is "Boxed t", then construct the value
          boxed_type <-
            reduceToWhnf $ varApp (coreBuiltin The_AsBox) [whnf_type]
          case fromVarApp boxed_type of
            Just (ty_op, [_])
              | ty_op `isCoreBuiltin` The_Boxed ->
                return $ Just $ construct_boxed whnf_type
            _ ->
              -- Otherwise, cannot simplify
              return Nothing
  where
    -- Argument is an initializer expression whose output has 'Ref' type.
    -- Bind it to a temporary value, then deconstruct it.
    deconstruct_stored_box boxed_type repr = do
      localE bare_type (return arg)
        (\arg_val ->
          caseE (mkVarE arg_val) 
          [mkAlt ref_conV
           [boxed_type]
           (\ [] [boxed_ref] -> mkVarE boxed_ref)])
    
    construct_boxed whnf_type = do
      conE inf (VarCon (coreBuiltin The_boxed) [whnf_type] []) [arg]-}

rwAsBox _ _ _ = return Nothing

{-
-- | Rewrite 'stencil2D' to 'viewStencil2D' if the argument is a view.
rwStencil2D :: RewriteRule
rwStencil2D inf [container_type, t1, t2]
  (indexable : is_2d : repr1 : repr2 : dom1 : dom2 : f : inp : other_args) = do
  -- Is the input argument's type @view dim2 t1@?
  container_type' <- reduceToWhnf $ AppT container_type t1
  case fromVarApp container_type' of
    Just (op, [stored_arg]) | op `isCoreBuiltin` The_Ref -> do
      arg' <- reduceToWhnf stored_arg
      case fromVarApp arg' of
        Just (op, [shape_arg, _]) | op `isCoreBuiltin` The_view -> do

          -- Unbox the argument and create the new function
          tenv <- getTypeEnv
          liftM Just $
            caseE (return inp)
            [mkAlt tenv (coreBuiltin The_ref) [stored_arg]
             (\ [] [view_dom] ->
               return $
               appE inf (varE inf (coreBuiltin The_viewStencil2D))
               [t1, t2]
               (repr1 : repr2 : dom1 : dom2 : f : varE' view_dom :
                other_args))]
        _ -> return Nothing
    _ -> return Nothing
-}

{-
-- | Convert a reduction on a @mk_darr1@ to a primitive reduction.
--   The result is basically the same as if the function were inlined.
--   It's done as a rewrite rule because we want to \"inline\" only if
--   the argument is a data constructor.
rwDarr1Reduce :: RewriteRule
rwDarr1Reduce inf [size_index, ty]
  (repr : count : reducer : init : darr : other_args) =
  case fromExpM darr
  of ConE _ (VarCon con _ _) [producer] 
       | con `isCoreBuiltin` The_mk_darr1 ->
         let op = ExpM $ VarE inf $ coreBuiltin The_primitive_darr1_reduce
             exp = appE inf op [size_index, ty]
                   (repr : count : reducer : init : producer : other_args)
         in return $ Just exp

     AppE _ (ExpM (VarE _ op_var)) ty_args args
       | op_var `isCoreBuiltin` The_darr2_flatten ->
         let [size_y, size_x, _, _] = ty_args
             [count_y, count_x, darr2] = args
             op = ExpM $ VarE inf $ coreBuiltin The_darr2_reduce
             exp = appE inf op [size_y, size_x, ty]
                   (repr : count_y : count_x : reducer : init : darr2 : other_args)
         in return $ Just exp

     _ -> return Nothing

rwDarr1Reduce _ _ _ = return Nothing

-- | Convert a reduction on a @mk_darr1@ to a primitive reduction.
--   The result is basically the same as if the function were inlined.
--   It's done as a rewrite rule because we want to \"inline\" only if
--   the argument is a data constructor.
rwDarr1Reduce1 :: RewriteRule
rwDarr1Reduce1 inf [size_index, ty]
  (repr : count : reducer : darr : other_args) =
  case fromExpM darr
  of ConE _ (VarCon con _ _) [producer] 
       | con `isCoreBuiltin` The_mk_darr1 ->
         let op = ExpM $ VarE inf $ coreBuiltin The_primitive_darr1_reduce1
             exp = appE inf op [size_index, ty]
                   (repr : count : reducer : producer : other_args)
         in return $ Just exp
     _ -> return Nothing

rwDarr1Reduce1 _ _ _ = return Nothing

-- | Convert a reduction on a @mk_darr2@ to a primitive reduction.
--   The result is basically the same as if the function were inlined.
--   It's done as a rewrite rule because we want to \"inline\" only if
--   the argument is a data constructor.
rwDarr2Reduce :: RewriteRule
rwDarr2Reduce inf [size_y, size_x, ty]
  (repr : count_y : count_x : reducer : init : darr : other_args) =
  case fromExpM darr
  of ConE _ (VarCon con _ _) [producer] 
       | con `isCoreBuiltin` The_mk_darr2 ->
         let op = ExpM $ VarE inf $ coreBuiltin The_primitive_darr2_reduce
             exp = appE inf op [size_y, size_x, ty]
                   (repr : count_y : count_x : reducer : init : producer : other_args)
         in return $ Just exp

     _ -> return Nothing

rwDarr2Reduce _ _ _ = return Nothing

-- | Convert a 1D array creation on a @mk_darr1@ to a loop.
--   The result is basically the same as if the function were inlined.
--   It's done as a rewrite rule because we want to \"inline\" only if
--   the argument is a data constructor.
rwArr1DBuild :: RewriteRule
rwArr1DBuild inf [size_index, ty]
  (repr : count : darr : other_args) =
  case fromExpM darr
  of ConE _ (VarCon con _ _) [producer] 
       | con `isCoreBuiltin` The_mk_darr1 ->
         let op = ExpM $ VarE inf $ coreBuiltin The_primitive_darr1_generate
             exp = appE inf op [size_index, ty]
                   (repr : count : producer : other_args)
         in return $ Just exp
     _ -> return Nothing

rwArr1DBuild _ _ _ = return Nothing

-- | Convert a 2D array creation on a @mk_darr2@ to a loop.
--   The result is basically the same as if the function were inlined.
--   It's done as a rewrite rule because we want to \"inline\" only if
--   the argument is a data constructor.
rwArr2DBuild :: RewriteRule
rwArr2DBuild inf [size_index_y, size_index_x, ty]
  (repr : count_y : count_x : darr : other_args) =
  case fromExpM darr
  of ConE _ (VarCon con _ _) [producer] 
       | con `isCoreBuiltin` The_mk_darr2 ->
         let op = ExpM $ VarE inf $ coreBuiltin The_primitive_darr2_generate
             exp = appE inf op [size_index_y, size_index_x, ty]
                   (repr : count_y : count_x : producer : other_args)
         in return $ Just exp
     _ -> return Nothing

rwArr2DBuild _ _ _ = return Nothing

-- | Eliminate an identity transformation 
rwView1ToDarr1 :: RewriteRule
rwView1ToDarr1 inf [_, _] (vw : user : _ : other_args)
  | Just (op, [size, _], [count, darr]) <- unpackVarAppM vw,
    op `isCoreBuiltin` The_darr1ToView1 =
      return $ Just $ ExpM $ AppE inf user [size] (count : darr : other_args)

rwView1ToDarr1 _ _ _ = return Nothing
-}

{-
-- | Convert 'range' into an explicitly indexed variant
rwRange :: RewriteRule
rwRange inf [] [count] = do
  tenv <- getTypeEnv
  fmap Just $
    defineAndInspectIndInt tenv (return count)
    (\intindex intvalue ->
      varAppE (coreBuiltin The_fun_asList_Stream)
      [TypM $ array1Shape (VarT intindex),
       TypM storedIntType]
      [varAppE (coreBuiltin The_rangeIndexed) [TypM $ VarT intindex]
       [varAppE (coreBuiltin The_iInt) [TypM $ VarT intindex]
        [mkVarE intvalue]]])

rwRange _ _ _ = return Nothing-}

{- rwTraverseList :: RewriteRule
rwTraverseList inf [elt_type] [elt_repr, list] = do
  tenv <- getTypeEnv
  fmap Just $
    caseOfList tenv (return list) elt_type $ \size_index size_var array ->
    varAppE (coreBuiltin The_fun_asList_Stream) 
    [TypM $ array1Shape (VarT size_index), elt_type]
    [varAppE (coreBuiltin The_generate)
     [TypM (VarT size_index), elt_type]
     [varAppE (coreBuiltin The_iInt) [TypM $ VarT size_index] [mkVarE size_var],
      return elt_repr,
      lamE $ mkFun []
      (\ [] -> return ([intType, outType (fromTypM elt_type)],
                       initEffectType (fromTypM elt_type)))
      (\ [] [index_var, ret_var] ->
          varAppE (coreBuiltin The_copy)
          [elt_type]
          [return elt_repr,
           varAppE (coreBuiltin The_subscript)
           [TypM (VarT size_index), elt_type]
           [return elt_repr, mkVarE array, mkVarE index_var],
           mkVarE ret_var])]]
  
rwTraverseList _ _ _ = return Nothing -}

{-
rwBuildList :: RewriteRule
rwBuildList inf [elt_type] (elt_repr : stream : other_args) = do
  m_stream <- interpretStream2 (VarT (coreBuiltin The_dim1))
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
    caseOfMatrix tenv (return matrix) elt_type $
    \size_y_index size_x_index size_y_var size_x_var array ->
    varAppE (coreBuiltin The_fun_asMatrix_Stream)
    [TypM $ VarT size_y_index, TypM $ VarT size_x_index, elt_type]
    [varAppE (coreBuiltin The_iInt) [TypM $ VarT size_y_index] [mkVarE size_y_var],
     varAppE (coreBuiltin The_iInt) [TypM $ VarT size_x_index] [mkVarE size_x_var],
     varAppE (coreBuiltin The_bind)
     [TypM $ VarT size_y_index, TypM $ array1Shape (VarT size_x_index),
      TypM storedIntType, elt_type]
     [return int_repr,
      return elt_repr,
      -- Generate array indices in the Y dimension
      varAppE (coreBuiltin The_generate)
      [TypM (VarT size_y_index), TypM storedIntType]
      [varAppE (coreBuiltin The_iInt) [TypM $ VarT size_y_index] [mkVarE size_y_var],
       return int_repr,
       lamE $ mkFun []
       (\ [] -> return ([intType, outType storedIntType],
                        initEffectType storedIntType))
       (\ [] [y_var, ret_var] ->
         varAppE (coreBuiltin The_stored) [TypM intType] [mkVarE y_var, mkVarE ret_var])],

      -- For each Y index, generate array elements for the row
      lamE $ mkFun []
      (\ [] -> return ([storedIntType],
                       varApp (coreBuiltin The_Stream)
                       [varApp (coreBuiltin The_arr_shape) [VarT size_x_index, VarT (coreBuiltin The_dim0)], fromTypM elt_type]))
      (\ [] [y_var] ->
        varAppE (coreBuiltin The_generate)
        [TypM (VarT size_x_index), elt_type]
        [varAppE (coreBuiltin The_iInt) [TypM $ VarT size_x_index] [mkVarE size_x_var],
         return elt_repr,
         lamE $ mkFun []
         (\ [] -> return ([intType, outType (fromTypM elt_type)],
                          initEffectType (fromTypM elt_type)))
         (\ [] [x_var, ret_var] ->
           varAppE (coreBuiltin The_copy)
           [elt_type]
           [return elt_repr,
            subscript2D (VarT size_y_index) (VarT size_x_index)
            size_y_var size_x_var
            (mkVarE array)
            (load tenv (TypM intType) $ mkVarE y_var)
            (mkVarE x_var),
            mkVarE ret_var])])]]
  where
    int_repr = ExpM $ VarE defaultExpInfo (coreBuiltin The_repr_int) 
    
    subscript2D :: Type -> Type -> Var -> Var -> RW ExpM -> RW ExpM -> RW ExpM
                -> RW ExpM
    subscript2D y_ix x_ix y_var x_var ay y x =
      varAppE (coreBuiltin The_subscript)
      [TypM x_ix, elt_type]
      [return elt_repr,
       varAppE (coreBuiltin The_subscript)
       [TypM y_ix, TypM $ varApp (coreBuiltin The_arr) [x_ix, fromTypM elt_type]]
       [varAppE (coreBuiltin The_repr_arr)
        [TypM x_ix, elt_type]
        [mkVarE x_var, return elt_repr],
        ay,
        y],
       x]
  
rwTraverseMatrix _ _ _ = return Nothing
-}

{-
rwBuildMatrix :: RewriteRule
rwBuildMatrix inf [elt_type] (elt_repr : stream : other_args) = do
  m_stream <- interpretStream2 (VarT (coreBuiltin The_dim1))
              (fromTypM elt_type) elt_repr stream
  case m_stream of
    Just stream ->
      -- Shape should be a matrix shape
      case sexpShape stream
      of MatrixShape -> do
           m_stream' <- encodeStream2 (TypM $ VarT $ coreBuiltin The_dim2) stream
           case m_stream' of
             Just stream' -> do
               tenv <- getTypeEnv
               fmap Just $ build_matrix_expr tenv y_t y_v x_t x_v stream' other_args
             Nothing -> return Nothing
         _ ->
           internalError "rwBuildMatrix: Stream has wrong dimensionality"
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
              writerType $ varApp (coreBuiltin The_matrix) [fromTypM elt_type]
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
        varAppE (coreBuiltin The_make_matrix) [elt_type, y_t, x_t]
        (mkVarE y_fv :
         mkVarE x_fv :
         varAppE (coreBuiltin The_referenced)
         [TypM array_2d_type]
         [varAppE (coreBuiltin The_build_array)
          [y_t, TypM array_1d_type]
          [mkVarE y_fv,
           array_1d_repr,
           varAppE (coreBuiltin The_chunk)
           [y_t, TypM array_1d_shape, elt_type, TypM array_1d_type]
           [return elt_repr,
            array_1d_repr,
            return stream,
            varAppE (coreBuiltin The_build_array)
            [x_t, elt_type]
            [mkVarE x_fv, return elt_repr]]]] :
         map return other_args)
        where
          array_2d_type = varApp (coreBuiltin The_arr)
                          [fromTypM y_t, array_1d_type]
          array_1d_type = varApp (coreBuiltin The_arr)
                          [fromTypM x_t, fromTypM elt_type]
          array_1d_shape = varApp (coreBuiltin The_arr_shape)
                           [fromTypM x_t, VarT (coreBuiltin The_dim0)]
          array_1d_repr = varAppE (coreBuiltin The_repr_arr)
                          [x_t, elt_type] [mkVarE x_fv, return elt_repr]

rwBuildMatrix _ _ _ = return Nothing
-}

{-
rwTraverseStream :: RewriteRule
rwTraverseStream inf _ [_, stream] = return (Just stream)
rwTraverseStream _ _ _ = return Nothing

rwBuildStream :: RewriteRule
rwBuildStream inf _ [_, stream] = return (Just stream)
rwBuildStream _ _ _ = return Nothing

rwBuildArray :: RewriteRule
rwBuildArray inf [size, elt_type] (elt_repr : count : stream : other_args) = do
  m_stream <- interpretStream2 (VarT $ coreBuiltin The_dim1) (fromTypM elt_type) elt_repr stream
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

rwBuildArray _ _ _ = return Nothing

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
          list_type = varApp (coreBuiltin The_list) [fromTypM elt_type]

      write_array index mk_dst =
        appExp (generator (ExpM $ VarE defaultExpInfo index)) [] [mk_dst]

      define_list finite_size =
        defineList elt_type size
        (mkVarE finite_size) (return elt_repr) return_ptr write_array

      undef_list _ =
        exceptE return_type

  tenv <- getTypeEnv 
  caseOfIndInt tenv (return count) (fromTypM size) define_list undef_list

buildArrayDoall inf elt_type elt_repr size count generator = do
  let array_type = varApp (coreBuiltin The_arr) [fromTypM size, fromTypM elt_type]
      return_type = writerType array_type

      write_array index mk_dst =
        appExp (generator (ExpM $ VarE defaultExpInfo index)) [] [mk_dst]

      define_array finite_size =
        defineArray elt_type size
        (mkVarE finite_size) (return elt_repr) write_array
      
      undef_array _ =
        exceptE (writerType array_type)

  tenv <- getTypeEnv
  caseOfIndInt tenv (return count) (fromTypM size) define_array undef_array
  -}

{-
rwBindStream tenv inf
  [elt1, elt2]
  [repr1, repr2, producer, transformer] =
  case unreturnStreamTransformer transformer
  of Just map_fn ->
       fmap Just $
       varAppE (coreBuiltin The_fun_map_Stream)
       [TypM (VarT $ coreBuiltin The_list), elt1, elt2]
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
  (varAppE (coreBuiltin The_oper_EMPTY) [elt_ty] [return elt_repr])

rwGuard _ _ _ = return Nothing-}

{-
-- Try to simplify applications of 'chunk'.
--
-- 'Chunk' can create nested loops.
rwChunk :: RewriteRule
rwChunk inf [dim_y, dim_x, elt_ty, result_ty]
  [elt_repr, result_repr, size_x, stream, consumer] = do
  -- The source stream is expected to be a multidimensional array stream
  let shape = arrayShape [fromTypM dim_y, fromTypM dim_x]
      shape_1d = arrayShape [fromTypM dim_x]
  m_stream <- interpretStream2 shape (fromTypM elt_ty) elt_repr stream
  case m_stream of
    Just (NestedLoopStream src_stream (binder, producer_stream)) -> do
      -- Map over the source stream
      -- mapStream (\x. consumer (producer x)) stream
      producer_exp <- encodeStream2 (TypM shape_1d) producer_stream
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

rwOuterProduct :: RewriteRule
rwOuterProduct inf
  [TypM elt1, TypM elt2, TypM elt3]
  [repr1, repr2, repr3, transformer, src1, src2] = runMaybeT $ do
    let list_shape = VarT $ coreBuiltin The_dim1
    s1 <- MaybeT $ interpretStream2 list_shape elt1 repr1 src1
    (size_y, count_y) <- from_1d_array s1
    s2 <- MaybeT $ interpretStream2 list_shape elt2 repr2 src2
    (size_x, count_x) <- from_1d_array s2
    
    -- Create a matrix stream
    -- matrixStream (bind s1 (\x -> map (\y -> transformer x y) s2))
    var_x <- newAnonymousVar ObjectLevel
    let pattern_x = patM (var_x ::: elt1)
    transformer_function <- lift $
      lamE $ mkFun []
      (\ [] -> return ([elt2], writerType elt3))
      (\ [] [var_y] -> appExp (return transformer) [] [mkVarE var_x, mkVarE var_y])
    
    let s2' = mapStream elt3 repr3 transformer_function s2
        new_stream = MatrixStream (size_y, count_y) (size_x, count_x) $
                     NestedLoopStream s1 (pattern_x, s2')

    MaybeT $
      encodeStream2 (TypM (VarT $ coreBuiltin The_dim2)) new_stream
  where
    from_1d_array s = 
      case sexpShape s
      of ArrayShape [size] -> return size
         _                 -> mzero

rwOuterProduct _ _ _ = return Nothing
-}

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
     varAppE (coreBuiltin The_fun_map_Stream)
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

{-
rwMapStream :: RewriteRule
rwMapStream inf
  [TypM shape_type, TypM elt1, TypM elt2]
  [repr1, repr2, transformer, producer] = runMaybeT $ do
    s <- MaybeT $ interpretStream2 shape_type elt1 repr1 producer
    MaybeT $ generalizedZipStream2 elt2 repr2 transformer shape_type [s]

rwMapStream _ _ _ = return Nothing

-- | Rewrite calls to @zipStream@ when we know the size of the stream.
--
-- > zipStream(count, generate(n, f)) -> generate(n, \i -> (i, f i))
-- > zipStream(generate(n, f), count) -> generate(n, \i -> (f i, i))
-- > zipStream(generate(n1, f1), generate(n2, f2)) ->
--     generate(min(n1, n2), \i -> (f1 i, f2 i))
rwZipStream :: RewriteRule
rwZipStream inf
  [TypM shape_type, TypM elt1, TypM elt2, TypM ret]
  [repr1, repr2, repr_ret, transformer, stream1, stream2] = runMaybeT $ do
    s1 <- MaybeT $ interpretStream2 shape_type elt1 repr1 stream1
    s2 <- MaybeT $ interpretStream2 shape_type elt2 repr2 stream2
    MaybeT $ generalizedZipStream2 ret repr_ret transformer shape_type [s1, s2]

rwZipStream _ _ _ = return Nothing

rwZip3Stream :: RewriteRule
rwZip3Stream inf
  [TypM shape_type, TypM elt1, TypM elt2, TypM elt3, TypM ret]
  [repr1, repr2, repr3, repr_ret, transformer, stream1, stream2, stream3] = runMaybeT $ do
    s1 <- MaybeT $ interpretStream2 shape_type elt1 repr1 stream1
    s2 <- MaybeT $ interpretStream2 shape_type elt2 repr2 stream2
    s3 <- MaybeT $ interpretStream2 shape_type elt3 repr3 stream3
    MaybeT $ generalizedZipStream2 ret repr_ret transformer shape_type [s1, s2, s3]

rwZip3Stream _ _ _ = return Nothing

rwZip4Stream :: RewriteRule
rwZip4Stream inf
  [TypM shape_type, TypM elt1, TypM elt2, TypM elt3, TypM elt4, TypM ret]
  [repr1, repr2, repr3, repr4, repr_ret, transformer, stream1, stream2, stream3, stream4] = runMaybeT $ do
    s1 <- MaybeT $ interpretStream2 shape_type elt1 repr1 stream1
    s2 <- MaybeT $ interpretStream2 shape_type elt2 repr2 stream2
    s3 <- MaybeT $ interpretStream2 shape_type elt3 repr3 stream3
    s4 <- MaybeT $ interpretStream2 shape_type elt4 repr4 stream4
    MaybeT $ generalizedZipStream2 ret repr_ret transformer shape_type [s1, s2, s3, s4]

rwZip4Stream _ _ _ = return Nothing

rwZipArrayStream :: RewriteRule
rwZipArrayStream inf
  [TypM elt1, TypM elt2, TypM ret, TypM size1, TypM size2]
  [repr1, repr2, repr_ret, transformer, stream1, stream2] = runMaybeT $ do
    s1 <- MaybeT $ interpretStream2 (array1Shape size1) elt1 repr1 stream1
    s2 <- MaybeT $ interpretStream2 (array1Shape size2) elt2 repr2 stream2
    let size3 = array1Shape (minIntIndex size1 size2)
    MaybeT $ generalizedZipStream2 ret repr_ret transformer size3 [s1, s2]

rwZipArrayStream _ _ _ = return Nothing

rwZip3ArrayStream :: RewriteRule
rwZip3ArrayStream inf
  [TypM elt1, TypM elt2, TypM elt3, TypM ret, TypM size1, TypM size2, TypM size3]
  [repr1, repr2, repr3, repr_ret, transformer, stream1, stream2, stream3] = runMaybeT $ do
    s1 <- MaybeT $ interpretStream2 (array1Shape size1) elt1 repr1 stream1
    s2 <- MaybeT $ interpretStream2 (array1Shape size2) elt2 repr2 stream2
    s3 <- MaybeT $ interpretStream2 (array1Shape size3) elt3 repr3 stream3
    let size4 = array1Shape (minIntIndex (minIntIndex size1 size2) size3)
    MaybeT $ generalizedZipStream2 ret repr_ret transformer size4 [s1, s2, s3]

rwZip3ArrayStream _ _ _ = return Nothing

rwZip4ArrayStream :: RewriteRule
rwZip4ArrayStream inf
  [TypM elt1, TypM elt2, TypM elt3, TypM elt4, TypM ret, TypM size1, TypM size2, TypM size3, TypM size4]
  [repr1, repr2, repr3, repr4, repr_ret, transformer, stream1, stream2, stream3, stream4] = runMaybeT $ do
    s1 <- MaybeT $ interpretStream2 (array1Shape size1) elt1 repr1 stream1
    s2 <- MaybeT $ interpretStream2 (array1Shape size2) elt2 repr2 stream2
    s3 <- MaybeT $ interpretStream2 (array1Shape size3) elt3 repr3 stream3
    s4 <- MaybeT $ interpretStream2 (array1Shape size4) elt4 repr4 stream4
    let size5 = array1Shape (minIntIndex (minIntIndex (minIntIndex size1 size2) size3) size4)
    MaybeT $ generalizedZipStream2 ret repr_ret transformer size5 [s1, s2, s3, s4]

rwZip4ArrayStream _ _ _ = return Nothing

generalizedZipStream2 :: Type -> ExpM -> ExpM -> Type -> [ExpS]
                      -> RW (Maybe ExpM)
generalizedZipStream2 out_type out_repr transformer shape_type streams = do
  zipped <- zipStreams2 out_type out_repr transformer streams
  case zipped of
    Just s -> encodeStream2 (TypM shape_type) s
    Nothing -> return Nothing
-}

-- | If defining a fixed-size integer index, create the integer value
rwDefineIntIndex :: RewriteRule
rwDefineIntIndex inf [] [integer_value@(ExpM (LitE _ lit))] =
  let IntL m _ = lit
      fin_int = valConE inf (VarCon (coreBuiltin The_fiInt) [IntT m] [])
                [integer_value]
      package = valConE inf (VarCon (coreBuiltin The_someIInt) [] [IntT m])
                [fin_int]
  in return $! Just $! package

rwDefineIntIndex _ _ _ = return Nothing

-- | If converting an int constant to a float, evaluate it
rwFloatFromInt :: RewriteRule
rwFloatFromInt inf [] [integer_value@(ExpM (LitE _ lit))] =
  let IntL m _ = lit
      f = fromIntegral m
      float_exp = ExpM $ LitE inf (FloatL f floatT)
  in f `seq` return $ Just float_exp

rwFloatFromInt _ _ _ = return Nothing

-- | If comparing two integer literals, replace it with constant True or False
rwIntComparison :: (Integer -> Integer -> Bool) -> RewriteRule
rwIntComparison op inf [] [arg1, arg2]
  | ExpM (LitE _ lit1) <- arg1, ExpM (LitE _ lit2) <- arg2 =
    let IntL m _ = lit1
        IntL n _ = lit2
    in return $! Just $! case op m n
                         of True -> true_value
                            False -> false_value
  | otherwise = return Nothing
  where
    true_value = valConE inf (VarCon (coreBuiltin The_True) [] []) []
    false_value = valConE inf (VarCon (coreBuiltin The_False) [] []) []

rwNegateInt :: RewriteRule
rwNegateInt inf [] [ExpM (LitE _ lit)] =
  let IntL m t = lit
  in return $! Just $! ExpM (LitE inf (IntL (negate m) t))

rwNegateInt _ _ _ = return Nothing

rwAddInt :: RewriteRule
rwAddInt inf [] [e1, e2]
  | ExpM (LitE _ l1) <- e1, ExpM (LitE _ l2) <- e2 =
      let IntL m t = l1
          IntL n _ = l2
      in return $! Just $! ExpM (LitE inf (IntL (m + n) t))

  -- Eliminate add of zero
  | ExpM (LitE _ (IntL 0 _)) <- e1 = return $ Just e2
  | ExpM (LitE _ (IntL 0 _)) <- e2 = return $ Just e1

rwAddInt _ _ _ = return Nothing

rwSubInt :: RewriteRule
rwSubInt inf [] [e1, e2]
  | ExpM (LitE _ l1) <- e1, ExpM (LitE _ l2) <- e2 =
      let IntL m t = l1
          IntL n _ = l2
      in return $! Just $! ExpM (LitE inf (IntL (m - n) t))

  -- Eliminate subtract of zero
  | ExpM (LitE _ (IntL 0 _)) <- e1 = return $ Just $ negateIntExp inf e2
  | ExpM (LitE _ (IntL 0 _)) <- e2 = return $ Just e1

  -- x - x = 0
  | ExpM (VarE _ v1) <- e1, ExpM (VarE _ v2) <- e2, v1 == v2 =
    return $ Just zero_lit
  where
    zero_lit = ExpM $ LitE inf (IntL 0 intT)

rwSubInt _ _ _ = return Nothing

rwMulInt :: RewriteRule
rwMulInt inf [] [e1, e2]
  | ExpM (LitE _ l1) <- e1, ExpM (LitE _ l2) <- e2 =
      let IntL m t = l1
          IntL n _ = l2
      in return $! Just $! ExpM (LitE inf (IntL (m * n) t))

  -- Eliminate product of zero
  | ExpM (LitE _ (IntL 0 _)) <- e1 = return $ Just zero_lit
  | ExpM (LitE _ (IntL 0 _)) <- e2 = return $ Just zero_lit

  -- Eliminate product of one
  | ExpM (LitE _ (IntL 1 _)) <- e1 = return $ Just e2
  | ExpM (LitE _ (IntL 1 _)) <- e2 = return $ Just e1
  where
    zero_lit = ExpM $ LitE inf (IntL 0 intT)

rwMulInt _ _ _ = return Nothing

rwFloorDivInt :: RewriteRule
rwFloorDivInt inf [] [e1, e2]
  | ExpM (LitE _ l1) <- e1, ExpM (LitE _ l2) <- e2 =
      let IntL m t = l1
          IntL n _ = l2
      in if n == 0
         then return $ Just $ ExpM (ExceptE inf t) -- divide by zero
         else return $! Just $! ExpM (LitE inf (IntL (m `div` n) t))

  -- Simplify division by 1 or -1
  | ExpM (LitE _ (IntL 1 _)) <- e2 = return $ Just e1
  | ExpM (LitE _ (IntL (-1) _)) <- e2 = return $ Just $ negateIntExp inf e1

rwFloorDivInt _ _ _ = return Nothing

rwModInt :: RewriteRule
rwModInt inf [] [e1, e2]
  | ExpM (LitE _ l1) <- e1, ExpM (LitE _ l2) <- e2 =
      let IntL m t = l1
          IntL n _ = l2
      in if n == 0
         then return $ Just $ ExpM (ExceptE inf t) -- divide by zero
         else return $! Just $! ExpM (LitE inf (IntL (m `mod` n) t))

  -- Simplify remainder division by 1 or -1
  | ExpM (LitE _ (IntL 1 _)) <- e2 = return $ Just $ zero_lit
  | ExpM (LitE _ (IntL (-1) _)) <- e2 = return $ Just $ zero_lit
  where
    zero_lit = ExpM $ LitE inf (IntL 0 intT)

rwModInt _ _ _ = return Nothing

rwGcd :: RewriteRule
rwGcd inf [] [e1, e2]
  | ExpM (LitE _ l1) <- e1, ExpM (LitE _ l2) <- e2 =
    let IntL m t = l1
        IntL n _ = l2
    in if m == 0 && n == 0      -- gcd 0 0 = 0
       then return $ Just $ ExpM (LitE inf (IntL 0 t))
       else return $! Just $! ExpM (LitE inf (IntL (gcd m n) t))
  -- gcd 1 x = 1
  -- gcd x 1 = 1
  | ExpM (LitE _ (IntL 1 _)) <- e1 = return $ Just $ one_lit
  | ExpM (LitE _ (IntL 1 _)) <- e2 = return $ Just $ one_lit
  -- gcd x x = x
  | ExpM (VarE _ v1) <- e1, ExpM (VarE _ v2) <- e2, v1 == v2 =
    return $ Just e1
  where
    one_lit = ExpM $ LitE inf (IntL 1 intT)

rwGcd _ _ _ = return Nothing

negateIntExp inf e = appE inf neg_op [] [e]
  where
    neg_op = varE' (coreBuiltin The_negI)
