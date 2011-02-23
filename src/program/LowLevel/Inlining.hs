{-| Function inlining.
-}

{-# LANGUAGE ViewPatterns, FlexibleInstances, Rank2Types #-}
module LowLevel.Inlining
       (funIsInlinable, funSmallEnoughForInlining, inlineModule)
where

import Prelude hiding(mapM)

import Control.Applicative
import Control.Monad hiding(mapM)
import Control.Monad.Reader hiding(mapM)
import Control.Monad.Trans
import Data.Graph.Inductive(Gr)
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS
import qualified Data.IntMap as IntMap
import Data.List as List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Monoid
import Data.Traversable
import Debug.Trace

import Common.Error
import Common.Identifier
import LowLevel.FreshVar
import LowLevel.Build
import LowLevel.CodeTypes
import LowLevel.Syntax
import LowLevel.Rename
import LowLevel.Print
import Globals

closureInlineCutoff = 20
primInlineCutoff = 5

debugInlining = False

-- | For debugging, show what's inlined
inlStatus message k = 
  if debugInlining
  then trace message k
  else k

-------------------------------------------------------------------------------
-- Topological sorting

-- | Topologically sort a group of function definitions.  If there are SCCs,
--   pick an arbitrary order for the functions in the SCCs.
--
-- This way of ordering function definitions is probably more
-- complicated than necessary.
topSortDefGroup :: [FunDef] -> [FunDef]
topSortDefGroup defs =
  let nodes = map definiendum defs
      node_map = Map.fromList $ zip nodes [0..]
      edges = concatMap (findReferences (Set.fromList $ map definiendum defs)) defs
      
      gr = mkUGraph
           [0 .. length nodes - 1]
           [(node_map Map.! s, node_map Map.! d) | (s, d) <- edges]
      gr' = breakReferenceLoops gr
  in map (defs !!) $ concat $ reverse $ scc gr'

breakReferenceLoops :: Gr () () -> Gr () ()
breakReferenceLoops gr =
  case find ((> 1) . length) $ scc gr
  of Nothing -> gr
     Just (n:_) ->
       case match n gr
       of (Just (_, n, (), out_edges), gr') ->
            breakReferenceLoops (([], n, (), out_edges) & gr')

findReferences :: Set.Set Var -> FunDef -> [(Var, Var)]
findReferences referents (Def fname fun) = [(fname, v) | v <- find_fun fun]
  where
    find_fun f = find_stm $ funBody f
    find_stm statement =
      case statement
      of LetE _ rhs body -> find_atom rhs ++ find_stm body
         LetrecE defs body -> concatMap (find_fun . definiens) defs ++
                              find_stm body
         SwitchE s alts -> concatMap (find_stm . snd) alts ++ find_val s
         ReturnE a -> find_atom a

    find_atom atom =
      case atom
      of ValA vs -> concatMap find_val vs
         CallA _ v vs -> concatMap find_val (v:vs)
         PrimA _ vs -> concatMap find_val vs
         PackA _ vs -> concatMap find_val vs
         UnpackA _ v -> find_val v

    find_val value =
      case value
      of VarV v | v `Set.member` referents -> [v]
                | otherwise -> []
         RecV _ vs -> concatMap find_val vs
         LitV _ -> []
         LamV f -> find_fun f

-------------------------------------------------------------------------------
-- Finding function endpoints 

{- $functionendpoints

When inlining a function, the code that was after the function call gets moved
to the end of the inlined function body.  To do that, the end(s) of the
function body must be found.  In particular, code should not be inserted after
a tail call if avoidable, because turning a tail call into a non-tail-call
hurts performance.  Instead, code should go at the end of the callee.

Functions are scanned before inlining to find their /endpoints/.  A
function @g@ is an endpoint of @f@ if it can only be reached through tail
calls from @f@ or from endpoints of @f@.  The code is scanned to build a
/tail-calls/ graph in which an edge @f -> g@ means that @f@ tail-calls @g@
and @g@ is not referenced in a way other than a tail call.  The roots of the
graph, that is, functions that are used in some way other than a tail call,
are also identified.  Reachability from roots is determined using depth-first
search.  If any node is reachable from multiple roots, it is not an endpoint;
the remaining reachable set are endpoints.

A second scan is then performed to determine how many places a function's
return code must be modified.  Inlining is performed differently depending
on whether the answer is zero, one, or many.  If zero, the continuation
code is discarded.  If one, the continuation code is put at the unique
return site.  If many, a continuation function is created and a tail call
to the continuation is inserted at each return site.
-}

-- | Information about observed tail calls observed in a function.
--
--   This keeps track of roots, functions that are defined in the scanned
--   scope, and tail calls.
data ObservedTailCalls = ObservedTailCalls [Var] [Var] [(Var, Var)]

instance Monoid ObservedTailCalls where
  mempty = ObservedTailCalls [] [] []
  ObservedTailCalls x1 y1 z1 `mappend` ObservedTailCalls x2 y2 z2 =
    ObservedTailCalls (x1 ++ x2) (y1 ++ y2) (z1 ++ z2)

-- | A tail call scan.  The scan needs to know the function in which
--   the current code is contained and the arity of all locally defined
--   functions.  For lambda functions, 'Nothing' is used.
type TailCallScan = Maybe Var -> IntMap.IntMap Int -> ObservedTailCalls

setCallingContext :: Maybe Var -> TailCallScan -> TailCallScan
setCallingContext mv f = \_ arities -> f mv arities

-- | Scan code that may use a definition of a function.  The function's
--   arity is given as a parameter.
withDefinition :: Var -> Int -> TailCallScan -> TailCallScan
withDefinition v arity f = \cc arities -> 
  let arities' = IntMap.insert (fromIdent $ varID v) arity arities
      ObservedTailCalls roots defs edges = f cc arities'
  in ObservedTailCalls roots (v:defs) edges

-- | Use a variable in a non-tail-call context
use :: Var -> TailCallScan
use v = scanner
  where
    scanner _ arities
      | fromIdent (varID v) `IntMap.member` arities =
          ObservedTailCalls [v] [] []
      | otherwise = mempty

-- | Use a variable in a tail call
useTailCall :: Var -> Int -> TailCallScan
useTailCall v num_args = scanner
  where
    scanner ctx arities =
      case IntMap.lookup (fromIdent $ varID v) arities
      of Nothing -> mempty      -- Variable is ignored 
         Just arity | arity /= num_args -> non_tail_call
                    | otherwise -> case ctx
                                   of Nothing -> non_tail_call
                                      Just caller -> tail_call caller v
    non_tail_call = ObservedTailCalls [v] [] []
    tail_call caller callee = ObservedTailCalls [] [] [(caller, callee)]

tailCallScanVal :: Val -> TailCallScan
tailCallScanVal value =
  case value
  of VarV v -> use v
     RecV _ vs -> tailCallScanVals vs
     LitV _ -> mempty
     LamV f -> setCallingContext Nothing $ tailCallScanFun f
     
tailCallScanVals :: [Val] -> TailCallScan
tailCallScanVals vs = mconcat $ map tailCallScanVal vs

-- | Scan an atom that's not in tail position
tailCallScanAtom :: Atom -> TailCallScan
tailCallScanAtom (ValA vs) = tailCallScanVals vs
tailCallScanAtom (CallA _ op args) = tailCallScanVals (op:args)
tailCallScanAtom (PrimA _ vs) = tailCallScanVals vs
tailCallScanAtom (PackA _ vs) = tailCallScanVals vs
tailCallScanAtom (UnpackA _ v) = tailCallScanVal v

tailCallScanStm :: Stm -> TailCallScan
tailCallScanStm statement =
  case statement
  of LetE params rhs body ->
       tailCallScanAtom rhs `mappend` tailCallScanStm body
     LetrecE defs body ->
       tailCallScanDefs defs $ tailCallScanStm body
     SwitchE scrutinee alternatives ->
       mconcat $
       tailCallScanVal scrutinee : map (tailCallScanStm . snd) alternatives

     -- Scan a tail call
     ReturnE (CallA _ (VarV op) args) ->
       useTailCall op (length args) `mappend` tailCallScanVals args
     ReturnE atom ->
       tailCallScanAtom atom

tailCallScanFun :: Fun -> TailCallScan
tailCallScanFun f = tailCallScanStm (funBody f)

tailCallScanDefs defs scan = with_definitions (scan `mappend` scan_definitions)
  where
    with_definitions k = foldr with_definition k defs
    with_definition def k =
      withDefinition (definiendum def) (length $ funParams $ definiens def) k
    
    scan_definitions =
      mconcat [setCallingContext (Just fname) $ tailCallScanFun fun
              | Def fname fun <- defs]

-- | Scan a top-level function.  Indicate that the function is used outside of
--   the scanned code.
tailCallScanTopLevelFunction :: FunDef -> TailCallScan
tailCallScanTopLevelFunction def =
  tailCallScanDefs [def] (use $ definiendum def)

-- | Create the tail-call graph of a top-level function.
-- Return the set of root nodes and the graph.
mkTailCallGraph :: FunDef -> ([Node], Gr Var ())
mkTailCallGraph fdef = 
  let ObservedTailCalls roots defs edges =
        tailCallScanTopLevelFunction fdef no_context IntMap.empty
        where
          no_context = internalError "mkTailCallGraph: No calling context"
      
      -- Get the set of roots and the set of all defined functions.
      root_set = Set.fromList roots
      all_nodes = Set.fromList defs -- Making a set removes duplicates
      node_map :: Map.Map Var Node
      node_map = Map.fromList $ zip (Set.toList all_nodes) [1..]
      root_nodes = [node_map Map.! v | v <- Set.toList root_set]

      graph_edges =
        [(node_map Map.! s, node_map Map.! d, ())
        | (s, d) <- edges, not $ d `Set.member` root_set]
      graph_nodes = [(n, l) | (l, n) <- Map.assocs node_map]
      graph = mkGraph graph_nodes graph_edges
  in (root_nodes, graph)

-- | For each root node of the tail-call graph, list its endpoints
type Endpoints = [(Var, [Var])]

getEndpoints :: FunDef -> Endpoints
getEndpoints fdef =
  let -- Get the tail call graph
      (roots, gr) = mkTailCallGraph fdef

      -- Start with the reachability graph
      endpoints = [(root, reachable root gr) | root <- roots]

      -- If a node is in multiple endpoints lists, remove it and make it its
      -- own endpoint
      multiple_endpoints = [n | n <- nodes gr, memberN 2 n (map snd endpoints)]
      f_endpoints = [(n, [n]) | n <- multiple_endpoints] ++
                    [(n, ns List.\\ multiple_endpoints) | (n, ns) <- endpoints]

      getlab node = case lab gr node
                    of Just l -> l
                       Nothing -> internalError "getEndpoints"
  in [(getlab n, map getlab e) | (n, e) <- f_endpoints]
  where
    -- memberN n x xss -> True if x appears in at least n members of xss 
    memberN 0 _ _        = True
    memberN _ _ []       = False
    memberN n x (xs:xss) = let n' = if x `elem` xs then n - 1 else n
                           in memberN n' x xss

-------------------------------------------------------------------------------
-- Prepare a function for inlining

-- | A function that has been prepared for inlining.
--   Given the inlined function's continuation, you can produce the
--   inlined function as a statement.
data Inlinable a = Inlinable !Uses (([Var], Stm) -> a)

instance Functor Inlinable where
  fmap f (Inlinable u g) = Inlinable u (f . g)

instance Applicative Inlinable where
  pure x  = Inlinable ZeroUses (const x)
  Inlinable u1 f <*> Inlinable u2 x =
    Inlinable (u1 `mappend` u2) (\k -> f k $ x k)

-- | Prepare a function for inlining.  Called by makeInlinable.
--
--   The function must not use a stack frame.
makeInlinableFunction :: Endpoints -> FunDef -> Inlinable Stm
makeInlinableFunction endpoints (Def fun_name f) 
  | funFrameSize f /= 0 =
      internalError "makeInlinableFunction: Function uses stack frame"
  | otherwise = inl_stm $ funBody f
  where
    inl_stm statement =
      case statement
      of LetE lhs rhs body -> LetE lhs rhs <$> inl_stm body
         LetrecE defs body ->
           LetrecE <$> traverse inl_def defs <*> inl_stm body
         SwitchE scr alts -> SwitchE scr <$> traverse inl_alt alts
         ReturnE (CallA _ (VarV op) _)
           | is_endpoint op ->
             -- The statement will be inlined into this local function
             pure statement
         ReturnE atom ->
             -- Pass the atom's result to the continuation
             Inlinable OneUse $ \(retvars, cont) -> LetE retvars atom cont

    inl_alt (tag, stm) = fmap ((,) tag) $ inl_stm stm

    inl_def (Def fname f)
      | is_endpoint fname = mk_def <$> inl_stm (funBody f)
      | otherwise = pure (Def fname f)
      where
        mk_def new_body =
          Def fname $
          mkFun (funConvention f) (funInlineRequest f) 0 (funParams f) (funReturnTypes f) new_body

    endpoints_of_f = case lookup fun_name endpoints
                     of Nothing -> internalError "makeInlinableFunction"
                        Just x  -> x
    is_endpoint var = var `elem` endpoints_of_f

-- | Specification of an inlinable function.
--   Includes the function body (for inlining in tail position) and
--   an inlinable function body (for non-tail position).
data InlSpec =
  InlSpec !Bool !CallConvention !CodeSize !Uses [Var] !Stm !(Inlinable Stm)

makeInlinable :: Var -> Fun -> FreshVarM InlSpec
makeInlinable v f = do
  let cc        = funConvention f
      code_size = funSize f
      uses      = funUses f
      inl_req   = funInlineRequest f
  -- Rename to avoid name conflicts
  f' <- renameFun RenameEverything emptyRenaming f
  let endpoints = getEndpoints (Def v f')
  let inlinable = makeInlinableFunction endpoints (Def v f')
  return $ InlSpec inl_req cc code_size uses (funParams f') (funBody f') inlinable

makeDefInlinable :: FunDef -> FreshVarM InlSpec
makeDefInlinable (Def v f) = makeInlinable v f

makeLambdaFunInlinable :: Fun -> FreshVarM InlSpec
makeLambdaFunInlinable f = do
  -- Create a dummy variable name for the lambda function
  let ty = case funConvention f
           of PrimCall -> PointerType
              ClosureCall -> OwnedType
  v <- newAnonymousVar (PrimType ty)
  makeInlinable v f

-- | Make all imported functions that have function bodies inlinable
makeImportsInlinable :: [Import] -> FreshVarM (IntMap.IntMap InlSpec)
makeImportsInlinable imports = do
  specs <- mapM make_import $ mapMaybe get_imported_function imports
  return $ IntMap.fromList specs
  where
    make_import (v, f) = do
      spec <- makeInlinable v f
      return (fromIdent $ varID v, spec)

    get_imported_function impent =
      case impent
      of ImportClosureFun _ (Just f) -> Just (importVar impent, f)
         ImportPrimFun _ _ (Just f)  -> Just (importVar impent, f)
         _ -> Nothing

-------------------------------------------------------------------------------
-- Specialize a function that has been partially applied

-- | Specialize a lambda function.
--
--   For each parameter whose argument is given, the argument is bound 
--   in a let expression.  A specialized function with the remaining parameters
--   is returned.
specializeLambda fun args
  | length args >= length (funParams fun) || 
    funConvention fun /= ClosureCall =
      internalError "specializeLamba"

  | otherwise =
      let bindings = zip (funParams fun) args
          leftover_params = drop (length args) $ funParams fun
      in do forM_ bindings $ \(param, val) -> bindAtom1 param $ ValA [val]
            return $ fun {funParams = leftover_params}

-------------------------------------------------------------------------------

type GenM a = Gen FreshVarM a

instance (Monad m, Applicative m) => Applicative (Gen m) where
  pure x = lift (pure x)
  (<*>) = ap

type Inl m a = ReaderT (IntMap.IntMap InlSpec) m a 
               
type InlG a = Inl (Gen FreshVarM) a
type InlF a = Inl FreshVarM a

embedInlF :: InlF a -> InlG a
embedInlF (ReaderT f) =
  ReaderT $ \env -> lift (f env)

-- | Run an inlining computation and get the code it generates
execInlG :: [ValueType] -> InlG Stm -> InlF Stm
execInlG return_type (ReaderT f) =
  ReaderT $ \env -> execBuild return_type (f env)

-- | A map from variable ID to inlineable function.  The map only contains
--   entries for functions that may be inlined.
type InlineEnv = IntMap.IntMap Fun

assignCallParameters params args 
  | length params /= length args =
    internalError "assignCallParameters: wrong number of parameters"
  | otherwise = lift $ zipWithM_ bind_arg params args
  where
    bind_arg param arg = bindAtom1 param $ ValA [arg]

-- | Return True if the function is judged /profitable/ to inline.
worthInlining inline_requested fcc fsize fuses
  | inline_requested = True
  | fuses == OneUse = True
  | fcc == ClosureCall,
    Just sz <- fromCodeSize fsize = sz < closureInlineCutoff
  | fcc == PrimCall,
    Just sz <- fromCodeSize fsize = sz < primInlineCutoff
  | otherwise = False

-- | Return True if it's possible to inline the function.
funIsInlinable f =
  -- Function must not use stack data
  funFrameSize f == 0 

-- | Is this function small enough to be worth inlining?
funSmallEnoughForInlining :: Fun -> Bool
funSmallEnoughForInlining f =
  worthInlining (funInlineRequest f) (funConvention f) (funSize f) (funUses f)

tryInlineTailCall :: CallConvention
                  -> Var            -- ^ The callee
                  -> [Val]          -- ^ The operands of the call
                  -> InlG Stm       -- ^ The continuation
tryInlineTailCall cc op args = do
  inline_specs <- ask
  inline $ IntMap.lookup (fromIdent $ varID op) inline_specs
  where
    inline Nothing = no_inline
    inline (Just (InlSpec inl_req fcc fsize fuses params stm _)) 
      | length args /= length params = no_inline
      | worthInlining inl_req fcc fsize fuses =
          inlStatus ("Inlining: " ++ show (pprVar op)) $ 
          inlineTailCall params args stm
      | otherwise = no_inline

    no_inline = inlStatus ("Not inlining: " ++ show (pprVar op)) $ do
      return $ ReturnE $ CallA cc (VarV op) args

tryInlineCall :: CallConvention
              -> Var            -- ^ The callee
              -> [Val]          -- ^ The operands of the call
              -> [Var]          -- ^ The result variables
              -> InlG Stm       -- ^ The continuation
              -> InlG Stm       -- ^ The inlined call generator
tryInlineCall cc op args retvars mk_cont = do
  inline_specs <- ask
  inline $ IntMap.lookup (fromIdent $ varID op) inline_specs
  where
    -- This function isn't inlinable
    inline Nothing = no_inline
      
    inline (Just (InlSpec inl_req inl_cc inl_size inl_uses params _ inl_stm))
      | cc /= inl_cc = internalError "tryInlineCall: Calling convention mismatch"
      | length args /= length params = no_inline
      | not $ worthInlining inl_req inl_cc inl_size inl_uses = no_inline
      | otherwise = inlStatus ("Inlining: " ++ show (pprVar op)) $ 
                    inlineCall params args retvars inl_stm mk_cont

    no_inline = inlStatus ("Not inlining: " ++ show (pprVar op)) $ do
      lift $ bindAtom retvars $ CallA cc (VarV op) args
      mk_cont

inlineTailLambda cc fun args =
  case length args `compare` length (funParams fun)
  of LT ->
       -- Undersaturated call, returning a function.
       -- Bind the known arguments to variables and define the function.
       if cc == ClosureCall
       then do specialized_fun <- lift $ specializeLambda fun args
               return $ ReturnE $ ValA [LamV specialized_fun]
       else internalError "inlineTailLambda: Malformed function call"
     EQ -> do
      InlSpec _ _ _ _ params stm _ <- lift $ lift $ makeLambdaFunInlinable fun
      inlineTailCall params args stm
     GT -> do
       -- Oversaturated call.
       -- Inline the call (not a tail call) with the correct number of arguments.
       -- In the continuation, call with the remaining arguments.
       ret_var <- lift $ lift $ newAnonymousVar (PrimType OwnedType)
       let now_args = take (length (funParams fun)) args
           later_args = drop (length (funParams fun)) args
           call_remaining_args :: InlG Stm
           call_remaining_args =
             return $ ReturnE $ closureCallA (VarV ret_var) later_args
       inlineLambda cc fun now_args [ret_var] call_remaining_args

inlineLambda cc fun args retvars mk_cont =
  case length args `compare` length (funParams fun)
  of LT ->
       -- Undersaturated call, returning a function.
       -- Bind the known arguments to variables and define the function.
       case retvars
       of [retvar]
            | cc == ClosureCall && varType retvar == PrimType OwnedType -> do
                specialized_fun <- lift $ specializeLambda fun args 
                lift $ emitLetrec [Def retvar specialized_fun]
                mk_cont
          _ ->
            internalError "inlineLambda: Malformed function call"
     EQ -> do
       InlSpec _ _ _ _ params _ inl_stm <-
         lift $ lift $ makeLambdaFunInlinable fun
       inlineCall params args retvars inl_stm mk_cont
     GT -> do
       -- Oversaturated call.
       -- Inline the call with the correct number of arguments.
       -- In the continuation, call with the remaining arguments.
       ret_var <- lift $ lift $ newAnonymousVar (PrimType OwnedType)
       let now_args = take (length (funParams fun)) args
           later_args = drop (length (funParams fun)) args
           call_remaining_args :: InlG Stm
           call_remaining_args = do
             -- Call the function
             lift $ bindAtom retvars $ closureCallA (VarV ret_var) later_args
             -- Do everything else
             mk_cont
       inlineLambda cc fun now_args [ret_var] call_remaining_args

inlineTailCall params args stm = do
  assignCallParameters params args
  return stm

inlineCall params args retvars inl_stm mk_cont = do
  assignCallParameters params args
  case inl_stm of
    Inlinable ZeroUses inl ->
      -- Ignore the continuation
      let err = internalError "tryInlineCall"
      in return $ inl (err, err)
    Inlinable OneUse inl -> do
      -- Inline the continuation
      cont <- embedInlF $ execInlG (map varType retvars) mk_cont
      return $ inl (retvars, cont)
    Inlinable ManyUses inl -> do
      -- Create a local function for the continuation
      lift $ getContinuation True retvars $ \cont ->
        return $ inl (retvars, cont)
      mk_cont

inlVal :: Val -> InlF Val
inlVal value =
  case value
  of VarV {} -> return value
     RecV rec vs -> RecV rec <$> inlValues vs
     LitV {} -> return value
     LamV f -> LamV <$> inlFun f

inlValues :: [Val] -> InlF [Val]
inlValues = mapM inlVal

inlAtom :: Atom -> InlF Atom
inlAtom atom =
  case atom
  of ValA vs -> ValA <$> inlValues vs
     CallA cc op args -> CallA cc <$> inlVal op <*> inlValues args
     PrimA op args -> PrimA op <$> inlValues args
     PackA rec vals -> PackA rec <$> inlValues vals
     UnpackA rec val -> UnpackA rec <$> inlVal val

-- | Perform inlining in a statement.
inlStatement :: [ValueType]     -- ^ Statement's return types
             -> Stm             -- ^ Statement to process
             -> InlG Stm        -- ^ Produce a statement with inlined calls
inlStatement rt statement =
  case statement
  of LetE lhs atom body -> do 
       atom' <- embedInlF $ inlAtom atom
       case atom' of
         CallA cc (VarV op_var) args ->
           tryInlineCall cc op_var args lhs $ inlStatement rt body
         CallA cc (LamV op_fun) args ->
           inlineLambda cc op_fun args lhs $ inlStatement rt body
         _ -> do lift $ bindAtom lhs atom'
                 inlStatement rt body
     LetrecE defs body ->
       inlDefGroupG defs $ inlStatement rt body
     SwitchE scrutinee alternatives -> do
       scrutinee' <- embedInlF $ inlVal scrutinee
       alts' <- mapM inl_alt alternatives
       return $ SwitchE scrutinee' alts'
     ReturnE atom -> do
       atom' <- embedInlF $ inlAtom atom
       case atom' of 
         CallA cc (VarV op_var) args -> tryInlineTailCall cc op_var args
         CallA cc (LamV op_fun) args -> inlineTailLambda cc op_fun args
         _ -> return (ReturnE atom')
  where
    inl_alt (lit, stm) = do
      stm' <- embedInlF $ execInlG rt $ inlStatement rt stm
      return (lit, stm')

-- | Perform inlining in a function
inlFun :: Fun -> InlF Fun
inlFun f = do
  body <- execInlG rt $ inlStatement rt (funBody f)
  return $ f {funBody = body}
  where
    rt = funReturnTypes f

-- TODO: Inlining in definition groups; find SCCs and choose loop breakers
inlDefGroupF defs m =
  foldr inline_def (fmap ((,) []) m) $ topSortDefGroup defs 
  where
    inline_def def m = do
      def' <- inlDef def
      (defs', x) <- withDefF def' m
      return (def' : defs', x)

inlDefGroupG defs m = inline_defs id $ topSortDefGroup defs
  where
    inline_defs defs' (d:ds) = do
      def' <- embedInlF $ inlDef d
      withDefG def' $ inline_defs (defs' . (def':)) ds
    
    inline_defs defs' [] = do
      lift $ emitLetrec (defs' [])
      m

inlDef (Def v f) = Def v <$> inlFun f

withDefsG defs m = foldr withDefG m defs
withDefsF defs m = foldr withDefF m defs

withDefG :: FunDef -> InlG a -> InlG a
withDefG = withDef lift

withDefF :: FunDef -> InlF a -> InlF a
withDefF = withDef id

-- | Consider a function definition for inlining.  If it is suitable, then
--   add it to the local environment.
--
-- FIXME: only inline if function is small
withDef :: Monad m =>
           (forall a. FreshVarM a -> m a) -> FunDef -> Inl m a -> Inl m a
withDef t def@(Def v f) m 
  | not $ funIsInlinable f = m 
  | otherwise = do
      new_inline_spec <- lift $ t $ makeDefInlinable def
      local (add_inline_spec new_inline_spec) m
  where
    add_inline_spec new_inline_spec inline_specs =
      IntMap.insert (fromIdent $ varID v) new_inline_spec inline_specs

-------------------------------------------------------------------------------

inlineModule :: Module -> IO Module
inlineModule mod =
  withTheLLVarIdentSupply $ \var_ids -> do
    -- Inline functions
    let (fdefs, ddefs) = partitionGlobalDefs $ moduleGlobals mod
    (fdefs', ()) <- inline_defs var_ids fdefs
    let gdefs' = map GlobalFunDef fdefs' ++ map GlobalDataDef ddefs
        inlined_mod = mod {moduleGlobals = gdefs'}

    -- Rename so that all inlined variables are unique
    runFreshVarM var_ids $ renameModule RenameLocals emptyRenaming inlined_mod
  where
    inline_defs var_ids fdefs =
      runFreshVarM var_ids $ do
        import_map <- makeImportsInlinable (moduleImports mod)
        runReaderT (inlDefGroupF fdefs $ return ()) import_map
