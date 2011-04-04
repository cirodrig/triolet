{-| Local continuation-passing transformation.

This transformation reorganizes local functions in a way that increases the
number of functions that can be translated to local procedures, which execute
more efficiently than hoisted functions.

The program should be lambda-converted before running the transformation.
LCPS creates non-minimal definition groups, so DCE should be run afterwards to
simplify the definition groups.

The transformation is described in the paper
\"Optimizing Nested Loops Using Local CPS Conversion\" by John Reppy,
in Proc. Higher-Order and Symbolic Computation 15, p. 161-180, 2002.
-}

module LowLevel.LocalCPS(localContinuationPassingConversion, lcpsModule)
where

import Prelude hiding(mapM)

import Control.Applicative hiding(empty)
import Control.Monad hiding(mapM, forM, join)
import Data.Traversable
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Maybe
import Data.Monoid
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import LowLevel.CodeTypes
import LowLevel.FreshVar
import LowLevel.Print
import LowLevel.Syntax
import Globals

-- | The set of return continuations of a function.
--
--   If the set contains zero or one values, we represent it precisely.
--   Larger sets are rounded up to 'Top'.
data RCont = Bottom | RCont !Var | Top
           deriving (Eq, Ord, Show)

-- | A value supporting join semi-lattice operations.
class Lattice a where
  bottom :: a
  join :: a -> a -> a

joinList :: Lattice a => [a] -> a
joinList xs = foldr join bottom xs

instance Lattice RCont where
  bottom = Bottom
  join Bottom x = x
  join x Bottom = x
  join (RCont v1) (RCont v2) = if v1 == v2 then RCont v1 else Top
  join _ _ = Top

instance Lattice a => Lattice (IntMap.IntMap a) where
  bottom = IntMap.empty
  join x y = IntMap.unionWith join x y

-- | A mapping from variable to return continuation.
type RConts = IntMap.IntMap RCont

singletonRConts :: Var -> RCont -> RConts
singletonRConts v rc = IntMap.singleton (fromIdent $ varID v) rc

-- | Look up the return continuation assigned to the given variable.
--   If not in the map, then no continuations (bottom) have been assigned.
lookupCont :: Var -> RConts -> RCont
lookupCont v m = fromMaybe bottom $ IntMap.lookup (fromIdent $ varID v) m

-------------------------------------------------------------------------------

-- | A LCPS Statement.  This is like 'Stm' except that let-expressions are
--   annotated with a variable.  The variable stands for the body of the
--   let-expression; if the body is turned into a function, then that variable
--   becomes the function's name.
data LStm =
    LetLCPS [ParamVar] Atom !Var LStm
  | LetrecLCPS !(Group LFunDef) LStm
  | SwitchLCPS Val [LAlt]
  | ReturnLCPS Atom

type LAlt = (Lit, LStm)
type LFunDef = Def LFun
type LFun = FunBase LStm

-- | Is the variable the name of a let-statement continuation from inside the
--   given expression?
containsLetContinuation :: LStm -> Var -> Bool
stm `containsLetContinuation` search_v = search stm
  where
    search (LetLCPS _ _ v s) = search_v == v || search s
    search (LetrecLCPS grp s) = any search_fun (groupMembers grp) || search s
    search (SwitchLCPS _ alts) = any (search . snd) alts
    search (ReturnLCPS _) = False
    
    search_fun (Def _ f) = search $ funBody f

annotateStm :: Stm -> FreshVarM LStm
annotateStm statement =
  case statement
  of LetE params rhs body -> do
       v <- newAnonymousVar (PrimType OwnedType)
       body' <- annotateStm body
       return $ LetLCPS params rhs v body'
     LetrecE defs body ->
       LetrecLCPS <$> traverse do_fundef defs <*> annotateStm body
     SwitchE scr alts ->
       SwitchLCPS scr <$> traverse do_alt alts
     ReturnE atom -> pure $ ReturnLCPS atom
  where
    do_fundef (Def v f) = Def v <$> annotateFun f
    do_alt (k, stm) = (,) k <$> annotateStm stm

annotateFun :: Fun -> FreshVarM LFun
annotateFun f = changeFunBodyM annotateStm f

unAnnotate :: LStm -> Stm
unAnnotate statement =
  case statement
  of LetLCPS params rhs _ body -> LetE params rhs (unAnnotate body)
     LetrecLCPS defs body -> LetrecE (fmap do_def defs) (unAnnotate body)
     SwitchLCPS scr alts -> SwitchE scr (map do_alt alts)
     ReturnLCPS atom -> ReturnE atom
  where
    do_def (Def v f) = Def v (unAnnotateFun f)
    do_alt (k, stm) = (k, unAnnotate stm)

unAnnotateFun :: LFun -> Fun
unAnnotateFun = changeFunBody unAnnotate

pprLStm :: LStm -> Doc
pprLStm stmt = pprLabeledLStm empty stmt

-- | Pretty-print a statement, preceded by a label.  This code is a modified
--   version of 'pprStm'.
pprLabeledLStm :: Doc -> LStm -> Doc
pprLabeledLStm label stmt =
  case stmt
  of LetLCPS [] atom v body ->
       label <+> text "[] <-" <+> pprAtom atom $$
       pprLabeledLStm (pprVar v <+> text ":") body
     LetLCPS vars atom v body ->
       let binder = sep $ punctuate (text ",") $ map pprVarLong vars
           rhs = pprAtom atom
       in hang (label <+> binder <+> text "<-") 8 rhs $$
          pprLabeledLStm (pprVar v <+> text ":") body
     LetrecLCPS defs body ->
       label <+> text "let" <+> pprGroup pprLFunDef defs $$
       pprLStm body
     SwitchLCPS val alts ->
       label <+> text "switch" <> parens (pprVal val) $$
       nest 2 (vcat $ map print_alt alts)
     ReturnLCPS atom -> label <+> pprAtom atom
  where
    print_alt (lit, body) = hang (pprLit lit <> text ":") 6 (pprLStm body)

-- | Pretty-print a function definition.  This code is a modified
--   version of 'pprFunDef'.
pprLFunDef :: Def LFun -> Doc
pprLFunDef (Def v f) =
  let intro = if isPrimFun f then text "procedure" else text "function"
      uses = case funUses f
             of ZeroUses -> text "[0]"
                OneUse -> text "[1]"
                ManyUses -> empty
      inl = if funInlineRequest f then text "INLINE" else empty
      param_doc = map pprVarLong $ funParams f
      ret_doc = map pprValueType $ funReturnTypes f
      leader = pprVar v <> pprFunSignature param_doc ret_doc
      local_doc = if funFrameSize f == 0
                  then empty
                  else text "frame size:" <+> text (show $ funFrameSize f)
  in intro <+> uses <+> inl <+> leader <+> text "=" $$
     nest 4 local_doc $$
     nest 4 (pprLStm (funBody f))


-------------------------------------------------------------------------------
-- Scanning to identify LCPS candidates.  A scan computes return continuations
-- of local functions.

-- | The set of local functions, and their arities.
--   Only local functions are considered for the local CPS transformation;
--   other variables are ignored.  To be CPS-transformed, a function has to
--   be called with the right number of arguments.
type Relevant = IntMap.IntMap Int

-- | A scan to identify LCPS candidates.
--   The parameters are the set of local functions and the current statement's 
--   return continuation.
newtype Scan = Scan {runScan :: Relevant -> RCont -> RConts}

instance Monoid Scan where
  mempty = Scan (\_ _ -> bottom)
  mappend (Scan f1) (Scan f2) = Scan (\r c -> f1 r c `join` f2 r c)

addRelevant :: Var -> Int -> Scan -> Scan
addRelevant v a (Scan f) =
  Scan $ \r -> f (IntMap.insert (fromIdent $ varID v) a r)

addRelevants :: [(Var, Int)] -> Scan -> Scan
addRelevants vs s = foldr (uncurry addRelevant) s vs

-- | Set the return continuation of the scanned code.  The return continuation
--   is what executes after the scanned code finishes executing.
setCont :: RCont -> Scan -> Scan
setCont rc (Scan f) = Scan (\r _ -> f r rc)

-- | Record the variable's return continuation.
--
--   If the variable is not a candidate for transformation, nothing happens.
tellRCont :: Var -> RCont -> Scan
tellRCont v c = Scan $ \relevant _ ->
  if fromIdent (varID v) `IntMap.member` relevant
  then singletonRConts v c
  else IntMap.empty

-- | The variable was called with some arguments.
--
--   If the variable is not a candidate for transformation, nothing happens.
--
--   If it's a saturated call of a known function, then record the current
--   return continuation as the variable's return continuation.
--
--   If it's an under- or oversaturated call, then the function's return
--   continuation becomes unknown.
tellCurrentRCont :: Var -> Int -> Scan
tellCurrentRCont v n_args = Scan $ \relevant rc ->
  case IntMap.lookup (fromIdent $ varID v) relevant
  of Nothing -> IntMap.empty
     Just arity | arity == n_args -> singletonRConts v rc
                | otherwise       -> singletonRConts v Top

scanValue :: Val -> Scan
scanValue value =
  case value
  of VarV v -> tellRCont v Top  -- Variable has unknown return continuation
     LitV _ -> mempty
     RecV _ vs -> scanValues vs
     LamV _ -> internalError "scanValue: Unexpected lambda"

scanValues vs = mconcat $ map scanValue vs

scanAtom :: Atom -> Scan
scanAtom atom =
  case atom
  of ValA vs -> scanValues vs
     CallA _ (VarV callee) vs ->
       -- The callee is called with the current return continuation
       tellCurrentRCont callee (length vs) `mappend`
       scanValues vs
     CallA _ v vs ->
       scanValues (v:vs)
     PrimA _ vs -> scanValues vs
     PackA _ vs -> scanValues vs
     UnpackA _ v -> scanValue v

scanDefGroup :: Group (Def LFun) -> Scan -> Scan
scanDefGroup group scan_body = Scan $ \relevant rcont ->
  let -- Scan the body to find calls of local functions
      body_conts = runScan (in_scope scan_body) relevant rcont
      
      -- Scan each function, using its return continuation in the body
      fun_conts =
        joinList [runScan (in_scope $ scan_fun f) relevant
                  (lookupCont v body_conts) | Def v f <- groupMembers group]
  in join body_conts fun_conts
  where
    -- Names and arities of functions in the definition group
    arities :: [(Var, Int)]
    arities = [(definiendum def, length $ funParams $ definiens def)
              | def <- groupMembers group]
    in_scope scan = addRelevants arities scan
    scan_fun f = scanStm $ funBody f

scanStm :: LStm -> Scan
scanStm statement =
  case statement
  of LetLCPS params rhs v body ->
       setCont (RCont v) (scanAtom rhs) `mappend` scanStm body
     LetrecLCPS defs body ->
       scanDefGroup defs $ scanStm body
     SwitchLCPS scr alts ->
       scanValue scr `mappend` mconcat [scanStm s | (_, s) <- alts]
     ReturnLCPS atom ->
       scanAtom atom

-------------------------------------------------------------------------------
-- The LCPS transformation.

data LCPSContext =
  LCPSContext
  { -- | The set of definition groups that are sunk by an LCPS transformation
    --   and could be placed in the code that's being processed.
    --   They are stored in a map, indexed by the return continuation.
    --   The return continuation also tells us where the groups should be
    --   moved to.
    --
    --   When a group is inserted in its destination location, it is
    --   transformed using the context of where the group /originated/ and
    --   the return type of where the group was placed.  The original
    --   context is saved with the group for that purpose.
    sunkenGroups :: IntMap.IntMap [(LCPSContext, Group (Def LFun))]

    -- | The set of return continuations identified for each local function
  , analysisReturnContinuations :: !RConts

    -- | The return continuation that will be applied to each in-scope local
    --   function during transformation.  A function is in this map iff it 
    --   is in scope and will be given a return continuation.
    --
    --   If the mapping contains an assignment @f |-> v@, then the analysis 
    --   map contains an agreeing assignment @f |-> RCont v@.
  , transformationReturnContinuations :: IntMap.IntMap Var

    -- | The return continuation of the current statement, if it's being
    --   transformed; Nothing otherwise.
  , currentReturnContinuation :: Maybe Var
    
    -- | The post-LCPS return type of the current function.  If the current
    --   function isn't being CPS-transformed, this is the same as
    --   'originalReturnTypes'.
  , currentReturnTypes :: [ValueType]
    
    -- | The original return type of the current function, before LCPS.
    --   This is used when inserting a continuation call /after/ a tail call;
    --   the original return types tell us the old tail call's return types.
  , originalReturnTypes :: [ValueType]
  }

insertSunkenGroup v defs ctx =
  ctx {sunkenGroups = IntMap.insertWith (++) var_id [(ctx, defs)] $
                      sunkenGroups ctx}
  where
    var_id = fromIdent $ varID v

deleteSunkenGroup v ctx =
  ctx {sunkenGroups = IntMap.delete (fromIdent $ varID v) $ sunkenGroups ctx}

-- | If the group should be LCPS-transformed, return the group's return
--   continuation and add the continuation to the context.
--   Otherwise return Nothing and leave the context unchanged.
chooseLcpsCont :: LCPSContext
               -> Group (Def LFun) -- ^ The definition group under consideration
               -> LStm             -- ^ The body of the definition group
               -> (Maybe Var, LCPSContext)
chooseLcpsCont ctx grp body =
  let continuations = [lookupCont v (analysisReturnContinuations ctx)
                      | Def v _ <- groupMembers grp]
      -- Do all functions in the group have the same continuation?
      all_same = let (c:cs) = continuations in all (c ==) cs
  in case continuations
     of RCont cont_var : _
          -- To be LCPS-transformed, all return continuations must be the same.
          --
          -- FIXME: This potentially captures variables, but we don't handle
          -- variable capture at all, leading to errors in closure conversion!
          -- tree.
          --
          -- We used to have this more restrictive test, but it turns many
          -- many proper tail-calls into non-tail calls.
          --
          -- > all_same && body `containsLetContinuation` cont_var
          | all_same ->
              (Just cont_var, assign_cont cont_var ctx)
        _ : _ -> (Nothing, ctx)
        [] -> internalError "chooseLcpsCont: Empty definition group"
  where
    -- Map each function in the group to the continuation variable
    assign_cont cont_var ctx =
      let ins m = foldr (uncurry IntMap.insert) m
                  [(fromIdent $ varID v, cont_var) | Def v _ <- groupMembers grp]
      in ctx {transformationReturnContinuations =
                 ins $ transformationReturnContinuations ctx}

-- | Look up the return continuation that is assigned to the variable.
--   If 'Nothing' is returned, no return continuation is assigned.
lookupTransformationCont :: Var -> LCPSContext -> Maybe Var
lookupTransformationCont v ctx =
  IntMap.lookup (fromIdent $ varID v) $ transformationReturnContinuations ctx

setReturnContinuation :: Maybe Var -> LCPSContext -> LCPSContext
setReturnContinuation mv ctx = ctx {currentReturnContinuation = mv}

setReturnTypes :: [ValueType] -> [ValueType] -> LCPSContext -> LCPSContext
setReturnTypes orig_return_types new_return_types ctx =
  ctx {currentReturnTypes = new_return_types,
       originalReturnTypes = orig_return_types}

-- | Perform local CPS transformation on the functions in a definition group
--   with the given continuation.
--
--   If a continuation variable and return types are given, then
--   the function is changed to call the continuation, which returns the
--   specified return types.
lcpsGroup :: LCPSContext -> Maybe (Var, [ValueType]) -> Group (Def LFun)
          -> FreshVarM (Group FunDef)
lcpsGroup ctx return_cont grp = mapM lcps_def grp
  where
    group_ctx = setReturnContinuation (fmap fst return_cont) ctx
    lcps_def (Def v f) =
      case return_cont
      of Nothing -> Def v `liftM` lcpsFun group_ctx f
         Just (rcont, rtypes) -> Def v `liftM` lcpsContFun group_ctx rtypes f

-- | Perform local CPS on the body of a function.
--   The function itself is not CPS-transformed.
lcpsFun :: LCPSContext -> LFun -> FreshVarM Fun
lcpsFun ctx f = do
  let local_ctx = setReturnTypes (funReturnTypes f) (funReturnTypes f) ctx
  fun_body <- lcpsStm local_ctx $ funBody f
  return $ f {funBody = fun_body}

-- | Perform local CPS on a function.  The function's continuation and return
--   types are changed by the transformation.
lcpsContFun :: LCPSContext -> [ValueType] -> LFun -> FreshVarM Fun
lcpsContFun ctx return_types f = do
  let local_ctx = setReturnTypes (funReturnTypes f) return_types ctx
  fun_body <- lcpsStm local_ctx $ funBody f
  return $ f {funBody = fun_body, funReturnTypes = return_types}

-- | Perform local CPS transformation on a statement.
--
--   If the statement is a 'let', check to see if a definition group should
--   be inserted here.
--   If the statement is a 'letrec', check to see if it should be moved.
--   For other statements, transform subexpressions recursively. 
lcpsStm :: LCPSContext -> LStm -> FreshVarM Stm
lcpsStm ctx statement =
  case statement
  of LetLCPS params rhs v body ->
       case IntMap.lookup (fromIdent $ varID v) $ sunkenGroups ctx
       of Nothing -> do
            body' <- lcpsStm ctx body
            return $ LetE params rhs body'
          Just groups -> do
            let ctx' = deleteSunkenGroup v ctx -- Not necessary, but reduces size of map
                return_types = currentReturnTypes ctx'

            -- Transform the functions in the definition group.
            -- If there are multiple groups, merge them into one group.
            let transform_group (grp_ctx, grp) =
                  lcpsGroup grp_ctx (Just (v, return_types)) grp

            grp' <- do groups' <- mapM transform_group groups
                       case groups' of
                         [grp] -> return grp
                         _ -> return $ Rec $ concatMap groupMembers groups'
            
            -- The body of the 'let' becomes a continuation function
            -- and is inserted into the group
            let cont = mkFun ClosureCall False 0 params return_types body
            cont' <- lcpsFun ctx' cont
            let ext_grp = Rec (Def v cont' : groupMembers grp')

            -- Generate a letrec.  The RHS of the 'let' becomes the new
            -- letrec body.  The RHS is a function call to one of the local
            -- functions.
            return $ LetrecE ext_grp $ ReturnE rhs

     LetrecLCPS defs body ->
       let (group_cont, ctx') = chooseLcpsCont ctx defs body
       in case group_cont
          of Just v | Just v /= currentReturnContinuation ctx ->
               -- This definition group should be moved
               let ctx'' = insertSunkenGroup v defs ctx'
               in lcpsStm ctx'' body
             _ -> do
               -- This definition group should not be moved.  Either it's
               -- already in the right context for its continuation, or it
               -- isn't being LCPS-transformed.
               let cont_types =
                     case group_cont
                     of Nothing -> Nothing
                        Just v  -> Just (v, currentReturnTypes ctx')
               defs' <- lcpsGroup ctx' cont_types defs
               body' <- lcpsStm ctx' body
               return $ LetrecE defs' body'

     SwitchLCPS scr alts -> do
       alts' <- forM alts $ \(l, s) -> do
         s' <- lcpsStm ctx s
         return (l, s')
       return $ SwitchE scr alts'
     
     ReturnLCPS atom ->
       case currentReturnContinuation ctx
       of Nothing -> return $ ReturnE atom
          Just rc ->
            -- This is the end of a LCPS-transformed block.
            -- If this is a call to an LCPS-transformed function with the
            -- same continuation, it's fine.
            -- Otherwise, call the continuation function.
            case atom
            of CallA cc (VarV callee) args
                 | lookupTransformationCont callee ctx == Just rc ->
                   return $ ReturnE atom
               _ -> do
                 -- Create temporary variables to hold the atom's result
                 return_vars <- mapM newAnonymousVar $ originalReturnTypes ctx
                 return $
                   LetE return_vars atom $
                   ReturnE (closureCallA (VarV rc) (map VarV return_vars))

-------------------------------------------------------------------------------
-- Entry point of module                   

-- | Perform local CPS on a top-level function definition.
localContinuationPassingConversion :: FunDef -> FreshVarM FunDef
localContinuationPassingConversion (Def global_name global_fun) = do
  -- Setup and analysis
  annotated_fun <- annotateFun global_fun
  let return_continuations =
        runScan (scanStm $ funBody annotated_fun) IntMap.empty Top
  
  -- Transformation
  let transform_ctx =
        LCPSContext { sunkenGroups = IntMap.empty
                    , analysisReturnContinuations = return_continuations
                    , transformationReturnContinuations = IntMap.empty
                    , currentReturnContinuation = Nothing
                    , currentReturnTypes = undefined_return
                    , originalReturnTypes = undefined_return}
  transformed_fun <- lcpsFun transform_ctx annotated_fun

  return $ Def global_name transformed_fun
  where
    undefined_return =
      internalError "localContinuationPassingConversion: Return types are undefined"

lcpsGlobalDefGroup :: Group GlobalDef -> FreshVarM (Group GlobalDef)
lcpsGlobalDefGroup group = mapM lcps_def group
  where
    -- Data definitions are unchanged
    lcps_def def@(GlobalDataDef _) = return def
    
    -- Transform function definitions
    lcps_def (GlobalFunDef fdef) =
      GlobalFunDef `liftM` localContinuationPassingConversion fdef

-- | Perform local CPS on an entire module.
lcpsModule :: Module -> IO Module
lcpsModule mod =
  withTheLLVarIdentSupply $ \var_ids -> do
    global_defs <- runFreshVarM var_ids $
                   mapM lcpsGlobalDefGroup $ moduleGlobals mod
    return $ mod {moduleGlobals = global_defs}