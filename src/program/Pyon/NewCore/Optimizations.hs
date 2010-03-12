
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Pyon.NewCore.Optimizations
       (evaluate, flattenApplications, inline)
where

import Control.Monad
import Control.Monad.Reader
import Data.Graph.Inductive.Graph as Graph
import Data.Graph.Inductive.PatriciaTree as Graph
import Data.Graph.Inductive.Query.DFS as Graph
import Data.List
import Data.Monoid
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set(Set)
import qualified Data.Set as Set

import Gluon.Common.Error
import Gluon.Common.Supply
import Gluon.Core
import Gluon.Eval.Environment
import Gluon.Eval.Eval
import Pyon.Globals
import Pyon.NewCore.Syntax
import Pyon.NewCore.Rename
  
-- | Evaluate Gluon code in a module.
evaluate :: Module Core -> IO (Module Core)
evaluate (Module defs) =
  withTheVarIdentSupply $ \ident ->
  case runEval ident $ mapM evalDef defs
  of Nothing -> fail "Evaluation failed"
     Just defs' -> return $ Module defs'

evalExp :: Exp Core -> Eval (Exp Core)
evalExp expression = liftM whnfExp $ evalFully' expression

evalVal :: Val Core -> Eval (Val Core)
evalVal = traverseVal evalVal evalStm evalExp

evalStm :: Stm Core -> Eval (Stm Core)
evalStm = traverseStm evalVal evalStm evalExp

evalDef :: Def Core -> Eval (Def Core)
evalDef = traverseDef evalVal evalStm evalExp

-- | Search for nested application terms ('AppV' or 'AppE') and convert them
-- to non-nested applications.
flattenApplications :: Module Core -> Module Core
flattenApplications (Module defs) = Module $ map faDef defs

faExp :: Exp Core -> Exp Core
faExp expression =
  case expression
  of AppE {expInfo = inf, expOper = op, expArgs = args} ->
       -- Flatten operator before inspecting it
       case faExp op
       of AppE {expOper = op', expArgs = args'} ->
            -- Flatten this expression.  Combine the argument lists.
            AppE {expInfo = inf, expOper = op', expArgs = args' ++ args}
          _ -> flattenSubexpressions
     _ -> flattenSubexpressions
  where
    flattenSubexpressions =
      mapExp faExp flattenTuple flattenSum expression
    flattenTuple = mapTuple faExp flattenTuple
    flattenSum = mapSum faExp flattenSum

-- | Flatten a value.
-- Note that we check for both Gluon application terms and Pyon application 
-- terms.
faVal :: Val Core -> Val Core
faVal value =
  case value
  of AppV {valInfo = inf, valOper = op, valArgs = args} ->
       -- Flatten operator first 
       case faVal op
       of GluonV {valGluonTerm = AppE {expOper = op', expArgs = args'}} ->
            -- If possible, convert all terms to Gluon expressions.
            -- Either way, flatten arguments.
            case mapM valToMaybeExp args
            of Just gluon_args ->
                 let new_args = map faExp $ args' ++ gluon_args
                 in GluonV { valInfo = inf
                           , valGluonTerm = AppE { expInfo = inf
                                                 , expOper = op'
                                                 , expArgs = new_args}}
               Nothing ->
                 let new_args = map (expToVal . faExp) args' ++
                                map faVal args
                 in AppV { valInfo = inf
                         , valOper = expToVal op'
                         , valArgs = new_args
                         }
          AppV {valOper = op', valArgs = args'} ->
            let new_args = map faVal $ args' ++ args
            in AppV {valInfo = inf, valOper = op', valArgs = new_args}
            
          -- Other terms can't be flattened
          _ -> flattenSubexpressions
     _ -> flattenSubexpressions
  where
    flattenSubexpressions = mapVal faVal faStm faExp value

faStm :: Stm Core -> Stm Core
faStm statement = mapStm faVal faStm faExp statement

faDef :: Def Core -> Def Core
faDef def = mapDef faVal faStm faExp def

-------------------------------------------------------------------------------

type GetMentions a = a -> Set Var

getMentionsBinder :: Binder Core () -> Set Var -> Set Var
getMentionsBinder (Binder v ty ()) s =
  mentionedInExp ty `Set.union` Set.delete v s

getMentionsBinder' :: Binder' Core () -> Set Var -> Set Var
getMentionsBinder' (Binder' mv ty ()) s =
  mentionedInExp ty `Set.union` maybe id Set.delete mv s

mentionedInExp :: GetMentions (Exp Core)
mentionedInExp expression =
  case expression
  of VarE {expVar = v} -> Set.singleton v
     ConE {} -> Set.empty
     LitE {} -> Set.empty
     AppE {expOper = op, expArgs = args} ->
       Set.unions $ map mentionedInExp (op : args)
     LamE {expParam = param, expBody = body} ->
       getMentionsBinder param $ mentionedInExp body
     FunE {expMParam = param, expRange = range} ->
       getMentionsBinder' param $ mentionedInExp range
     TupE {expFields = fs} -> mentionedInFields fs
     TupTyE {expTyFields = fs} -> mentionedInTyFields fs
  where
    mentionedInFields (Binder' mv ty val :&: rest) =
      mentionedInExp ty `Set.union`
      mentionedInExp val `Set.union`
      maybe id Set.delete mv (mentionedInFields rest)
    mentionedInFields Nil = Set.empty

    mentionedInTyFields (param :*: rest) =
      getMentionsBinder' param $ mentionedInTyFields rest
    mentionedInTyFields Unit = Set.empty

mentionedInVal :: GetMentions (Val Core)
mentionedInVal value =
  case value
  of GluonV {valGluonTerm = ty} -> mentionedInExp ty
     AppV {valOper = op, valArgs = args} ->
       Set.unions $ map mentionedInVal (op : args)
     ALamV {valAFun = sf} -> mentionedInActionFun sf
     SLamV {valSFun = sf} -> mentionedInStreamFun sf
     SDoV {valStm = stm} -> mentionedInStm stm

mentionedInStm :: GetMentions (Stm Core)
mentionedInStm statement =
  case statement
  of ReturnS {stmVal = val} -> mentionedInVal val
     CallS {stmVal = val} -> mentionedInVal val
     LetS {stmVar = mv, stmStm = rhs, stmBody = body} ->
       mentionedInStm rhs `Set.union`
       maybe id Set.delete mv (mentionedInStm body)
     LetrecS {stmDefs = defs, stmBody = body} ->
       let local_vars = Set.fromList $ map definiendum defs
           local_mentions =
             Set.unions (mentionedInStm body :
                         map (mentionedInDefiniens . definiens) defs)
       in local_mentions `Set.difference` local_vars
     CaseS {stmScrutinee = val, stmAlts = alts} ->
       Set.unions (mentionedInVal val : map mentionedInAlt alts)

mentionedInAlt (Alt _ pat body) =
  mentionedInStm body `Set.difference` Set.fromList (patternVariables pat)

mentionedInDefiniens (ActionFunDef f) = mentionedInActionFun f
mentionedInDefiniens (StreamFunDef f) = mentionedInStreamFun f

mentionedInActionFun f = foldr getMentionsBinder body $ funParams f
  where
    body = Set.unions [ mentionedInExp $ funReturnType f
                      , mentionedInExp $ funEffectType f
                      , mentionedInStm $ funBody f
                      ]
    
mentionedInStreamFun f = foldr getMentionsBinder body $ funParams f
  where
    body = Set.unions [ mentionedInExp $ funReturnType f
                      , mentionedInExp $ funEffectType f
                      , mentionedInVal $ funBody f
                      ]

-- Find SCCs in a definition group
sortDefGroup :: [Def Core] -> [[Def Core]]
sortDefGroup defgroup =
  let -- Map definienda to graph node IDs.
      -- ID is position in the original defgroup list.
      var_list = map definiendum defgroup
      var_assocs = zip var_list [0..]
      node_list = [(x, ()) | x <- [0..length defgroup - 1]]
      var_map = Map.fromList var_assocs
      
      -- There is an edge from X to Y iff Y is mentioned in X
      edges = [(x_id, y_id, ()) | def <- defgroup
                                , let x_id = var_map Map.! definiendum def
                                , y <- Set.toList $
                                       mentionedInDefiniens $
                                       definiens def
                                , y_id <- maybeToList $ Map.lookup y var_map
                                ]
      
      -- Build a graph
      gr = Graph.mkGraph node_list edges :: Graph.Gr () ()
      
      -- Find the SCCs.  We want the most-depended-on SCC to appear first.
      sccs = reverse $ Graph.scc gr
      
  in -- Create the new definition groups
     map (map (defgroup !!)) sccs

type Inl a = ReaderT (Map Var (Val Core)) Eval a

instance Supplies (ReaderT (Map Var (Val Core)) Eval) VarID where
  fresh = lift fresh

runInl supply m = runEval supply $ runReaderT m Map.empty

inline :: Module Core -> IO (Module Core)
inline mod = do
  mod' <- withTheVarIdentSupply $ \supply -> return $ runInl supply $ do
    let Module defs = mod
    (defs', _) <- inlineDefGroup False defs $ return ((), undefined)
    return $ Module (concat defs')
  case mod' of
    Nothing -> fail "Evaluation failed"
    Just m  -> return m

lookupName :: Var -> Inl (Maybe (Val Core))
lookupName v = asks (Map.lookup v)

withInlineFunctions :: [Def Core] -> Inl a -> Inl a
withInlineFunctions defs m = foldr withInlineFunction m defs

withInlineFunction :: Def Core -> Inl a -> Inl a
withInlineFunction (Def inf v f) = local $ Map.insert v (asValue f)
  where
    asValue (ActionFunDef f) = ALamV inf f
    asValue (StreamFunDef f) = SLamV inf f

withAssignment :: Var -> Val Core -> Inl a -> Inl a
withAssignment v value = local $ Map.insert v value

bindParameter :: Binder Core () -> Val Core -> Inl a -> Inl a
bindParameter (Binder v _ ()) value = withAssignment v value

bindParameters :: [(Binder Core (), Val Core)] -> Inl a -> Inl a
bindParameters xs m = foldr (uncurry bindParameter) m xs

inlineBinder :: Binder Core () -> Inl (Binder Core ())
inlineBinder (Binder v ty ()) = do
  ty' <- inlineExp' ty
  return $ Binder v ty' ()

inlineDefGroup :: Bool
               -> [Def Core]
               -> Inl (a, Set Var)
               -> Inl ([[Def Core]], a)
inlineDefGroup removeUnmentionedDefs defs doBody = do
  (defs, x, _) <- inlineLocally $ sortDefGroup defs
  return (defs, x)
  where
    inlineLocally (defgroup:defgroups) = do
      -- Inline into this definition group
      defgroup' <- mapM inlineDef defgroup
      
      -- Add definitions to the environment and process the rest
      (defgroups', body, mentions) <-
        withInlineFunctions defgroup' $ inlineLocally defgroups
        
      -- Remove functions that aren't mentioned somewhere
      let defgroup'' =
            if removeUnmentionedDefs
            then filter ((`Set.member` mentions) . definiendum) defgroup'
            else defgroup'

      -- Create the new definition group list
      let defgroups'' = if null defgroup''
                        then defgroups'
                        else defgroup'':defgroups'
      
      -- Compute the new mentions set
      let mentions' =
            if removeUnmentionedDefs
            then let localMentions =
                       Set.unions $ map (mentionedInDefiniens . definiens) defgroup''
                 in (localMentions `Set.union` mentions) `Set.difference`
                    Set.fromList (map definiendum defgroup'')
            else error "inlineDefGroup"
      
      return (defgroups'', body, mentions')
      
    inlineLocally [] = do
      (x, mentions) <- doBody
      return ([], x, mentions)

inlineDef :: Def Core -> Inl (Def Core)
inlineDef def =
  case definiens def
  of ActionFunDef f -> do f' <- inlineActionFun f
                          return $ def {definiens = ActionFunDef f'}
     StreamFunDef f -> do f' <- inlineStreamFun f
                          return $ def {definiens = StreamFunDef f'}

inlineActionFunDef fun = undefined

inlineActionCallVal :: SynInfo -> Val Core -> Inl (Stm Core)
inlineActionCallVal info value = evalActionCall info =<< inlineVal value
  
inlineVal value =
  case value
  of GluonV {valGluonTerm = exp} -> inlineExp exp 
     AppV {valOper = op, valArgs = args} -> do
       op' <- inlineVal op
       args' <- mapM inlineVal args
       return $ value {valOper = op', valArgs = args'}
     ALamV {valAFun = f} -> do
       f' <- inlineActionFun f
       return $ value {valAFun = f'}
     SLamV {valSFun = f} -> do
       f' <- inlineStreamFun f
       return $ value {valSFun = f'}
     SDoV {valStm = stm} -> do
       stm' <- inlineStm stm
       return $ value {valStm = stm'}

inlineExp exp =
  case exp
  of VarE {expVar = v} -> do
       val' <- lookupName v
       return $ fromMaybe (expToVal exp) val'
     AppE {expInfo = inf, expOper = op, expArgs = args} -> do
       op' <- inlineExp op
       args' <- mapM inlineExp args
       return $ AppV {valInfo = inf, valOper = op', valArgs = args'}
     _ -> liftM expToVal $ inlineExp' exp
     
inlineExp' :: Exp Core -> Inl (Exp Core)
inlineExp' exp =
  case exp
  of VarE {expVar = v} -> do
       val' <- lookupName v
       return $ maybe exp valToExp val'
     _ -> traverseExp inlineExp' inlineTuple inlineSum exp
  where
    inlineTuple = traverseTuple inlineExp' inlineTuple
    inlineSum = traverseSum inlineExp' inlineSum
  
inlineStm statement =
  case statement
  of ReturnS {stmVal = val} -> do
       val' <- inlineVal val
       return $ statement {stmVal = val'}
     CallS {stmInfo = inf, stmVal = val} -> inlineActionCallVal inf val
     LetS {stmInfo = inf, stmVar = mv, stmStm = stm, stmBody = body} -> do
       stm' <- inlineStm stm
       
       -- If the statement returns a value, we can inline the value
       case stm' of
         ReturnS {stmInfo = rhs_inf, stmVal = rhs_val} ->
           inlineLetBinding inf mv rhs_inf rhs_val body
         _ -> do body' <- inlineStm body
                 return $ statement {stmStm = stm', stmBody = body'}
     LetrecS {stmInfo = inf, stmDefs = defs, stmBody = body} -> do
       (defgroups, body') <- inlineDefGroup True defs $ do
         body' <- inlineStm body
         return (body', mentionedInStm body')
       return $ rebuildLetrec inf defgroups body'
     CaseS {stmScrutinee = v, stmAlts = alts} -> do
       v' <- inlineVal v
       -- If the scrutinee is a constructor application, then evaluate it now
       case v' of
         AppV { valOper = GluonV {valGluonTerm = ConE {expCon = c}}
              , valArgs = args} -> evalCase c args alts
         GluonV {valGluonTerm = AppE { expOper = ConE {expCon = c}
                                     , expArgs = args}} ->
           evalCase c (map expToVal args) alts
         _ -> do alts' <- mapM inlineAlt alts
                 return $ statement {stmScrutinee = v', stmAlts = alts'}
  where
    rebuildLetrec inf defgroups body = foldr make_letrec body defgroups
      where
        make_letrec g e = LetrecS {stmInfo = inf, stmDefs = g, stmBody = e}
    
    inlineAlt (Alt inf pat body) = do
      body' <- inlineStm body
      return $ Alt inf pat body'
      
    -- Inline a pure let binding's value into its body
    inlineLetBinding inf mv rhs_inf rhs_val body =
      case mv
      of Nothing -> 
           -- Let-bound value is dead code
           inlineStm body
         Just v -> do
           withAssignment v rhs_val $ inlineStm body

-- | Evaluate a 'case' expression for which the scrutinee has a known
-- constructor
evalCase con args alts =
  case find ((con ==) . patCon . altPat) alts
  of Just (Alt inf pat body) ->
       -- Substitute the constructor arguments for the case patterns
       assignParams (patParams pat) args $ inlineStm body
     Nothing ->
       internalError "No pattern matches constructor" 
  where
    assignParams (RigidP:params)      (_:args)   k =
      assignParams params args k
    assignParams (FlexibleP v:params) (arg:args) k =
      withAssignment v arg $ assignParams params args k
    assignParams []                   []         k =
      k

evalActionCall info val =
  case val
  of AppV {valOper = ALamV {valAFun = f}, valArgs = args} -> do
       when (length (funParams f) /= length args) $
         internalError "Cannot evaluate a partially applied function"
       
       -- Rename the function to avoid name collisions
       f_renamed <- freshenActionFunFully mempty f
       
       bindParameters (zip (funParams f_renamed) args) $ do
         -- Substitute arguments for parameters in function body
         new_expr <- inlineStm $ funBody f_renamed
         
         return new_expr
     
     _ -> return $ CallS info val

-- | Perform inlining in a function definition
inlineActionFun fun = do
  params <- mapM inlineBinder $ funParams fun
  ret_type <- inlineExp' $ funReturnType fun
  eff_type <- inlineExp' $ funEffectType fun
  body <- inlineStm $ funBody fun
  return $ Fun params ret_type eff_type body
  
-- | Perform inlining in a function definition
inlineStreamFun fun = do
  params <- mapM inlineBinder $ funParams fun
  ret_type <- inlineExp' $ funReturnType fun
  let eff_type = funEffectType fun -- Effect type is always 'empty'
  body <- inlineVal $ funBody fun
  return $ Fun params ret_type eff_type body

       