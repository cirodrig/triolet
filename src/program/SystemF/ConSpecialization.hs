{-| Constructor specialization.

* Purpose

When a function inspects one of its arguments in a case statement, and the
argument has a known constructor at the function's call site, we can
generate a specialized version of the function that contains just the relevant
case branch.  This transformation avoids building a data structure just to
inspect it.

A big benefit occurs when constructor specialization generates some functions
that have a single callsite.  Those functions can be inlined after
specialization.

* Problem breakdown

Constructor specialization performs a pass over the program to detect
specializable functions.  A function is judged to be specializable based on
the function's definition (it must follow a pattern that we know how to
specialize) and its uses (the function must be called in a way that tells
us how to specialize that call).  When a function is detected to be
specializable, an extra pass is performed to specialize calls of that
function.

Specialization decisions are encoded using 'DecisionTree's.
Each 'DecisionTree' node represents a @case@ statement for which we would
like to precompute which alternative will execute.  The act of
specializing consists of choosing a path from the root of a 'DecisionTree'
to one of its nodes, inlining that path into a callsite, and translating
the subtree starting at that tree node into a new function.

The points of primary interest in the code are:

1. 'functionDecisionTree', which converts a function to a decision tree.

2. 'recordCall', which records that part of a decision tree created by
   'functionDecisionTree' should be specialized.

3. 'decisionTreeFun', which specializes a function.  The output of
   this step is a set of specialized functions and a new decision tree.
   The new decision tree is used to specialize calls.

4. 'specializeCall', which uses the decision tree created by
   'decisionTreeFun' to specialize a function call.

A candidate function for specialization is encoded as a 'DecisionFun
Bool ExpM'.  The 'Bool' labels in the tree are initialized to 'False',
and changed to 'True' when that node is selected for specialization.

A function call is encoded as a 'CallPattern'.
-}

{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}
{-# OPTIONS_GHC -auto-all #-}
module SystemF.ConSpecialization(specializeOnConstructors)
where

import Prelude hiding(mapM)

import Control.Applicative
import Control.Monad hiding(forM, mapM)
import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Writer
import qualified Data.IntMap as IntMap
import Data.IORef
import qualified Data.List as List
import Data.Maybe
import Data.Monoid
import Data.Traversable
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Label
import Common.Supply
import SystemF.PrintMemoryIR
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.TypecheckMem
import qualified SystemF.Rename
import SystemF.Rename(substitutePatM, substitutePatMs)
import Type.Environment
import Type.Eval
import qualified Type.Substitute as Substitute
import Type.Substitute(Substitutable, substitute, freshen)
import Type.Type
import Type.Var
import Globals
import GlobalVar

-- | If set to 'True', print a message whenever specialization occurs
debuggingEnabled = False

debug doc x = if debuggingEnabled then traceShow doc x else x

-- | A function that has been translated into a decision tree.
--
--   The fields are derived from the fields of 'BaseFun'.
--   Unlike 'BaeFun', input parameters and output parameters are
--   stored separately.
data DecisionFun lab a =
  DecisionFun 
  { dfunInfo      :: ExpInfo
  , dfunTyParams  :: [TyPatM]
  , dfunParams    :: [PatM]
  , dfunOutParams :: [PatM]
  , dfunReturn    :: TypM
  , dfunBody      :: DecisionTree lab a
  }

isSingletonTree :: DecisionFun lab a -> Bool
isSingletonTree dfun = case dfunBody dfun
                       of Done _ -> True
                          _ -> False

-- | A decision tree.
data DecisionTree lab a =
    Case !Var [DecisionBranch lab a]
  | Done a

-- | A labeled branch of a decision tree.
data DecisionBranch lab a =
  DecisionBranch lab !DeConInst [PatM] (DecisionTree lab a)

branchTree :: DecisionBranch lab a -> DecisionTree lab a
branchTree (DecisionBranch _ _ _ t) = t

-- | The set of wanted specializations is a decision tree annotated with
--   booleans.  Nodes annotated with 'True' will be specialized.
type WantedSpecializations = DecisionFun Bool ExpM

type WantedSpecializationsMap = IntMap.IntMap (IORef WantedSpecializations)

-- | The specialization tree of a function.  Each node labeled with a
--   'Just' value is a specialized function.
type CreatedSpecializations = DecisionFun (Maybe Var) ()

type CreatedSpecializationsMap = IntMap.IntMap CreatedSpecializations

-- | A function call pattern consists of some type parameters,
--   some value parameters, and some output parameters.
--   Output parameters are saved separately because they are not changed 
--   by speicalization and they must remain at the end of the list.
--   end of the parameter list
data CallPattern = CallPattern [TypM] [CallPatternArg] [ExpM]

-- | A pattern of known values passed as arguments to a function call.
data CallPatternArg =
    ConArg !ConInst [CallPatternArg]
  | SomeArg ExpM

isSomeArg (SomeArg _) = True
isSomeArg _ = False

type CallPatternEnv = [(Var, CallPatternArg)]

-- | Keep track of values bound to some parameter variables.
--   Unbound variables are not assigned a value.
mkCallParamTable :: [PatM] -> [CallPatternArg] -> CallPatternEnv
mkCallParamTable patterns params =
  zip (map patMVar patterns) params

-- | The type variable and variable bindings that are in scope at a point 
--   in a decision tree.  These bindings come from the original function
--   and whatever additional bindings introduced by tree nodes.
--   Output parameters are not included in the binding context.
type BindingContext = ([TyPatM], [PatM])

-- | Decide whether the given value matches the decision branch.
--   If so, return the variable binding produced by matching the argument with
--   this branch.
matchBranch :: CallPatternArg
            -> DecisionBranch lab a
            -> Maybe (CallPatternEnv, BindingContext)
matchBranch arg_value branch@(DecisionBranch _ decon pats _) =
  case arg_value
  of ConArg con field_values
       | summarizeConstructor con == summarizeDeconstructor decon ->
           let env = mkCallParamTable pats field_values
               ctx = (map TyPatM (deConExTypes decon), pats)
           in Just (env, ctx)
     _ -> Nothing

-- | Find the first branch that satisfies the predicate @isJust . f@.
findBranch :: (DecisionBranch lab a -> Maybe b)
           -> [DecisionBranch lab a]
           -> Maybe (DecisionBranch lab a, b)
findBranch f (b:bs)
  | Just x <- f b = Just (b, x)
  | otherwise     = findBranch f bs

findBranch _ [] = Nothing

-- | Alter the branch that satisfies the predicate @isJust . f@.
alterBranch :: (DecisionBranch lab a -> Maybe (DecisionBranch lab a))
            -> [DecisionBranch lab a] -> Maybe [DecisionBranch lab a]
alterBranch f xs = go id f xs
   where
    go hd f (x:xs) =
      case f x
      of Nothing -> go (hd . (x:)) f xs
         Just x' -> Just $ hd (x' : xs)
        
    go _  _ [] = Nothing

-------------------------------------------------------------------------------
-- WantedSpecializations methods

-- | Determine whether any specializations were created
hasSpecializations :: WantedSpecializations -> Bool
hasSpecializations f = check $ dfunBody f
  where
    check (Done _) = False
    check (Case _ branches) = any check_branch branches

    check_branch (DecisionBranch label _ _ tree) = label || check tree

-- | Record that a function call was made.  There will be an attempt to 
--   specialize the function.
recordCall :: CallPattern -> WantedSpecializations -> WantedSpecializations
recordCall (CallPattern ty_args args out_args) f
  | length ty_args /= length (dfunTyParams f) = f
  | otherwise =
      let table = mkCallParamTable (dfunParams f) args
      in case record_tree table $ dfunBody f
         of Nothing -> f
            Just body' -> f {dfunBody = body'}
  where
    record_tree param_table tree =
      case tree
      of Done _ -> Nothing
         Case v branches -> do
           -- Determine the data constructor 'v' will have 
           arg <- lookup v param_table
  
           -- Replace the matching case branch
           let alter_branch branch
                 | Just (local_bindings, _) <- matchBranch arg branch = do
                     let param_table' = local_bindings ++ param_table
                     Just $ record_branch param_table branch
                 | otherwise = Nothing
                     
           branches' <- alterBranch alter_branch branches
           return $ Case v branches'

    record_branch param_table (DecisionBranch label decon params subtree) =
      -- First, try to update a subtree.  If that fails, then update this
      -- branch by labeling it 'True'.
      case record_tree param_table subtree
      of Just subtree' -> DecisionBranch label decon params subtree'
         Nothing       -> DecisionBranch True decon params subtree

-- | Convert a function to a decision tree
functionDecisionTree :: TypeEnv -> FunM -> WantedSpecializations
functionDecisionTree tenv (FunM (Fun inf ty_params params ret body)) =
  DecisionFun inf ty_params in_params out_params ret $
  expToDecisionTree tenv body
  where
    (in_params, out_params) = partitionParameters local_tenv params

    -- Add the function's type parameters to the type environment
    local_tenv = foldr insert_typaram_type tenv ty_params
      where
        insert_typaram_type (TyPatM (a ::: k)) type_env = 
          insertType a k type_env

expToDecisionTree tenv exp =
  case exp
  of ExpM (CaseE inf (ExpM (VarE _ v)) alts)
       | not_single_constructor_type alts ->
           -- Case-of-variable gets transformed into decisions
           Case v $ map (altToDecisionBranch tenv) alts
     _ -> Done exp
  where
    -- If there are two or more alternatives, this type certainly has more than
    -- one data constructor
    not_single_constructor_type (_ : _ : _) = True
    
    -- If there's only one alternative, count the number of data constructors
    -- that the data type has
    not_single_constructor_type [AltM alt] =
      case fromDeCInstM $ altCon alt
      of VarDeCon con _ _ ->
           case lookupDataConWithType con tenv
           of Just (dtype, _) ->
                length (dataTypeDataConstructors dtype) /= 1
              Nothing ->
                internalError "expToDecisionTree"
         TupleDeCon _ -> False  -- Tuples have one data constructor

altToDecisionBranch tenv (AltM (Alt (DeCInstM decon) params body)) =
  DecisionBranch False decon params $ expToDecisionTree tenv body

-- | Convert an annotated decision tree to a function.
--
--   Each branch of the decision tree that was labeled with a variable 
--   will be extracted as a new function.  A list of extracted function
--   definitions is returned.  A decision tree is returned for
--   deciding how to specialize a function call.
decisionTreeFun :: EvalMonad m =>
                   Maybe Label -> DefAnn -> WantedSpecializations
                -> m (FunM, CreatedSpecializations, [Def Mem])
decisionTreeFun mlabel annotation dfun = do
  let DecisionFun inf ty_params in_params out_params ret body = dfun 
      properties = (mlabel, annotation, inf, ret)
      bindings = (ty_params, in_params)
  ((body', specializations), defs) <-
    runWriterT $ decisionTreeToExp properties bindings out_params body
  return (FunM (Fun inf ty_params (in_params ++ out_params) ret body'),
          DecisionFun inf ty_params in_params out_params ret specializations,
          defs)

decisionTreeToExp properties bindings out_params (Case v branches) = do
  (branch_code, branch_tree) <-
    mapAndUnzipM (decisionBranchToAlt properties bindings out_params) branches
  let case_expression =
        ExpM $ CaseE defaultExpInfo (ExpM (VarE defaultExpInfo v)) branch_code
  return (case_expression, Case v branch_tree)

decisionTreeToExp _ _ _ (Done e) =
  return (e, Done ())

-- | Convert a branch of a decision tree to a case alternative.
--
--   If the branch is marked for specialization, it will be extracted to a
--   new function.
decisionBranchToAlt properties bindings out_params branch = do
  (alt_body, alt_body_tree) <-
    decisionTreeToExp properties local_bindings out_params tree
  (code, label) <-
    if create_function
    then make_function alt_body
    else return (alt_body, Nothing)
  let alt = AltM (Alt (DeCInstM decon) params code)
      new_branch = DecisionBranch label decon params alt_body_tree
  return (alt, new_branch)
  where
    DecisionBranch create_function decon params tree = branch
    local_bindings =
      (map TyPatM (deConExTypes decon), params) `mappend` bindings
    (mlabel, annotation, function_inf, return_type) = properties

    -- Create a new function with 'alt_body' as its function body
    make_function alt_body = do
      subfunction_name <- lift $ newVar mlabel ObjectLevel

      let (ty_params, in_params) = local_bindings
          subfunction =
            FunM (Fun function_inf ty_params (in_params ++ out_params) return_type alt_body)
          definition =
            Def subfunction_name annotation subfunction

          -- Construct a function call to the new function
          call = specializedCallExp defaultExpInfo subfunction_name
                 local_bindings out_params

      tell [definition]
      return (call, Just subfunction_name)

-------------------------------------------------------------------------------

-- | Create a call to a specialized function.  Only a function call is
--   created.
specializedCallExp :: ExpInfo -> Var -> BindingContext -> [PatM] -> ExpM
specializedCallExp inf fname (ty_params, in_params) out_params =
  appE inf (ExpM $ VarE inf fname) ty_args args
  where
    ty_args = [TypM (VarT v) | TyPatM (v ::: _) <- ty_params]
    args = [ExpM $ VarE defaultExpInfo (patMVar p)
           | p <- in_params ++ out_params]

-- | Create a specialized function call based on the call pattern.
specializeCall :: EvalMonad m =>
                  CallPattern -> CreatedSpecializations -> m (Maybe ExpM)
specializeCall (CallPattern ty_args in_args out_args) f
  | length ty_args /= length (dfunTyParams f) = return Nothing
  | Just body_exp <- specialized_expression = do
      let -- Substitute types in the reconstructed expression
          type_subst = Substitute.fromList
                       [(a, t) | (TyPatM (a ::: _), TypM t) <-
                                   zip (dfunTyParams f) ty_args]
          subst = SystemF.Rename.Subst type_subst SystemF.Rename.emptyV
          
      -- Bind pattern variables to value arguments
      rtype <- substitute type_subst $ dfunReturn f
      let args = map callPatternArgExp in_args ++ out_args
      exp <- bindSpecializedCallPattern
             subst rtype (dfunParams f ++ dfunOutParams f) args body_exp
      return $ Just exp
  | otherwise =
      -- There is no specialization for this pattern
      return Nothing
  where
    
    -- Create a specialized expression
    specialized_expression =
      specializeFromDecisionTree param_table binding_context
      (dfunOutParams f) (dfunBody f)
      where
        param_table = mkCallParamTable (dfunParams f) in_args
        binding_context = (dfunTyParams f, dfunParams f)

-- | Create a specialized function call.  Apply the substitution to the
--   parameters and the expression, but not the arguments or return type.
bindSpecializedCallPattern
  subst return_type (param:params) (arg:args) e =

  -- Rename the parameter
  substitutePatM subst param $ \subst' param' -> do
    let param'' = setPatMDmd unknownDmd param'

    -- Bind remaining parameters
    e' <- bindSpecializedCallPattern subst' return_type params args e

    -- Create a 'let' expression
    return $ ExpM $ LetE defaultExpInfo param'' arg e'
    
bindSpecializedCallPattern subst return_type [] args e = do
  -- There are excess arguments, or an equal number of parameters and
  -- arguments.  Create a function call expression with the excess arguments.
  e' <- substitute subst e
  return $ appE defaultExpInfo e' [] args

bindSpecializedCallPattern subst return_type params [] e = do
  -- There are excess parameters.  Create a lambda expression.
  substitutePatMs subst params $ \subst' params' -> do
    e' <- substitute subst' e
    let lambda_fun = FunM $ Fun { funInfo = defaultExpInfo
                                , funTyParams = []
                                , funParams = params'
                                , funReturn = return_type
                                , funBody = e'}
    return $ ExpM $ LamE defaultExpInfo lambda_fun

-- | Given a decision tree and call pattern, create a specialized
--   function call.  The function call contains one path through the
--   decision tree, ending with a call to the specialized function.
--
--   This function only uses the environment to prune the decision tree. 
--   Values from the environment are not substituted.
--
--   This function always generates a fully applied function call. 
--   The correct number of output arguments must be given.
--   If the number of arguments doesn't match the number of function
--   parameters, that must be fixed up elsewhere.
specializeFromDecisionTree :: CallPatternEnv
                           -> BindingContext
                           -> [PatM]
                           -> DecisionTree (Maybe Var) ()
                           -> Maybe ExpM
specializeFromDecisionTree _ _ _ (Done _) = Nothing

specializeFromDecisionTree bindings binding_ctx out_params (Case v branches) = do
  -- Determine the data constructor 'v' will have 
  arg <- lookup v bindings
  
  -- Find the matching case branch
  (branch, (local_bindings, local_ctx)) <-
    findBranch (matchBranch arg) branches

  let bindings' = local_bindings ++ bindings
      binding_ctx' = local_ctx `mappend` binding_ctx
      DecisionBranch label decon field_patterns subtree = branch

  -- Translate the 'Case' decision to a case expression
  let make_case subexpression =
        let scrutinee_expr = ExpM $ VarE defaultExpInfo v
            alt = AltM $ Alt (DeCInstM decon) field_patterns subexpression
        in ExpM $ CaseE defaultExpInfo scrutinee_expr [alt]

  -- Convert the rest of the tree to an expression.  Emit a 'case' statement
  -- to specialize this argument.
  fmap make_case $

    -- Try to specialize on a subtree
    specializeFromDecisionTree bindings' binding_ctx' out_params subtree `mplus`
    
    -- If unable to specialize on a subtree,
    -- try to specialize at this tree node
    case label
    of Nothing -> Nothing  -- No specialization exists here
       Just specialized_function ->
         -- Call this specialized function
         return $ specializedCallExp defaultExpInfo specialized_function
         binding_ctx' out_params

-- | Convert the arguments of an 'AppE' to a 'CallPattern'.
computeCallPattern :: EvalMonad m => [TypM] -> [ExpM] -> m CallPattern
computeCallPattern ts es = do
  -- Separate arguments into input and output arguments
  e_types <- mapM inferExpType es
  tenv <- getTypeEnv
  let (in_argtypes, out_argtypes) = break is_output $ zip es e_types
        where
          is_output (_, t) = OutK == toBaseKind (typeKind tenv t)
      in_args = map fst in_argtypes
      out_args = map fst out_argtypes
  return $ CallPattern ts (map (callPatternArg tenv) in_args) out_args

callPatternArg tenv expression =
  case fromExpM expression
  of ConE _ (CInstM con) args
       | isValueConstructor con ->
         -- The argument is a constructor application term
         ConArg con $ map (callPatternArg tenv) args
     _ -> SomeArg expression
  where
    isValueConstructor (VarCon v _ _) =
      case lookupDataConWithType v tenv
      of Just (dtype, _) ->
           dataTypeKind dtype == ValK ||
           dataTypeKind dtype == BoxK
         _ -> internalError "callPatternArg"

    isValueConstructor (TupleCon _) = True
         
callPatternArgExp (SomeArg e) = e
callPatternArgExp (ConArg cinst args) =
  conE defaultExpInfo cinst (map callPatternArgExp args)

-------------------------------------------------------------------------------

data SpecializeEnv =
  SpecializeEnv
  { varIdSupply :: {-#UNPACK#-}!(IdentSupply Var)
  , typeEnvironment :: !TypeEnv
  , currentSpecializations :: WantedSpecializationsMap
  }

newtype Specialize a = Specialize (ReaderT SpecializeEnv IO a)
  deriving(Functor, Monad, Applicative)

instance MonadIO Specialize where
  liftIO m = Specialize $ liftIO m

instance Supplies Specialize (Ident Var) where
  fresh = Specialize $ ReaderT $ \env -> supplyValue (varIdSupply env)

instance TypeEnvMonad Specialize where
  getTypeEnv = Specialize $ asks typeEnvironment
  assumeWithProperties v t b (Specialize m) = Specialize $ local add_type m
    where
      add_type env =
        env {typeEnvironment =
                insertTypeWithProperties v t b $ typeEnvironment env}

instance EvalMonad Specialize where
  liftTypeEvalM m = Specialize $ ReaderT $ \env ->
    runTypeEvalM m (varIdSupply env) (typeEnvironment env)

lookupSpecialization :: Var
                     -> Specialize (Maybe (IORef WantedSpecializations))
lookupSpecialization v = Specialize $ ReaderT $ \env ->
  let specialization = IntMap.lookup (fromIdent $ varID v) (currentSpecializations env)
  in return specialization

insertCallPattern :: IORef WantedSpecializations -> CallPattern -> Specialize ()
insertCallPattern ref p = liftIO $ do
  spcl <- readIORef ref
  writeIORef ref $! recordCall p spcl

runSpecialize (Specialize m) e = runReaderT m e

specializeExp :: ExpM -> Specialize ExpM
specializeExp expression =
  case fromExpM expression
  of VarE {} -> return expression
     LitE {} -> return expression
     ConE inf op args ->
       ExpM <$> (ConE inf op <$> specializeExps args)
     AppE inf op ty_args args ->
       specializeApp inf op ty_args args
     LamE inf f ->
       ExpM <$> (LamE inf <$> specializeFun f)
     LetE inf pat rhs body -> do
       rhs' <- specializeExp rhs
       body' <- assumePatM pat $ specializeExp body
       return $ ExpM $ LetE inf pat rhs' body'
     LetfunE inf defs body -> specializeLetfun inf defs body
     CaseE inf scr alts ->
       ExpM <$> (CaseE inf <$> specializeExp scr <*> mapM specializeAlt alts)
     ExceptE {} -> return expression
     CoerceE inf t1 t2 body ->
       ExpM <$> (CoerceE inf t1 t2 <$> specializeExp body)

specializeExps es = mapM specializeExp es

specializeLetfun inf defs body = do
  (body', specializations, defs') <-
    specializeDefGroup defs $ specializeExp body

  -- If some functions were specialized, then specialize the corresponding
  -- function calls
  case specializations of
    Nothing ->
      return $ ExpM $ LetfunE inf defs' body'
    Just spcl_map -> liftTypeEvalM $ do
      (defs'', body'') <-
        assumeDefGroup defs'
        (case defs'
         of NonRec {} -> return defs'
            Rec ds -> Rec <$> mapM (specializeCallsDef spcl_map) ds)
        (specializeCallsExp spcl_map body')
      return $ ExpM $ LetfunE inf defs'' body''

-- | Perform specialization in a function application.
--   If the callee is a specializable function, then record the call as 
--   a potential specialization.
specializeApp inf op ty_args args =
  case op
  of ExpM (VarE _ op_var) -> do
       m_specialization <- lookupSpecialization op_var
       tenv <- getTypeEnv
       case m_specialization of
         Just ref -> do
           -- Record this call pattern
           pattern <- computeCallPattern ty_args args
           insertCallPattern ref pattern
         Nothing -> return ()

       subexpressions op
     _ -> do
       op' <- specializeExp op
       subexpressions op'
  where
    subexpressions op' = do
      args' <- mapM specializeExp args
      return $ ExpM $ AppE inf op' ty_args args'

specializeAlt (AltM alt) =
  assumeBinders (deConExTypes $ fromDeCInstM $ altCon alt) $
  assumePatMs (altParams alt) $ do
    body <- specializeExp (altBody alt)
    return $ AltM $ alt {altBody = body}
  
specializeFun (FunM f) =
  assumeTyPatMs (funTyParams f) $
  assumePatMs (funParams f) $ do
    body <- specializeExp (funBody f)
    return $ FunM $ f {funBody = body}

-- | Perform specialization in a definition group.  During specialization,
--   the group and body are scanned to decide how to specialize.  The
--   generated information is used to create specialized versions of the 
--   functions.
--
--   Function calls are not specialized--that must be done in a separate pass.
specializeDefGroup :: DefGroup (Def Mem)
                   -> Specialize a
                   -> Specialize (a,
                                  Maybe CreatedSpecializationsMap,
                                  DefGroup (Def Mem))
specializeDefGroup group m =
  case group
  of NonRec def -> do
       -- Run the computation
       (return_value, specializations) <-
         withWantedSpecializations [def] m

       -- Perform specialization inside the function
       def' <- mapMDefiniens specializeFun def

       specialize_group (NonRec def') [def']
         return_value specializations

     Rec defs -> do
       -- Scan the recursive functions and run the computation
       ((return_value, defs'), specializations) <-
         withWantedSpecializations defs $ do
           return_value <- m
           defs' <- mapM (mapMDefiniens specializeFun) defs
           return (return_value, defs')

       specialize_group (Rec defs') defs'
         return_value specializations
  where
    specialize_group grp defs return_value specializations
      | IntMap.null specializations =
          debug (text "Unspecialized functions" <+>
                 sep (map (pprVar . definiendum) $ defGroupMembers grp)) $
          return (return_value, Nothing, grp)
      | otherwise = do
          (new_defs, created) <- specialize_functions specializations defs
          return (return_value, Just created, Rec new_defs)

    specialize_function :: IntMap.IntMap WantedSpecializations -> Def Mem
                        -> Specialize ([Def Mem], Maybe (Var, CreatedSpecializations))
    specialize_function wanted_map def
      | Just wanted <-
        IntMap.lookup (fromIdent $ varID $ definiendum def) wanted_map = do
          let name = definiendum def
              fun_label = varName $ definiendum def
              annotation = defAnnotation def
          (f, specializations, new_defs) <-
            decisionTreeFun fun_label annotation wanted
          let specialized_functions = Def name annotation f : new_defs
          
          -- If debugging this module,
          -- notify user that a function was specialized
          let debug_message =
                hang (text "Constructor specialized function") 2 $
                old $$ text "----" $$ new
                where
                  old = pprDef def
                  new = vcat (map pprDef specialized_functions)
          debug debug_message $
            return (specialized_functions, Just (name, specializations))
      | otherwise =
          debug (text "Unspecialized function" <+> pprVar (definiendum def)) $
          return ([def], Nothing)

    specialize_functions :: IntMap.IntMap WantedSpecializations
                         -> [Def Mem]
                         -> Specialize ([Def Mem], IntMap.IntMap CreatedSpecializations)
    specialize_functions wanted_map xs = do
      (defss, assocs) <- mapAndUnzipM (specialize_function wanted_map) xs
      let m = IntMap.fromList [(fromIdent $ varID v, c)
                              | (v, c) <- catMaybes assocs]
      return (concat defss, m)

-- | Create decision trees of some functions and pass them to some
--   computation.  Run the computation to compute wanted specializations.
--   Return the wanted specializations, and the list of functions that 
--   shouldn't be specialized.
withWantedSpecializations :: [Def Mem]
                          -> Specialize a
                          -> Specialize (a, IntMap.IntMap WantedSpecializations)
withWantedSpecializations defs m = Specialize $ ReaderT $ \env -> do
  -- Create wanted specializations.  Skip the ones that can't be specialized
  -- anyway.
  let tenv = typeEnvironment env
  m_wanted_specialization_list <- forM defs $ \def -> 
    let dfun = functionDecisionTree tenv $ definiens def
    in if isSingletonTree dfun
       then return Nothing
       else do ref <- newIORef dfun
               return $ Just (definiendum def, ref)
  let wanted_specialization_list = catMaybes m_wanted_specialization_list
  
  -- Add wanted specializations to environment.  Skip the ones that can't 
  -- be specialized anyway.
  let insert_specializations e = foldr ins e wanted_specialization_list
        where ins (v,s) e = IntMap.insert (fromIdent $ varID v) s e
  let local_env = env {currentSpecializations =
                          insert_specializations $ currentSpecializations env}

  -- Run the computation
  return_value <- runSpecialize (assume_defs defs m) local_env
  
  -- Read and return the set of wanted specializations
  wanted <-
    let insert_specialization m (v, ref) = do
          s <- readIORef ref
          return $! if hasSpecializations s
                    then IntMap.insert (fromIdent $ varID v) s m
                    else m
    in foldM insert_specialization IntMap.empty wanted_specialization_list

  return (return_value, wanted)
  where
    assume_defs defs m = foldr assumeDef m defs

specializeExport export = do
  f <- specializeFun (exportFunction export)
  return $ export {exportFunction = f}
  
specializeTopLevel :: [DefGroup (Def Mem)] -> [Export Mem]
                   -> Specialize ([DefGroup (Def Mem)], [Export Mem])
specializeTopLevel (defs:defss) exports = do
  ((defss', exports'), specializations, defs') <-
    specializeDefGroup defs $ specializeTopLevel defss exports
  case specializations of
    Nothing -> return (defs' : defss', exports')
    Just spcl_map -> liftTypeEvalM $ do
      (defs'', (defss'', exports'')) <-
        assumeDefGroup defs'
        (case defs'
         of NonRec {} -> return defs'
            Rec ds -> Rec <$> mapM (specializeCallsDef spcl_map) ds)
        (specializeCallsTopLevel spcl_map defss' exports')
      return (defs'' : defss'', exports'')

specializeTopLevel [] exports = do
  exports' <- mapM specializeExport exports
  return ([], exports')

specializeModule (Module module_name imports defs exports) =
  assume_imports $ do
    (defs', exports') <- specializeTopLevel defs exports
    return $ Module module_name imports defs' exports' 
  where
    assume_imports m = foldr assumeDef m imports

-------------------------------------------------------------------------------

-- | Replace function calls with specialized function calls, based on 
--   the given set of specializations.
specializeCallsExp :: IntMap.IntMap CreatedSpecializations
                -> ExpM
                -> TypeEvalM ExpM
specializeCallsExp spcl_map expression =
  case fromExpM expression
  of VarE {} -> return expression
     LitE {} -> return expression 
     ConE inf op args ->
       ExpM <$> (ConE inf op <$> specializeCallsExps spcl_map args)
     AppE inf op@(ExpM (VarE _ op_var)) ty_args args
       | Just spcl <- IntMap.lookup (fromIdent $ varID op_var) spcl_map -> do
           -- This is a call of a specialized function
           args' <- specializeCallsExps spcl_map args
           pattern <- computeCallPattern ty_args args'
           m_specialized_call <- specializeCall pattern spcl
           case m_specialized_call of
             Nothing -> return $ ExpM $ AppE inf op ty_args args'
             Just e  -> trace_specialization e $ return e
     AppE inf op ty_args args -> do
       -- Cannot specialize on this operator
       op' <- specializeCallsExp spcl_map op
       args' <- specializeCallsExps spcl_map args
       return $ ExpM $ AppE inf op' ty_args args'
     LamE inf f ->
       ExpM <$> (LamE inf <$> specializeCallsFun spcl_map f)
     LetE inf pat rhs body -> do
       rhs' <- specializeCallsExp spcl_map rhs
       body' <- assumePatM pat $ specializeCallsExp spcl_map body
       return $ ExpM $ LetE inf pat rhs' body'
     LetfunE inf defs body -> do
       (defs', body') <-
         assumeDefGroup defs
         (mapM (specializeCallsDef spcl_map) defs)
         (specializeCallsExp spcl_map body)
       return $ ExpM $ LetfunE inf defs' body'
     CaseE inf scr alts ->
       ExpM <$> (CaseE inf <$>
                 specializeCallsExp spcl_map scr <*>
                 mapM (specializeCallsAlt spcl_map) alts)
     ExceptE {} -> return expression
     CoerceE inf t1 t2 e ->
       ExpM <$> (CoerceE inf t1 t2 <$> specializeCallsExp spcl_map e)
  where
    -- If debugging this module, notify user that a call was specialized
    trace_specialization e =
      debug
      (text "Specialized call" <+> (pprExp expression $$ text "to" $$ pprExp e))

specializeCallsExps spcl_map es = mapM (specializeCallsExp spcl_map) es
                                               
specializeCallsAlt spcl_map (AltM alt) =
  assumeBinders (deConExTypes $ fromDeCInstM $ altCon alt) $
  assumePatMs (altParams alt) $ do
    body <- specializeCallsExp spcl_map (altBody alt)
    return $ AltM $ alt {altBody = body}

specializeCallsFun spcl_map (FunM f) =
  assumeTyPatMs (funTyParams f) $
  assumePatMs (funParams f) $ do
    body <- specializeCallsExp spcl_map (funBody f)
    return $ FunM $ f {funBody = body}

specializeCallsDef spcl_map def =
  mapMDefiniens (specializeCallsFun spcl_map) def

specializeCallsExport spcl_map export = do
  f <- specializeCallsFun spcl_map $ exportFunction export
  return $ export {exportFunction = f}

specializeCallsTopLevel :: CreatedSpecializationsMap
                        -> [DefGroup (Def Mem)]
                        -> [Export Mem]
                        -> TypeEvalM ([DefGroup (Def Mem)], [Export Mem])
specializeCallsTopLevel spcl_map (defs : defss) exports = do
  (defs', (defss', exports')) <-
    assumeDefGroup defs
    (mapM (specializeCallsDef spcl_map) defs)
    (specializeCallsTopLevel spcl_map defss exports)
  return (defs' : defss', exports')

specializeCallsTopLevel spcl_map [] exports = do
  exports' <- mapM (specializeCallsExport spcl_map) exports
  return ([], exports')

-------------------------------------------------------------------------------

specializeOnConstructors :: Module Mem -> IO (Module Mem)
specializeOnConstructors mod =
  withTheNewVarIdentSupply $ \id_supply -> do
    tenv <- readInitGlobalVarIO the_memTypes
    let env = SpecializeEnv id_supply tenv IntMap.empty
    case specializeModule mod of Specialize m -> runReaderT m env
