{-| Abstract values.
    This module replaces the old "SystemF.Simplifier.KnownValue".

Most of the simplification performed by the simplifier relies on knowing some
approximation of the run-time value of an expresion or a variable.  The
'AbsValue' data type is how we store this information.

A data value that's in the correct representation for a @case@ statement is
represented by a 'DataAV' term.
-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module SystemF.Simplifier.AbsValue
       (-- * Abstract values
        AbsCode,
        topCode,
        isTopCode,
        valueCode,
        labelCode,
        labelCodeVar,
        relabelCodeVar,
        codeExp,
        codeTrivialExp,
        codeValue,
        litCode,
        trueCode, falseCode,
        varEqualityTestCode,
        conjunctionCode,
        AbsValue(..),
        AbsData(..),
        AbsProp(..),
        funValue,
        initializerValue,
        scrutineeDataValue,
        AbsComputation(..),
        
        -- * Interpretation
        applyCode,
        interpretCon,
        interpretConAsValue,
        interpretInitializer,
        interpretConstant,

        -- * Concretization
        concretize,
        absPropSubstitutions,

        -- * Printing
        pprAbsCode,

        -- * Environments of abstract values
        AbsEnv,
        emptyAbsEnv,
        absEnvMembers,
        insertAbstractValue,
        lookupAbstractValue
        )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.Monoid(Monoid(..))
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.Supply
import Builtins.Builtins
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import qualified SystemF.Rename as SFRename
import SystemF.TypecheckMem
import Type.Environment
import Type.Eval
import Type.Type
import qualified Type.Rename as Rename
import Type.Substitute(TypeSubst,
                       SubstitutionMap(..), Substitutable(..),
                       substitute, freshen)
import qualified Type.Substitute as Substitute

renameMany :: (st -> a -> (st -> a -> b) -> b)
           -> st -> [a] -> (st -> [a] -> b) -> b
renameMany f rn (x:xs) k =
  f rn x $ \rn' x' -> renameMany f rn' xs $ \rn'' xs' -> k rn'' (x':xs')

renameMany _ rn [] k = k rn []

-- | An abstract value labeled with a piece of code and/or a variable.
--
--   The label retrieved with 'codeExp' or 'codeTrivialExp' is an
--   expression that is exactly equal to the abstract value.  At the
--   discretion of the simplifier, this expression may be inlined in
--   place of the abstract value.
--
--   Of these functions, 'codeTrivialExp' only returns a variable or 
--   literal, while 'codeExp' may return a larger expession.  Function values
--   are an example of where both are useful: the larger expression is needed
--   for beta-reduction (i.e., inlining) while the variable is useful for
--   copy propagation when the function value is copied but not called.
--
--   If the value is a 'LitAV' or 'VarAV', the label does not have to be
--   explicitly stored.  Note that the abstract value (not the label) is
--   given priority when creating an expression.
data AbsCode =
  AbsCode { _codeLabel :: !(Maybe ExpM)
          , _codeVarLabel :: !(Maybe Var)
          , _codeValue :: !AbsValue
          }

-- | The least precise 'AbsCode' value.
topCode :: AbsCode
topCode = AbsCode Nothing Nothing TopAV

isTopCode (AbsCode Nothing Nothing TopAV) = True
isTopCode _ = False

-- | Create an 'AbsCode' from an 'AbsValue'.  The created code is not labeled.
valueCode :: AbsValue -> AbsCode
valueCode v = AbsCode Nothing Nothing v

-- | Attach a label to an 'AbsCode', to be retrieved with 'codeExp'.
labelCode :: ExpM -> AbsCode -> AbsCode
labelCode lab code = code {_codeLabel = Just lab}

-- | Attach a variable label to an 'AbsCode', to be retrieved with
--   'codeTrivialExp', unless the code already has a trivial expression.
labelCodeVar :: Var -> AbsCode -> AbsCode
labelCodeVar v code
  | isJust $ codeTrivialExp code = code
  | TopAV <- _codeValue code = AbsCode (_codeLabel code) Nothing (VarAV v)
  | otherwise = code {_codeVarLabel = Just v}

-- | Attach a variable label to an 'AbsCode', to be retrieved with
--   'codeTrivialExp'.
relabelCodeVar :: Var -> AbsCode -> AbsCode
relabelCodeVar v code = code {_codeVarLabel = Just v}

-- | Convert an 'AbsCode' to an expression if possible.
codeExp :: AbsCode -> Maybe ExpM
codeExp code
  -- First, try to get the expression that was assigned
  | Just lab <- _codeLabel code = Just lab

  -- Next, try to get a trivial value
  | LitAV l <- _codeValue code = Just $ ExpM (LitE defaultExpInfo l)
  | VarAV v <- _codeValue code = Just $ ExpM (VarE defaultExpInfo v)

  -- Finally, get the variable that was assigned
  | Just v <- _codeVarLabel code = Just $ ExpM (VarE defaultExpInfo v)
  | otherwise = Nothing

-- | Convert an 'AbsCode' to an expression if it can be represented by a
--   trivial expression.
codeTrivialExp :: AbsCode -> Maybe ExpM
codeTrivialExp code =
  case _codeVarLabel code
  of Just v -> Just $ ExpM (VarE defaultExpInfo v)
     Nothing ->
       case _codeValue code
       of LitAV l -> Just $ ExpM (LitE defaultExpInfo l)
          VarAV v -> Just $ ExpM (VarE defaultExpInfo v)
          _ -> case _codeLabel code
               of Nothing -> Nothing
                  Just exp -> 
                    case exp
                    of ExpM (LitE {}) -> Just exp
                       ExpM (VarE {}) -> Just exp
                       _ -> Nothing

codeValue :: AbsCode -> AbsValue
codeValue = _codeValue

litCode :: Lit -> AbsCode
litCode l = valueCode $ LitAV l

trueCode, falseCode :: AbsCode
trueCode =
  valueCode $ DataAV $ AbsData (VarCon (coreBuiltin The_True) [] []) []
falseCode =
  valueCode $ DataAV $ AbsData (VarCon (coreBuiltin The_False) [] []) []

-- | Create abstract code of the boolean expression @v == L@ for some variable
--   @v@ and literal @L@.
varEqualityTestCode :: Var -> Lit -> AbsCode
varEqualityTestCode v l =
  valueCode $ BoolAV $ AbsValueProp v (litCode l)

conjunctionCode :: AbsCode -> AbsCode -> AbsCode
conjunctionCode c1 c2 =
  let p = case codeValue c1
          of BoolAV p -> p
             _ -> AbsAnyProp
      q = case codeValue c2
          of BoolAV p -> p
             _ -> AbsAnyProp
  in maybe topCode (valueCode . BoolAV) $ conjunction p q
  where
    conjunction AbsAnyProp AbsAnyProp = Nothing
    conjunction AbsAnyProp p          = Just p
    conjunction p          AbsAnyProp = Just p
    conjunction p          q          = Just $ AbsConjunction p q


data AbsValue =
    TopAV                       -- ^ Unknown value
  | VarAV !Var                  -- ^ A variable
  | LitAV !Lit                  -- ^ A literal
  | FunAV !AbsFun               -- ^ A function
  | DataAV !AbsData             -- ^ A fully applied constructor
  | HeapAV !AbsHeap             -- ^ A heap fragment
  | BoolAV !AbsProp             -- ^ A boolean value carrying the truth
                                --   value of a proposition

data AbsComputation =
    TopAC                       -- ^ Unknown computation
  | ReturnAC !AbsCode           -- ^ Computation returning a value
  | ExceptAC                    -- ^ Computation that does not return

-- | Simulate the effect of performing a computation, then computing something
--   else with its result.
interpretComputation :: Monad m =>
                        AbsComputation
                     -> (AbsCode -> m AbsComputation)
                     -> m AbsComputation
interpretComputation TopAC        _ = return TopAC
interpretComputation ExceptAC     _ = return ExceptAC
interpretComputation (ReturnAC x) f = f x

-- | Simulate the effect of performing a sequence of computations,
--   then combining their results.
sequenceComputations :: Monad m =>
                        [AbsComputation]
                     -> ([AbsCode] -> m AbsComputation)
                     -> m AbsComputation
sequenceComputations xs f
  | any is_except xs = return ExceptAC
  | any is_top xs    = return TopAC
  | otherwise        = f [c | ReturnAC c <- xs]
  where
    is_except ExceptAC = True
    is_except _ = False
    is_top TopAC = True
    is_top _ = False

data AbsFun =
  AbsFun
  { afunTyParams :: [Binder]
  , afunParams   :: [PatM]
  , afunBody     :: AbsComputation
  }

data AbsData =
  AbsData
  { dataCon    :: !ConInst
  , dataFields :: [AbsCode]
  }

-- | A heap fragment.  The domain of the heap fragment indicates exactly
--   the contents of the heap fragment.
newtype AbsHeap = AbsHeap {fromAbsHeap :: HeapMap AbsCode}

data AbsProp =
    -- | A proposition of the form @v = N@, for variable @v@ and value @N@.
    --   @N@ can be represented by a trivial expression
    --   ('codeTrivialExp' returns a 'Just' value).
    --   Where this proposition is true, we can substitute @N@ for @v@.
    AbsValueProp
    { apVar   :: !Var
    , apValue :: AbsCode
    }
    -- | A conjunction of propositions
  | AbsConjunction AbsProp AbsProp
    -- | An unknown proposition
  | AbsAnyProp

-------------------------------------------------------------------------------
-- Printing

pprAbsCode :: AbsCode -> Doc
pprAbsCode (AbsCode Nothing Nothing val) = pprAbsValue val
pprAbsCode (AbsCode lab var val) =
  let lab_doc =
        case (lab, var)
        of (Just lab, Nothing) -> pprExp lab
           (Nothing, Just v)   -> pprVar v
           (Just lab, Just v)  -> pprVar v <+> text "=" <+> pprExp lab
      val_doc = pprAbsValue val
  in braces lab_doc $$ text "~=" <+> val_doc

pprAbsValue TopAV = text "TOP"
pprAbsValue (VarAV v) = pprVar v
pprAbsValue (LitAV l) = pprLit l
pprAbsValue (FunAV f) = pprAbsFun f
pprAbsValue (DataAV d) = pprAbsData d
pprAbsValue (HeapAV hp) = pprAbsHeap hp
pprAbsValue (BoolAV b) = text "BOOL" <> parens (pprAbsProp b)

pprAbsComputation TopAC = text "TOP"
pprAbsComputation (ReturnAC c) = text "RET" <+> pprAbsCode c
pprAbsComputation ExceptAC = text "EXCEPT"

pprAbsFun (AbsFun ty_params params body) =
  let ty_params_doc = [text "@" <> parens (pprVar v <+> colon <+> pprType t)
                      | v ::: t <- ty_params]
      params_doc = [parens (pprVar (patMVar p) <+> colon <+> pprType (patMType p))
                   | p <- params]
  in hang (text "lambda" <+> sep (ty_params_doc ++ params_doc) <> text ".") 4 $
     pprAbsComputation body

pprAbsData (AbsData (VarCon op ty_args ex_types) fs) =
  let op_doc = text "<" <> pprVar op <> text ">"
      ty_args_doc = [text "@" <> pprType t | t <- ty_args]
      ex_types_doc = [text "&" <> pprType t | t <- ex_types]
      args_doc = map pprAbsCode fs
  in parens $ hang op_doc 6 (sep $ ty_args_doc ++ ex_types_doc ++ args_doc)

pprAbsData (AbsData (TupleCon _) fs) =
  parens $ sep $ punctuate comma $ map pprAbsCode fs

pprAbsHeap (AbsHeap (HeapMap xs)) =
  braces $ vcat $ punctuate semi [pprVar a <+> text "|->" <+> pprAbsCode v | (a, v) <- xs]

pprAbsProp (AbsValueProp v l) =
  pprVar v <+> equals <+> pprAbsCode l

pprAbsProp (AbsConjunction p1 p2) =
  pprAbsProp p1 <+> text "&&" <+> pprAbsProp p2

pprAbsProp AbsAnyProp = text "_"

-------------------------------------------------------------------------------
-- Substitution

-- | A substitution on abstract values
type AVSubst = IntMap.IntMap AbsValue

-- | A partial substitution on value terms.  If a variable is assigned
--   'Nothing', it cannot be represented and the value must be replaced by
--   'Nothing'.
type VSubst = IntMap.IntMap (Maybe ExpM)

excludeV v s = IntMap.delete (fromIdent $ varID v) s

excludeA v s = IntMap.delete (fromIdent $ varID v) s

extendV v mval s = IntMap.insert (fromIdent $ varID v) mval s

extendA v aval s = IntMap.insert (fromIdent $ varID v) aval s

-- | A substitution on abstract values.
--
--   The domain of 'absSubst' is the union of the domains of
--   'valueSubst' and 'unrepresentable'.  The map 'valueSubst' and set
--   'unrepresentable' are disjoint.
data AbsSubst =
  AbsSubst { -- | Substitution on types
             typeSubst :: TypeSubst

             -- | Substituion on value variables
           , valueSubst :: VSubst

             -- | Substitution on abstract value variables
           , absSubst :: AVSubst}

instance SubstitutionMap AbsSubst where
  emptySubstitution =
    AbsSubst emptySubstitution IntMap.empty IntMap.empty
  isEmptySubstitution (AbsSubst t v a) =
    isEmptySubstitution t && IntMap.null v && IntMap.null a

lookupValue :: Var -> AbsSubst -> Maybe (Maybe ExpM)
lookupValue v s = IntMap.lookup (fromIdent $ varID v) (valueSubst s)

lookupAbsValue :: Var -> AbsSubst -> Maybe AbsValue
lookupAbsValue v s = IntMap.lookup (fromIdent $ varID v) (absSubst s)

-- | Modify a substitution and bound variable name if necessary.
--   See 'substituteBinder'.
renameIfBound :: EvalMonad m => AbsSubst -> Var -> m (AbsSubst, Var)
renameIfBound s x = do
  -- Is the bound variable in scope?
  type_assignment <- askTypeEnv (lookupType x)
  case type_assignment of
    Nothing -> do
      let s' = s { valueSubst = excludeV x $ valueSubst s
                 , absSubst = excludeA x $ absSubst s}
      return (s', x)
    Just _  -> do
      -- In scope: rename and add to the substitution
      x' <- newClonedVar x
      let s' = s { valueSubst = let value = ExpM $ VarE defaultExpInfo x'
                                in extendV x (Just value) $ valueSubst s
                 , absSubst = extendA x (VarAV x') $ absSubst s}
      return (s', x')

-- | Apply a substitution to a binder that binds a value to a variable.
--
-- See 'substituteBinder'.
substituteValueBinder :: EvalMonad m =>
                         AbsSubst -> Binder
                       -> (AbsSubst -> Binder -> m a)
                       -> m a
substituteValueBinder s (x ::: t) k = do
  t' <- substitute (typeSubst s) t
  (s', x') <- renameIfBound s x
  assume x' t' $ k s' (x' ::: t')

substituteDeConInst s (VarDeCon op ty_args ex_types) k = do
  ty_args' <- substituteType s ty_args
  Substitute.substituteBinders (typeSubst s) ex_types $ \ts' ex_types' ->
    k (s {typeSubst = ts'}) (VarDeCon op ty_args' ex_types')

substituteDeConInst s (TupleDeCon ty_args) k = do
  ty_args' <- substituteType s ty_args
  k s (TupleDeCon ty_args')

-- | Apply a substitution to a pattern
substitutePatM :: EvalMonad m =>
                  AbsSubst -> PatM -> (AbsSubst -> PatM -> m a) -> m a
substitutePatM s (PatM binder uses) k = do
  uses' <- substitute (typeSubst s) uses
  substituteValueBinder s binder $ \s' binder' -> k s' (PatM binder' uses')

substitutePatMs :: EvalMonad m =>
                   AbsSubst -> [PatM] -> (AbsSubst -> [PatM] -> m a) -> m a
substitutePatMs = renameMany substitutePatM

substituteTyPatM s (TyPat binder) k =
  Substitute.substituteBinder (typeSubst s) binder $ \ts' binder' ->
  k (s {typeSubst = ts'}) (TyPat binder')

substituteTyPatMs = renameMany substituteTyPatM

substituteDefGroup s g k =
  case g
  of NonRec def -> do
       -- Get function type
       fun_type <- substitute (typeSubst s) $ functionType (definiens def)

       -- No new variables in scope over function body
       def1 <- mapMDefiniens (substituteFun s) def
       
       -- Rename the bound variable if appropriate
       (s', v') <- renameIfBound s (definiendum def)
       let def' = def1 {definiendum = v'}
       
       -- Add function to environment
       assume v' fun_type $ k s' (NonRec def')

     Rec defs -> do
       -- Get the functions' types.  Function types cannot refer to
       -- local variables.
       function_types <-
         mapM (substitute (typeSubst s) . functionType . definiens) defs

       -- Rename variables that shadow existing names
       let definienda = map definiendum defs
       (s', renamed_definienda) <- mapAccumM renameIfBound s definienda

       -- Rename functions
       assumeBinders (zipWith (:::) renamed_definienda function_types) $ do
         defs' <- mapM (mapMDefiniens (substituteFun s')) defs
         let new_defs = [def {definiendum = v}
                        | (def, v) <- zip defs' renamed_definienda]
         k s' (Rec new_defs)

substituteType :: (Substitutable a, Substitution a ~ TypeSubst) => 
                  AbsSubst -> a -> MaybeT TypeEvalM a
substituteType s t = lift $ substitute (typeSubst s) t

-- | Apply a substitution to an expression
substituteExp :: AbsSubst -> ExpM -> MaybeT TypeEvalM ExpM
substituteExp s expression =
  case fromExpM expression
  of VarE inf v ->
       case lookupValue v s
       of Nothing       -> return expression
          Just Nothing  -> mzero -- This expression is unrepresentable
          Just (Just e) -> return e
     LitE {} -> return expression
     ConE inf con args ->
       ExpM <$>
       (ConE inf <$>
        substituteType s con <*>
        mapM (substituteExp s) args)
     AppE inf op ty_args args ->
       ExpM <$>
       (AppE inf <$>
        substituteExp s op <*>
        substituteType s ty_args <*>
        mapM (substituteExp s) args)
     LamE inf f ->
       ExpM . LamE inf <$> substituteFun s f
     LetE inf pat rhs body -> do
       rhs' <- substituteExp s rhs
       substitutePatM s pat $ \s' pat' -> do
         body' <- substituteExp s' body
         return $ ExpM $ LetE inf pat' rhs' body'
     LetfunE inf defs body ->
       substituteDefGroup s defs $ \s' defs' -> do
         body' <- substituteExp s body
         return $ ExpM $ LetfunE inf defs' body'
     CaseE inf scr alts ->
       ExpM <$>
       (CaseE inf <$> substituteExp s scr <*> mapM (substituteAlt s) alts)
     ExceptE inf t ->
       ExpM . ExceptE inf <$> substituteType s t
     CoerceE inf t1 t2 body ->
       ExpM <$>
       (CoerceE inf <$>
        substituteType s t1 <*>
        substituteType s t2 <*>
        substituteExp s body)

substituteFun s (FunM f) =
  substituteTyPatMs s (funTyParams f) $ \s' ty_params ->
  substitutePatMs s' (funParams f) $ \s'' params -> do
    ret <- substituteType s'' (funReturn f)
    body <- substituteExp s'' (funBody f)
    return $ FunM $ Fun (funInfo f) ty_params params ret body

substituteAlt s (AltM (Alt decon params body)) =
  substituteDeConInst s decon $ \s' decon' ->
  substitutePatMs s' params $ \s'' params' -> do
    body' <- substituteExp s body
    return $ AltM (Alt decon' params' body')

substituteAbsValue s value =
  case value
  of TopAV   -> return value
     VarAV v -> case lookupAbsValue v s
                of Nothing  -> return value
                   Just val -> return val
     LitAV _ -> return value
     FunAV f -> FunAV `liftM` substitute s f
     DataAV d -> DataAV `liftM` substitute s d
     HeapAV h -> do
       -- Substitute the heap map; the result may be unrepresentable 
       h' <- substituteAbsHeap s h
       return $! case h'
                 of Nothing -> TopAV
                    Just hm -> HeapAV hm
     BoolAV p -> case substituteAbsProp s p
                 of Nothing -> return TopAV
                    Just p' -> return $ BoolAV p'

instance Substitutable AbsCode where
  type Substitution AbsCode = AbsSubst
  
  substituteWorker s code = do
    -- Substitute the variable label first
    let (var_label, expanded_var_label) =
          case _codeVarLabel code
          of Nothing -> (Nothing, Nothing)
             Just v ->
               case lookupValue v s
               of Nothing       -> (Just v, Nothing)
                  Just Nothing  -> (Nothing, Nothing)
                  Just (Just e) -> (Nothing, Just e)
    -- Substitute the code label
    label <-
      case expanded_var_label
      of Just lab -> return $ Just lab
         Nothing ->
           case _codeLabel code
           of Nothing -> return Nothing
              Just e -> liftTypeEvalM $ runMaybeT $ substituteExp s e
    value <- substitute s (_codeValue code)
    return $ AbsCode label var_label value

instance Substitutable AbsValue where
  type Substitution AbsValue = AbsSubst
  
  substituteWorker = substituteAbsValue

instance Substitutable AbsComputation where
  type Substitution AbsComputation = AbsSubst

  substituteWorker s comp =
    case comp
    of TopAC -> return TopAC
       ReturnAC c -> ReturnAC `liftM` substitute s c
       ExceptAC -> return ExceptAC

instance Substitutable AbsFun where
  type Substitution AbsFun = AbsSubst
  
  substituteWorker s (AbsFun ty_params params body) =
    Substitute.substituteBinders (typeSubst s) ty_params $ \ts' ty_params' ->
    substitutePatMs (s {typeSubst = ts'}) params $ \s' params' -> do
      body' <- substitute s body
      return $ AbsFun ty_params' params' body'

instance Substitutable AbsData where
  type Substitution AbsData = AbsSubst
  
  substituteWorker s (AbsData con fields) = do
    con' <- substitute (typeSubst s) con
    fields' <- substitute s fields
    return $ AbsData con' fields'
    
substituteAbsProp :: AbsSubst -> AbsProp -> Maybe AbsProp
substituteAbsProp s prop =
  case prop
  of AbsValueProp v l ->
       -- Substitute for 'v' if possible
       case lookupAbsValue v s 
       of Nothing -> Just prop
          Just (VarAV v') -> Just $ AbsValueProp v' l
          Just _  -> Just $ AbsAnyProp
     AbsConjunction p1 p2 ->
       substituteAbsProp s p1 `conjunction` substituteAbsProp s p2
     AbsAnyProp ->
       Just $ AbsAnyProp
  where
    conjunction (Just p) (Just q) = Just $ AbsConjunction p q
    conjunction (Just p) Nothing  = Just p
    conjunction Nothing  (Just q) = Just q
    conjunction Nothing  Nothing  = Nothing

substituteAbsHeap :: EvalMonad m => AbsSubst -> AbsHeap -> m (Maybe AbsHeap)
substituteAbsHeap s (AbsHeap (HeapMap xs)) = do
    m_xs' <- mapM substitute_entry xs
    case sequence m_xs' of
      Nothing -> return Nothing
      Just xs' -> return $ Just $ AbsHeap $ HeapMap xs'
    where
      substitute_entry (addr, code) =
        case lookupAbsValue addr s
        of Nothing -> subst_code addr
           Just (VarAV new_addr) -> subst_code new_addr
           Just _ -> return Nothing
        where
          subst_code new_addr = do
            code' <- substitute s code
            return $ Just (new_addr, code')

-------------------------------------------------------------------------------
-- Abstract environments

-- | An environment mapping program variables to abstract values.
--
--   All variables not explicitly stored in the map are mapped to 'topCode'.
newtype AbsEnv = AbsEnv (IntMap.IntMap AbsCode)

emptyAbsEnv :: AbsEnv
emptyAbsEnv = AbsEnv IntMap.empty

absEnvMembers :: AbsEnv -> [(Int, AbsCode)]
absEnvMembers (AbsEnv m) = IntMap.toList m

-- | Insert a variable's value in an environment
insertAbstractValue :: Var -> AbsCode -> AbsEnv -> AbsEnv
insertAbstractValue v c (AbsEnv m)
  | isTopCode c = AbsEnv m
  | otherwise   = AbsEnv (IntMap.insert (fromIdent $ varID v) c m)

-- | Look up the variable's value in an environment.
--   If its value is not stored there, it's assumed to be \'top\'.
lookupAbstractValue :: Var -> AbsEnv -> AbsCode
lookupAbstractValue v (AbsEnv m) =
  fromMaybe topCode $ IntMap.lookup (fromIdent $ varID v) m

-------------------------------------------------------------------------------
-- Abstract interpretation
        
-- | Apply an abstract function to arguments.
--
--   Application should only occur in a well-typed manner.  An error is raised
--   otherwise.
applyCode :: AbsCode -> [Type] -> [AbsCode] -> TypeEvalM AbsComputation
applyCode fun ty_args fields =
  case codeValue fun
  of TopAV   -> return TopAC
     VarAV _ -> return TopAC    -- Don't attempt to represent it precisely
     FunAV f -> applyAbsFun f ty_args fields
     _       -> internalError "applyCode: Type error detected"

-- | Apply an abstract function to arguments and compute the result.
--
--   The result may be to raise an exception or return a new abstract value.
applyAbsFun :: AbsFun -> [Type] -> [AbsCode] -> TypeEvalM AbsComputation
applyAbsFun (AbsFun ty_params params body) ty_args args
  | n_ty_args > n_ty_params =
      type_error
  | n_ty_args < n_ty_params && not (null args) =
      type_error
  | n_ty_args < n_ty_params && null args || 
    n_ty_args == n_ty_params && n_args < n_params = do
      -- Application, returning a new function.
      -- Substitute type arguments for parameters.
      let subst = AbsSubst type_subst value_subst arg_subst
      new_fun <- substitutePatMs subst excess_params $ \subst' excess_params' -> do
        body' <- substitute subst' body
        return $ AbsFun excess_ty_params excess_params' body'
      return $ ReturnAC (valueCode $ FunAV new_fun)

  | n_ty_args == n_ty_params && n_args >= n_params = do
      -- Application.  The function is applied and evaluated.
      let subst = AbsSubst type_subst value_subst arg_subst
      comp <- substitute subst body

      -- If there are no remaining arguments, application has finished
      if null excess_args
        then return comp
        -- Otherwise apply the result to the remaining arguments
        else interpretComputation comp $ \retval ->
             applyCode retval [] excess_args
  where
    n_ty_args = length ty_args
    n_ty_params = length ty_params
    n_args = length args
    n_params = length params

    -- Type parameters that are not bound to a type in this application
    excess_ty_params = drop (length ty_args) ty_params

    -- Value arguments that are not bound to a variable in this application
    excess_args = drop (length params) args

    -- Parameters that are bound to a value in this application
    bound_params = take (length args) params

    -- Parameters that are not bound to a value in this application
    excess_params = drop (length args) params

    type_subst =
      Substitute.fromList [(a, t) | (a ::: _, t) <- zip ty_params ty_args]

    arg_subst =
      IntMap.fromList [(fromIdent $ varID (patMVar p), codeValue c)
                      | (p, c) <- zip bound_params args]

    -- Values are not substituted.  If the result expression would mention a
    -- parameter, then substitution will produce a result that's not labeled
    -- with an expression.
    value_subst =
      IntMap.fromList [(fromIdent $ varID (patMVar p), Nothing)
                      | p <- bound_params]

    type_error = internalError "applyAbsFun: Type error detected"

-- | Construct an abstract value for a function
funValue :: [TyPat] -> [PatM] -> AbsComputation -> AbsCode
funValue typarams params body =
  -- If value of body is 'Top' or 'Return Top', then approximate the
  -- function as 'Top'.
  -- By approximating, we are forgetting that the function will
  -- /definitely not/ raise an exception when partially applied.
  -- When the value is 'Return Top', we are also forgetting that
  -- the function will definitely not raise an exception when fully
  -- applied.  That's okay because we have no way of utilizing that
  -- information.
  case body
  of TopAC -> topCode
     ReturnAC val | TopAV <- codeValue val -> topCode
     _ -> valueCode $ FunAV (AbsFun [b | TyPat b <- typarams] params body)

-- | Given a data value and its type, construct the value of the
-- corresponding initializer function.
--
-- The value is a one-parameter function returning a heap fragment.
initializerValue :: AbsCode -> Type -> TypeEvalM AbsCode
initializerValue data_value ty =
  initializerValueHelper (ReturnAC data_value) ty

-- | A helper function that handles exception-raising computations.
--   The computation that's passed as a parameter doesn't correspond to
--   a realizable program value.
initializerValueHelper :: AbsComputation -> Type -> TypeEvalM AbsCode
initializerValueHelper data_comp ty = do
  param <- newAnonymousVar ObjectLevel
  let param_type = varApp (coreBuiltin The_OutPtr) [ty]
      pattern = patM (param ::: param_type)
  computation <- interpretComputation data_comp $ \data_value ->
    return $ ReturnAC $ valueCode $ HeapAV $ AbsHeap (HeapMap [(param, data_value)])
  return $ funValue [] [pattern] computation

-- | Compute the value produced by a data constructor application.
--
--   Bare fields are constructed from initializer functions.  To get
--   the field values, the functions are each applied to a nonce
--   parameter representing the address of the constructor field.
--   For other fields, the argument value is exactly the field value.
interpretCon :: ConInst -> [AbsCode] -> TypeEvalM AbsComputation
interpretCon con fields =
  case con
  of VarCon op _ _ -> do
       -- Look up field kinds
       tenv <- getTypeEnv
       let Just (data_type, dcon_type) = lookupDataConWithType op tenv
       let field_kinds = dataConFieldKinds tenv dcon_type
       when (length field_kinds /= length fields) type_error
       
       -- Compute values
       field_computations <-
         zipWithM compute_initializer_value field_kinds fields
       
       -- Compute the data value.  If it's a bare object, the result doesn't
       -- represent a real value; we have to convert it to an initializer.
       data_comp <- sequenceComputations field_computations $ \field_values ->
         return $ ReturnAC $ valueCode (datacon_value field_values)

       -- If it's a bare object, create an initializer function value
       case dataTypeKind data_type of
         BareK -> do
           (_, con_type) <- conType con
           code <- initializerValueHelper data_comp con_type
           return $ ReturnAC code
         _ -> return data_comp
         
     -- A tuple contains no bare fields, so it's simpler to create
     TupleCon ty_args
       | length fields /= length ty_args ->
           type_error
       | otherwise ->
           return $ ReturnAC $ valueCode (datacon_value fields)
  where
    type_error :: TypeEvalM a
    type_error = internalError "constructorDataValue: Type error detected"
    
    datacon_value field_values = DataAV (AbsData con field_values)

    compute_initializer_value BareK f = interpretInitializer f
    compute_initializer_value BoxK f  = return (ReturnAC f)
    compute_initializer_value ValK f  = return (ReturnAC f)
    compute_initializer_value _    _  =
      internalError "constructorDataValue: Unexpected field kind"

-- | Interpret a data constructor application that is certain not to raise
--   an exception.
interpretConAsValue :: ConInst -> [AbsCode] -> TypeEvalM AbsCode
interpretConAsValue cinst fields = do
  comp <- interpretCon cinst fields
  case comp of
    TopAC -> return topCode
    ReturnAC c -> return c
    ExceptAC -> internalError "interpretConAsValue: Not a value"

-- | Compute the value produced by an initializer function
interpretInitializer :: AbsCode -> TypeEvalM AbsComputation
interpretInitializer code = do
  -- Create a new variable to stand for the location where the result will
  -- be written
  out_var <- newAnonymousVar ObjectLevel
  
  -- Run the value and inspect its result
  result <- applyCode code [] [valueCode $ VarAV out_var]
  interpretComputation result $ \retval ->
    case codeValue retval
    of HeapAV (AbsHeap (HeapMap m)) ->
         case lookup out_var m
         of Just value -> return $ ReturnAC value

            -- Can this happen normally?
            Nothing -> return $ ReturnAC topCode
       TopAV -> return $ ReturnAC topCode
       _ -> internalError "interpretInitializer: Type error detected"

-- | Compute the value of a constant value
interpretConstant :: Constant Mem -> AbsCode
interpretConstant c = interpret_exp $ constExp c
  where
    interpret_exp expression =
      case fromExpM expression
      of VarE _ v -> valueCode $ VarAV v
         LitE _ l -> valueCode $ LitAV l
         ConE _ con args ->
           let args_values = map interpret_exp args
           in valueCode $ DataAV $ AbsData con args_values
         AppE _ _ _ _ ->
           -- This must be a value or boxed expression.
           -- Allow this expression to be inlined.
           -- Note that work may be duplicated by inlining.
           labelCode expression topCode
         _ ->
           internalError "interpretConstant: Unexpected expression"

-- | Compute the value of a case scrutinee, given that it matched a pattern
--   in a case alternative.
scrutineeDataValue :: DeConInst -> [PatM] -> TypeEvalM AbsCode
scrutineeDataValue decon params = do
  let con = case decon
            of TupleDeCon ts -> TupleCon ts
               VarDeCon op ty_args ex_types ->
                 VarCon op ty_args [VarT v | v ::: _ <- ex_types]
      field_values = map pattern_field params
  return $ valueCode $ DataAV (AbsData con field_values)
  where
    pattern_field pat = valueCode $ VarAV (patMVar pat)

-------------------------------------------------------------------------------
-- Concretization

-- | Create an expression whose result has the given abstract value, where
--   the abstract value has the given type.
concretize :: Type -> AbsCode -> TypeEvalM (Maybe ExpM)
concretize ty e = runMaybeT (concretize' ty e)

concretize' ty e
  | Just exp <- codeTrivialExp e = return exp
  | otherwise =
      case codeValue e
      of DataAV dv -> concretizeData dv
         FunAV f   -> concretizeFun ty f
         HeapAV hp -> concretizeHeap hp
         _         -> mzero

-- | Try to create a concrete expression whose value is the value of this 
--   data constructor application.  For each bare field, create a constructor
--   application or \'copy\' function call.  For each other field, use the
--   field's value.
concretizeData :: AbsData -> MaybeT TypeEvalM ExpM
concretizeData data_value@(AbsData con fs) = do
  -- Ensure that the data value is not a bare data value.
  -- It's an error to attempt to concretize a bare value.
  tenv <- getTypeEnv
  when (bad_data_kind tenv con) $
    internalError "concretize: Cannot concretize values of kind 'bare'"

  concretizeDataConApp data_value
  where
    bad_data_kind tenv (VarCon op _ _) =
      let Just (data_type, dcon_type) = lookupDataConWithType op tenv
      in dataTypeKind data_type == BareK
    
    bad_data_kind tenv (TupleCon _) = False

-- | Concretize a data constructor application.
--   The result is either a data value or an initializer function.
concretizeDataConApp (AbsData con fs) = do
  -- Determine field kinds and types
  tenv <- getTypeEnv
  (field_types, _) <- conType con
  let field_kinds = conFieldKinds tenv con

  -- Concretize each field and create a constructor application
  field_exps <- sequence $ zipWith3 concretize_field field_kinds field_types fs
  return $ conE defaultExpInfo con field_exps
  where
    concretize_field BareK ty f = do
      -- Create and concretize an initializer value
      let init_type = varApp (coreBuiltin The_OutPtr) [ty] `FunT`
                      VarT (coreBuiltin The_Store)
      concretize' init_type =<< lift (initializerValue f ty)

    concretize_field BoxK ty f = concretize' ty f
    concretize_field ValK ty f = concretize' ty f

concretizeFun :: Type -> AbsFun -> MaybeT TypeEvalM ExpM
concretizeFun fun_type (AbsFun ty_params params body) =
  case body
  of TopAC -> mzero             -- Unknown behavior
     ReturnAC code ->
       -- Construct a function expression
       assumeBinders ty_params $ assumePatMs params $ do
         body_exp <- concretize' return_type code
         return $ make_function body_exp
     ExceptAC ->
       -- Construct a function that raises an exception
       let exception = ExpM $ ExceptE defaultExpInfo return_type
       in return $ make_function exception
  where
    return_type = unpackFunctionType fun_type ty_params params
    make_function e =
      ExpM $ LamE defaultExpInfo $
      FunM $ Fun defaultExpInfo (map TyPat ty_params) params return_type e

unpackFunctionType fun_type ty_params params =
  do_typarams Rename.empty fun_type ty_params params
  where
    -- Extract type arguments.  Rename the function type so that type
    -- variables match the given type parameters.
    do_typarams rn fun_type ((b ::: _):ty_params) params =
      case fun_type
      of AllT (a ::: _) range ->
           do_typarams (Rename.extend a b rn) range ty_params params
         _ -> type_error

    do_typarams rn fun_type [] params =
      do_params rn fun_type params

    -- Drop parameter types; we don't need them
    do_params rn fun_type (param : params) =
      case fun_type
      of FunT _ range -> do_params rn range params
         _ -> type_error

    -- Get the return type
    do_params rn fun_type [] = Rename.rename rn fun_type

    type_error = internalError "concretizeFun: Type error detected"

-- | Concretize a heap map.  For each entry in the map, write to the heap.
concretizeHeap :: AbsHeap -> MaybeT TypeEvalM ExpM
concretizeHeap (AbsHeap (HeapMap [(addr, val)])) =
  concretizeHeapItem addr val

concretizeHeap _ =
  -- Support for multiple heap contents have not been implemented
  internalError "concretizeHeap: Not implemented for this value"

concretizeHeapItem :: Var -> AbsCode -> MaybeT TypeEvalM ExpM
concretizeHeapItem addr val
  | Just exp <- codeTrivialExp val =
      -- Not implemented.  The right thing to do is copy the value to the 
      -- destination.  We need the type in order to call 'copy'.
      internalError "concretizeHeapItem: Not implemented"

  | DataAV data_value <- codeValue val = do
      -- Consruct this value at the address
      initializer <- concretizeDataConApp data_value
      let out_ptr = ExpM $ VarE defaultExpInfo addr
      return $ ExpM $ AppE defaultExpInfo initializer [] [out_ptr]

  | TopAV <- codeValue val = mzero

  -- Only data and variables should appear here
  | otherwise = internalError "concretizeHeapItem: Unexpected abstract value"

-------------------------------------------------------------------------------

-- | Given a proposition, get substitutions that can be performed if the
--   proposition is true or false.
absPropSubstitutions :: AbsProp -> (SFRename.Subst, SFRename.Subst)
absPropSubstitutions prop =
  case get_bindings prop
  of (b1, b2) -> (make_subst b1, make_subst b2)
  where
    make_subst s = SFRename.Subst Substitute.empty (SFRename.fromListV s)

    -- Get the bindings implied by this proposition.
    -- The return value is (if_true, if_false).
    get_bindings :: AbsProp
                 -> ([(Var, SFRename.ValAss)], [(Var, SFRename.ValAss)])
    get_bindings (AbsValueProp var value) =
      case codeTrivialExp value
      of Just trivial_value ->
           return_true (var, SFRename.SubstitutedVar trivial_value)
         Nothing ->
           mempty
    get_bindings (AbsConjunction p1 p2) =
      get_bindings p1 `mappend` get_bindings p2

    get_bindings AbsAnyProp = mempty

    return_true x = ([x], [])
