{-| Abstract values.
    This module replaces the old "SystemF.Simplifier.KnownValue".

Most of the simplification performed by the simplifier relies on knowing some
approximation of the run-time value of an expresion or a variable.  The
'AbsValue' data type is how we store this information.

A data value that's in the correct representation for a @case@ statement is
represented by a 'DataAV' term.
-}

module SystemF.Simplifier.AbsValue
       (-- * Abstract values
        AbsCode,
        topCode,
        valueCode,
        labelCode,
        codeExp,
        codeTrivialExp,
        codeValue,
        AbsValue(..),
        funValue,
        scrutineeDataValue,
        AbsComputation(..),
        
        -- * Interpretation
        applyCode,
        constructorDataValue,

        -- * Environments of abstract values
        AbsEnv,
        emptyAbsEnv,
        insertAbstractValue,
        lookupAbstractValue
        )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import qualified Data.IntMap as IntMap

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.Supply
import SystemF.Syntax
import SystemF.MemoryIR
import qualified SystemF.Rename as SFRename
import SystemF.TypecheckMem
import Type.Environment
import Type.Eval
import Type.Type
import Type.Substitute(TypeSubst,
                       SubstitutionMap(..), Substitutable(..),
                       substitute, freshen)
import qualified Type.Substitute as Substitute

renameMany :: (st -> a -> (st -> a -> b) -> b)
           -> st -> [a] -> (st -> [a] -> b) -> b
renameMany f rn (x:xs) k =
  f rn x $ \rn' x' -> renameMany f rn' xs $ \rn'' xs' -> k rn'' (x':xs')

renameMany _ rn [] k = k rn []

-- | An abstract value labeled with a piece of code.
--
--   The label retrieved with 'codeExp' is an expression that is exactly
--   equal to the abstract value.  At the discretion of the simplifier,
--   this expression may be inlined in place of the abstract value.
--
--   If the value is a 'LitAV' or 'VarAV', the label is not explicitly
--   stored.
--   Calling 'codeExp' will return an expression in those cases.
data AbsCode =
  AbsCode { _codeLabel :: !(Maybe ExpM)
          , _codeValue :: !AbsValue
          }

-- | The least precise 'AbsCode' value.
topCode :: AbsCode
topCode = AbsCode Nothing TopAV

-- | Create an 'AbsCode' from an 'AbsValue'.  The created code is not labeled
--   with an expression.
valueCode :: AbsValue -> AbsCode
valueCode v = AbsCode Nothing v

-- | Attach a label to an 'AbsCode', to be retrieved with 'codeExp'.
labelCode :: ExpM -> AbsCode -> AbsCode
labelCode lab code = code {_codeLabel = Just lab}

-- | Convert an 'AbsCode' to an expression if possible.
codeExp :: AbsCode -> Maybe ExpM
codeExp code =
  case _codeValue code
  of LitAV l -> Just $ ExpM (LitE defaultExpInfo l)
     VarAV v -> Just $ ExpM (VarE defaultExpInfo v)
     _ -> case _codeLabel code
          of Just lab -> Just lab
             Nothing  -> Nothing

-- | Convert an 'AbsCode' to an expression if it can be represented by a
--   trivial expression.
codeTrivialExp :: AbsCode -> Maybe ExpM
codeTrivialExp code =
  case codeExp code
  of Nothing -> Nothing
     Just exp -> 
       case exp
       of ExpM (LitE {}) -> Just exp
          ExpM (VarE {}) -> Just exp
          _ -> Nothing

codeValue :: AbsCode -> AbsValue
codeValue = _codeValue

data AbsValue =
    TopAV                       -- ^ Unknown value
  | VarAV !Var                  -- ^ A variable
  | LitAV !Lit                  -- ^ A literal
  | FunAV !AbsFun               -- ^ A function
  | DataAV !AbsData             -- ^ A fully applied constructor
  | HeapAV !AbsHeap             -- ^ A heap fragment

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

substituteTyPatM s (TyPatM binder) k =
  Substitute.substituteBinder (typeSubst s) binder $ \ts' binder' ->
  k (s {typeSubst = ts'}) (TyPatM binder')

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

substituteAlt s (AltM (Alt (DeCInstM decon) params body)) =
  substituteDeConInst s decon $ \s' decon' ->
  substitutePatMs s' params $ \s'' params' -> do
    body' <- substituteExp s body
    return $ AltM (Alt (DeCInstM decon') params' body')

substituteAbsValue s value =
  case value
  of TopAV   -> return value
     VarAV v -> case lookupAbsValue v s
                of Nothing  -> return value
                   Just val -> return val
     LitAV _ -> return value
     FunAV f -> FunAV `liftM` substitute s f
     DataAV d -> DataAV `liftM` substitute s d
     HeapAV h -> HeapAV `liftM` substitute s h

instance Substitutable AbsCode where
  type Substitution AbsCode = AbsSubst
  
  substituteWorker s code = do
    label <- case _codeLabel code
             of Nothing -> return Nothing
                Just e -> liftTypeEvalM $ runMaybeT $ substituteExp s e
    value <- substitute s (_codeValue code)
    return $ AbsCode label value

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

instance Substitutable AbsHeap where
  type Substitution AbsHeap = AbsSubst
 
  substituteWorker s (AbsHeap (HeapMap xs)) = do
    xs' <- mapM substitute_entry xs
    return $ AbsHeap $ HeapMap xs'
    where
      substitute_entry ((), code) = do
        code' <- substitute s code
        return ((), code')

-------------------------------------------------------------------------------
-- Abstract environments

-- | An environment mapping program variables to abstract values
newtype AbsEnv = AbsEnv (IntMap.IntMap AbsCode)

emptyAbsEnv :: AbsEnv
emptyAbsEnv = AbsEnv IntMap.empty

insertAbstractValue :: Var -> AbsCode -> AbsEnv -> AbsEnv
insertAbstractValue v c (AbsEnv m) =
  AbsEnv (IntMap.insert (fromIdent $ varID v) c m)

lookupAbstractValue :: Var -> AbsEnv -> Maybe AbsCode
lookupAbstractValue v (AbsEnv m) = IntMap.lookup (fromIdent $ varID v) m

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
      comp <- substitutePatMs subst params $ \subst' params' -> do
        substitute subst' body

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
funValue :: [TyPatM] -> [PatM] -> AbsComputation -> AbsValue
funValue typarams params body =
  FunAV (AbsFun [b | TyPatM b <- typarams] params body)

-- | Compute the value produced by a data constructor application.
--
--   Bare fields are constructed from initializer functions.  To get
--   the field values, the functions are each applied to a nonce
--   parameter representing the address of the constructor field.
--   For other fields, the argument value is exactly the field value.
constructorDataValue :: ConInst -> [AbsCode] -> TypeEvalM AbsComputation
constructorDataValue con fields =
  case con
  of VarCon op _ _ -> do
       -- Look up field kinds
       tenv <- getTypeEnv
       let Just dcon_type = lookupDataCon op tenv
       let field_kinds = dataConFieldKinds tenv dcon_type
       when (length field_kinds /= length fields) type_error
       
       -- Compute values
       field_computations <-
         zipWithM compute_initializer_value field_kinds fields
       sequenceComputations field_computations $ \field_values ->
         return $ ReturnAC $ AbsCode Nothing (datacon_value field_values)
         
     -- A tuple contains no bare fields, so it's simpler to create
     TupleCon ty_args
       | length fields /= length ty_args ->
           type_error
       | otherwise ->
           return $ ReturnAC $ AbsCode tuple_label (datacon_value fields)
  where
    type_error :: TypeEvalM a
    type_error = internalError "constructorDataValue: Type error detected"
    
    datacon_value field_values = DataAV (AbsData con field_values)

    compute_initializer_value BareK f = initializerValue f
    compute_initializer_value BoxK f  = return (ReturnAC f)
    compute_initializer_value ValK f  = return (ReturnAC f)
    compute_initializer_value _    _  =
      internalError "constructorDataValue: Unexpected field kind"

    -- Construct a tuple expression
    tuple_label = do
      field_labels <- mapM codeExp fields
      return $ conE defaultExpInfo con field_labels

-- | Compute the value produced by an initializer function
initializerValue :: AbsCode -> TypeEvalM AbsComputation
initializerValue code = do
  -- Create a new variable to stand for the location where the result will
  -- be written
  out_var <- newAnonymousVar ObjectLevel
  
  -- Run the value and inspect its result
  result <- applyCode code [] [valueCode $ VarAV out_var]
  interpretComputation result $ \retval ->
    case codeValue retval
    of HeapAV (AbsHeap (HeapMap m)) ->
         case lookup () m
         of Just value -> return $ ReturnAC value
       _ -> internalError "initializerValue: Type error detected"

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

