{-| The argument flattening transformation makes parameter passing more
    efficient by changing the format in which function arguments are passed.

Functions are replaced by a worker/wrapper pair.  The worker function
takes arguments in a flattened form, repacks them, and runs the function body.
The wrapper function takes arguments
in the original, packed form, and unpacks them for the worker.

After argument unpacking, the compiler will inline wrapper functions where
possible to eliminate argument packing in callers, and perform case elimination
to eliminate repacking inside workers.
-}

{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}
{-# OPTIONS_HADDOCK ignore-exports #-}
module SystemF.ArgumentFlattening(flattenArguments, flattenLocals)
where

import Prelude hiding (mapM, sequence)

import Control.Monad.Reader hiding(mapM, forM, sequence)
import Control.Monad.State hiding(mapM, sequence)
import qualified Data.IntMap as IntMap
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Traversable
import qualified Data.Set as Set
import Debug.Trace

import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Common.PrecDoc
import Builtins.Builtins
import SystemF.Build
import SystemF.Demand
import SystemF.Floating
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import SystemF.Rename
import SystemF.ReprDict
import SystemF.TypecheckMem
import Type.Compare
import Type.Environment
import Type.Eval
import Type.Rename
import Type.Type
import Globals
import GlobalVar

-- * Utility functions

-- | If the parameter is a type constructor that has a single data constructor,
--   return its type and data constructors
fromProductTyCon :: TypeEnv -> Var -> Maybe DataConType
fromProductTyCon tenv ty_op =
  case lookupDataType ty_op tenv
  of Nothing -> Nothing
     Just data_type ->
       case dataTypeDataConstructors data_type
       of [con] ->
            case lookupDataCon con tenv
            of Just dcon_type -> Just dcon_type
               Nothing -> internalError "fromProductTyCon"
          _ -> Nothing

fromOutPtrType :: Type -> Type
fromOutPtrType t =
  case fromVarApp t
  of Just (op, [arg]) | op `isPyonBuiltin` the_OutPtr -> arg
     _ -> internalError "fromOutPtrType: Not an output pointer"

-- | Bind a variable to a value.
--
--   Creates either a let expression or a case-of-boxed expression, depending
--   on the data type that will be bound.
bindVariable :: TypeEnv -> Binder -> ExpM -> ExpM -> ExpM
bindVariable tenv binder rhs body =
  case toBaseKind $ typeKind tenv (binderType binder)
  of BareK -> letViaBoxed binder rhs body
     ValK  -> ExpM $ LetE defaultExpInfo (patM binder) rhs body
     BoxK  -> ExpM $ LetE defaultExpInfo (patM binder) rhs body

-------------------------------------------------------------------------------
-- * The argument flattening monad

-- | Reader environment used during argument flattening and local variable
--   flattening.
data AFLVEnv a =
  AFLVEnv
  { afVarSupply :: {-# UNPACK #-}!(IdentSupply Var)
  , afTypeEnv :: TypeEnv
  , afDictEnv :: MkDictEnv
  , afIntIndexEnv :: IntIndexEnv
  , afOther :: a
  }

-- | The monad for argument and local variable flattening
newtype AFMonad e a =
  AF {unAF :: ReaderT (AFLVEnv e) IO a} deriving(Monad, MonadIO)

-- | The argument flattening monad
type AF = AFMonad ()

instance Supplies (AFMonad e) (Ident Var) where
  fresh = AF $ ReaderT $ \env -> supplyValue $ afVarSupply env

liftFreshVarAF :: FreshVarM a -> AFMonad e a
liftFreshVarAF m = AF $ ReaderT $ \env -> runFreshVarM (afVarSupply env) m

instance TypeEnvMonad (AFMonad e) where
  getTypeEnv = AF $ asks afTypeEnv
  assume v t m = AF $ local insert_type $ unAF m
    where
      insert_type env = env {afTypeEnv = insertType v t $ afTypeEnv env}

instance ReprDictMonad (AFMonad e) where
  getVarIDs = AF $ asks afVarSupply
  getDictEnv = AF $ asks afDictEnv
  getIntIndexEnv = AF $ asks afIntIndexEnv
  localDictEnv f m =
    AF $ local (\env -> env {afDictEnv = f $ afDictEnv env}) $ unAF m
  localIntIndexEnv f m =
    AF $ local (\env -> env {afIntIndexEnv = f $ afIntIndexEnv env}) $ unAF m

instance EvalMonad (AFMonad e) where
  liftTypeEvalM m = AF $ ReaderT $ \env -> do
    runTypeEvalM m (afVarSupply env) (afTypeEnv env)

assumeTyPat :: EvalMonad m => TyPatM -> m a -> m a
assumeTyPat (TyPatM binder) m = assumeBinder binder m

assumeTyPats :: EvalMonad m => [TyPatM] -> m a -> m a
assumeTyPats typats m = foldr assumeTyPat m typats

assumePat :: (EvalMonad m, ReprDictMonad m) =>
             PatM -> m a -> m a
assumePat pat m = assumeBinder (patMBinder pat) $ saveReprDictPattern pat m

assumePats :: (EvalMonad m, ReprDictMonad m) =>
              [PatM] -> m a -> m a
assumePats pats m = foldr assumePat m pats

assumeDef :: TypeEnvMonad m => Def Mem -> m a -> m a
assumeDef d m = assume (definiendum d) (functionType $ definiens d) m

assumeDefGroup :: TypeEnvMonad m => DefGroup (Def Mem) -> m a -> m a
assumeDefGroup dg m = foldr assumeDef m $ defGroupMembers dg

-- | Apply the transformation to each expression in tail position.
--   Look through let, letfun, and case statements.
mapOverTailExps :: (ReprDictMonad m, TypeEnvMonad m) =>
                   (ExpM -> m ExpM) -> ExpM -> m ExpM
mapOverTailExps f expression =
  case fromExpM expression
  of LetE inf binder rhs body -> do
       body' <- assumePat binder $ mapOverTailExps f body
       return $ ExpM $ LetE inf binder rhs body'
     LetfunE inf defs body -> do
       body' <- assumeDefGroup defs $ mapOverTailExps f body
       return $ ExpM $ LetfunE inf defs body'
     CaseE inf scr alts -> do
       alts' <- mapM map_alt alts
       return $ ExpM $ CaseE inf scr alts'
     _ -> f expression
  where
    map_alt (AltM alt) = do
      assumeTyPats (getAltExTypes alt) $ assumePats (altParams alt) $ do
        body <- mapOverTailExps f $ altBody alt
        return $ AltM (alt {altBody = body})

-------------------------------------------------------------------------------
-- * Argument flattening types 

-- | A decomposition of a value into components
data Decomp =
    -- | Value is unchanged
    IdDecomp
    -- | Value is deconstructed
  | DeconDecomp !MonoCon FlatArgs
    -- | Value is dead
    --
    --   An expression is provided to fabricate a value of the correct type.
    --   The exact value doesn't matter since it's dead.
  | DeadDecomp ExpM

pprDecomp :: Decomp -> Doc
pprDecomp IdDecomp = text "U"
pprDecomp (DeconDecomp (MonoCon con ty_args ex_types) fields) =
  text "D{" <> app <> text "}"
  where
    ty_args_doc = [pprTypePrec t ?+ appPrec | t <- ty_args]
    ex_types_doc = map (pprTyPat . TyPatM) ex_types
    fields_doc = map pprFlatArg fields
    app = sep (pprVar con : ty_args_doc ++ ex_types_doc ++ fields_doc)

pprDecomp (DeconDecomp (MonoTuple _) fields) =
  -- Tuples should not be decomposed
  text "ERROR"

pprDecomp (DeadDecomp e) = text "0" <+> braces (pprExp e)

isIdDecomp IdDecomp = True
isIdDecomp _ = False

-- | Determine whether all decomposed items are values or boxed objects.
--   If so, then it's possible to unpack a return value with this type.
unpacksToAValue :: TypeEnv -> FlatRet -> Bool
unpacksToAValue tenv (FlatRet ty IdDecomp) =
  case toBaseKind $ typeKind tenv ty
  of ValK -> True
     BoxK -> True
     _    -> False

unpacksToAValue tenv (FlatRet _ (DeconDecomp (MonoCon _ _ ex_types) fs)) =
  null ex_types && and [unpacksToAValue tenv (flatArgReturn f) | f <- fs]

unpacksToAValue _ (FlatRet _ (DeadDecomp _)) = True

-- | Flatten a decomposition.  Decomposed type parameters and fields are
--   transformed and collected by a monoid.
flattenDecomp :: Monoid a =>
                 (TyPatM -> a)  -- ^ Extract value from a type parameter
              -> (PatM -> a)    -- ^ Extract value from a field
              -> a              -- ^ Value of an identity decomposition
              -> Decomp         -- ^ Decomposition to flatten
              -> a              -- ^ Flattened value
flattenDecomp typaram field x decomp = go x decomp
  where
    go x IdDecomp = x
    go x (DeadDecomp _) = mempty
    go x (DeconDecomp (MonoCon _ _ ex_types) fields) =
      mconcat $ map (typaram . TyPatM) ex_types ++
                [go (field p) d | FlatArg p d <- fields]

-- | Flatten a decomposition that doesn't introduce type parameters
flattenMonoDecomp :: Monoid a =>
                     (PatM -> a) -- ^ Extract value from a field
                  -> a           -- ^ Value of an identity decomposition
                  -> Decomp      -- ^ Decomposition to flatten
                  -> a           -- ^ Flattened value
flattenMonoDecomp field x decomp = flattenDecomp typaram field x decomp
  where
    typaram _ = internalError "flattenMonoDecomp: Unexpected existential type"

-- | A flattened binding, for a local variable or function parameter.
--
--   The flattened argument specifies the
--   original variable binding, the flattened variable binding(s), and how 
--   to convert from one to the other.
data FlatArg =
  FlatArg { faPattern        :: !PatM   -- ^ The original function parameter
          , faTransformation :: !Decomp -- ^ How the parameter is decomposed
          }

type FlatArgs = [FlatArg]

pprFlatArg (FlatArg pat decomp) = hang (brackets (pprDecomp decomp)) 8 pat_doc
  where
    pat_doc = pprVar (patMVar pat) <+> text ":" <+> pprType (patMType pat)

isIdArg a = isIdDecomp (faTransformation a)

-- | A flattened return.
--
--   The flattened return specifies the original return type, the flattened
--   return type, and how to convert from one to the other.  If the return
--   type is bare, then the return type describes an initializer function;
--   otherwise, it describes a returned value or returned boxed object.
--
--   A return value may be flattened to a sequence of values.
--   Returned values containing existential types cannot be flattened.
--   If flattening produces one value, its type is the flattened return type. 
--   If it produces many values, they are aggregated into an unboxed tuple.
--   The unboxed tuple type is the flattened return type.
data FlatRet =
  FlatRet { frType :: Type      -- ^ The original return type
          , frDecomp :: Decomp  -- ^ How the return value is decomposed
          }

isIdRet (FlatRet _ IdDecomp) = True 
isIdRet _ = False

flatArgReturn :: FlatArg -> FlatRet
flatArgReturn (FlatArg pat decomp) = FlatRet (patMType pat) decomp

-- | Get the packed argument list from a sequence of flattened parameters
packedParameters :: FlatArgs -> [PatM]
packedParameters xs = map packedParameter xs

-- | Get the packed argument from a flattened parameter
packedParameter :: FlatArg -> PatM
packedParameter = faPattern

-- | Get the flattened argument list from a flattened parameter
flattenedParameter :: FlatArg -> ([TyPatM], [PatM])
flattenedParameter (FlatArg pat decomp) =
  flattenDecomp put_typat put_pat (put_pat pat) decomp
  where
    put_typat p = ([p], [])
    put_pat p = ([], [p])

-- | Get the flattened argument list from a sequence of flattened parameters
flattenedParameters :: FlatArgs -> ([TyPatM], [PatM])
flattenedParameters xs = mconcat $ map flattenedParameter xs

-- | Get the flattened parameter values from from a sequence of flattened
--   parameters.  Each value is a type variable or variable expression.
flattenedParameterValues :: FlatArgs -> ([TypM], [ExpM])
flattenedParameterValues xs =
  case flattenedParameters xs
  of (tps, ps) -> ([TypM (VarT a) | TyPatM (a ::: _) <- tps],
                   [ExpM $ VarE defaultExpInfo (patMVar p) | p <- ps])

-- | Get the flattened return type.  Only valid if
--   @flattenedReturnsBySideEffect flat_ret == False@.
flattenedReturnType :: TypeEnv -> FlatRet -> TypM
flattenedReturnType tenv flat_ret =
  let flat_type = frType flat_ret
      flat_decomp = frDecomp flat_ret
      flattened_types =
        flattenMonoDecomp (\p -> [patMType p]) [flat_type] flat_decomp
  in case flattened_types
     of [t] -> TypM t
        ts  -> TypM $ unboxedTupleType tenv flattened_types

-- | Get the parameter list to use to bind the flattened return values
flattenedReturnParameters :: FlatRet -> Maybe [PatM]
flattenedReturnParameters flat_ret =
  flattenMonoDecomp (\p -> Just [p]) Nothing $ frDecomp flat_ret

-- | Get the flattened return value expression for a return value that has
--   been decomposed.  The expression is either a tuple or a single variable,
--   containing bound return value patterns.
--   It's an error to call this function if the return value does not specify
--   to decompose.
flattenedReturnValue :: FlatRet -> ExpM
flattenedReturnValue flat_ret = 
  case flattenMonoDecomp (\p -> Just [var_exp p]) Nothing $ frDecomp flat_ret
  of Just [e] -> e
     Just es  -> ExpM $ UTupleE defaultExpInfo es
     Nothing -> internalError "flattenedReturnValue"
  where
    var_exp pat = ExpM $ VarE defaultExpInfo (patMVar pat)

-- | Given the variable bindings returned by 'flattenedReturnParameters', 
--   and a flattened return value, bind the flattened return variables.
bindFlattenedReturn :: ExpInfo -> [PatM] -> ExpM -> ExpM -> ExpM
bindFlattenedReturn inf [p] source_exp body =
  -- Single value.  Assign the expression result to the pattern variable.
  ExpM $ LetE inf p source_exp body

bindFlattenedReturn inf patterns source_exp body =
  -- Multiple or zero return values.  Deconstruct the
  -- expression result with a case statement, then repack.
  ExpM $ CaseE defaultExpInfo source_exp [AltM $ DeTuple patterns body]

-------------------------------------------------------------------------------
-- * Value packing and unpacking transformations

-- | Generate code to flatten a parameter in the context of an expression.
--
--   The parameter is assumed to be bound in the surrounding code.  The
--   generated code deconstructs the parameter variable and binds its fields.
flattenParameter :: FlatArg -> ExpM -> ExpM
flattenParameter (FlatArg pat decomp) body =
  case decomp
  of IdDecomp -> body
     DeconDecomp mono_con fields ->
       let pattern_exp = ExpM $ VarE defaultExpInfo (patMVar pat)
           body' = flattenParameters fields body
           alt = altFromMonoCon mono_con (map faPattern fields) body'
       in ExpM $ CaseE defaultExpInfo pattern_exp [alt]
     DeadDecomp _ -> body

flattenParameters :: [FlatArg] -> ExpM -> ExpM
flattenParameters args e = foldr flattenParameter e args

packParametersWrite :: (ReprDictMonad m, EvalMonad m) => FlatArgs -> m [ExpM]
packParametersWrite (arg:args) = do
  e <- packParameterWrite arg
  es <- assumePat (faPattern arg) $ packParametersWrite args
  return (e : es)

packParametersWrite [] = return []

-- | Pack a parameter whose result will be written to a destination
--
--   TODO: Don't return the parameter expression.  It's always just the
--   pattern variable.
packParameterWrite :: (ReprDictMonad m, EvalMonad m) => FlatArg -> m ExpM
packParameterWrite (FlatArg pat flat_arg) = packParameterWrite' pat flat_arg
  
packParameterWrite' pat flat_arg =
  case flat_arg
  of IdDecomp -> copy_expr (patMType pat) (var_exp $ patMVar pat)
     DeconDecomp (MonoCon con types ex_types) fields ->
       assumeBinders ex_types $ do
         exps <- packParametersWrite fields
         
         -- Construct/initialize a value
         let op = var_exp con
         let ty_args = map TypM (types ++ [VarT a | a ::: _ <- ex_types])
         return $ ExpM $ AppE defaultExpInfo op ty_args exps

     DeadDecomp e -> return e
  where
    var_exp v = ExpM $ VarE defaultExpInfo v
    
    copy_expr ty src = do
       tenv <- getTypeEnv
       case toBaseKind $ typeKind tenv ty of
         BareK -> do
           -- Insert a copy operation
           dict <- getReprDict ty
           return $ ExpM $ AppE defaultExpInfo copy_op [TypM ty] [dict, src]
         _ ->
           return src
    
    copy_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_copy)

-- | Pack a parameter, so that the result is readable
packParametersRead :: (ReprDictMonad m, EvalMonad m) =>
                      FlatArgs -> m ([ExpM], ExpM -> ExpM)
packParametersRead (arg : args) = do
  (val, ctx) <- packParameterRead arg
  (vals, ctxs) <- assumePat (faPattern arg) $ packParametersRead args
  return (val : vals, ctx . ctxs)

packParametersRead [] = return ([], id)

-- | Pack a parameter
--
--   TODO: Don't return the parameter expression.  It's always just the
--   pattern variable.
packParameterRead :: (ReprDictMonad m, EvalMonad m) =>
                     FlatArg -> m (ExpM, ExpM -> ExpM)
packParameterRead (FlatArg pat flat_arg) =
  case flat_arg
  of IdDecomp ->
       return (var_exp $ patMVar pat, id)
     DeconDecomp (MonoCon con types ex_types) fields ->
       assumeBinders ex_types $ do
         exps <- packParametersWrite fields
         let op = var_exp con
         let ty_args = map TypM (types ++ [VarT a | a ::: _ <- ex_types])
         let packed = ExpM $ AppE defaultExpInfo op ty_args exps
         
         -- If this is a bare type, define a local variable with the
         -- packed parameter.  Otherwise, just assign a local variable.
         tenv <- getTypeEnv
         return (var_exp $ patMVar pat,
                 bindVariable tenv (patMBinder pat) packed)

     DeadDecomp e ->
       -- Assign the expression to a temporary variable
       return (var_exp $ patMVar pat,
               \body -> ExpM $ LetE defaultExpInfo pat e body)
  where
    var_exp v = ExpM $ VarE defaultExpInfo v

-- | Transform an expression's return value to flattened form.  Deconstruct
--   the return value into its component fields, then pack the
--   components into the correct form to return from the expression.
--
--   To deconstruct an expression, the expression and its decomposition are
--   processed together, structurally.
--
--   We try to cancel deconstructor decompositions ('DeconDecomp') with
--   constructor applications.  When canceling is successful, the
--   application is eliminated, and its fields are bound individually.
--   Otherwise a case statement is generated.
--
--   Deconstruction is sunk to the tail position of let, letrec, and
--   case statements by calling 'mapOverTailExps'.
flattenReturnWrite :: forall m. (EvalMonad m, ReprDictMonad m) =>
                      FlatRet -> ExpM -> m ExpM
flattenReturnWrite flat_ret orig_exp =
  case frDecomp flat_ret
  of IdDecomp -> 
       return orig_exp -- Expression is unchanged

     DeadDecomp {} ->
       err -- Return value is not allowed to be completely dead

     DeconDecomp mono_con flat_args ->
       -- Apply flattening transformation to all expressions in tail position
       deconReturn mono_con flat_args
       (flatten_args flat_args) (return flattened_value) orig_exp
  where
    err :: forall a. a
    err = internalError "flattenReturnWrite"

    -- Flatten each initializer expression.
    -- If there's only one initializer, it produces the entire result
    flatten_args [flat_field] [initializer] =
      flattenReturnWrite (flatArgReturn flat_field) initializer
    
    -- If there are multiple initializers, then unpack and repack their
    -- results
    flatten_args flat_fields initializers =
      flattenReturnFields (zip initializers flat_fields) flattened_value

    -- The 'FlatRet' parameter determines the flattened return value
    flattened_value = flattenedReturnValue flat_ret
 
-- | Deconstruct a return value according to the given pattern.
--   The deconstruction code is moved to tail position and constructor
--   applications are eliminated when possible.
--
--   If a constructor application can be matched and deconstructed,
--   the initializer expressions are used to construct the final expression.
--   Otherwise, the constructor's result is deconstructed, its fields are 
--   bound to the given 'FlatArgs' patterns, and code is generated to
--   deconstruct those patterns.
deconReturn :: (EvalMonad m, ReprDictMonad m) =>
               MonoCon            -- ^ Constructor to match against
            -> FlatArgs           -- ^ Fields to deconstruct
            -> ([ExpM] -> m ExpM) -- ^ Deconstruct initializers
            -> m ExpM             -- ^ Deconstruct values bound to patterns
            -> ExpM               -- ^ Expression to deconstruct
            -> m ExpM             -- ^ Deconstructor
deconReturn con_type dc_fields decon_initializers decon_patterns expression =
  mapOverTailExps decon_tail expression
  where
    decon_tail tail_exp = do
      tenv <- getTypeEnv
      
      -- Attempt to deconstruct the tail expression
      case con_type of
        MonoCon con decon_ty_args decon_ex_types ->
          case unpackDataConAppM tenv tail_exp of
            Just (dcon_type, ty_args, ex_args, fields) 
              | dataConCon dcon_type /= con ->
                  internalError "deconReturn: Unexpected data constructor"
              | not (null ex_args && null decon_ex_types) ->
                  internalError "deconReturn: Unexpected existential types"
              | otherwise ->
                  -- Eliminate the data constructor.
                  -- Continue processing with the initializers.
                  decon_initializers fields
            Nothing -> bind_and_deconstruct tail_exp

        MonoTuple _ ->
          case tail_exp
          of ExpM (UTupleE _ fields) -> decon_initializers fields
             _ -> bind_and_deconstruct tail_exp
          
    -- Unable to deconstruct the expression.  Bind the expression's result to 
    -- a variable, then deconstruct it.
    bind_and_deconstruct tail_exp = do
      consumer_exp <- decon_patterns

      -- Deconstruct the expression result
      let match = altFromMonoCon con_type (map faPattern dc_fields)
                  consumer_exp
          case_of scrutinee = ExpM $ CaseE defaultExpInfo scrutinee [match]

      -- Bind the expression result
      data_type <- monoConType con_type
      tenv <- getTypeEnv
      case toBaseKind $ typeKind tenv data_type of
        BareK -> deconstruct_writer data_type tail_exp case_of
        ValK  -> deconstruct_value tail_exp case_of
        BoxK  -> deconstruct_value tail_exp case_of

    -- Deconstruct the result of a writer expression.
    -- The result is bound to a local variable, then deconstructed to bind
    -- its fields to variables.
    deconstruct_writer data_type tail_exp case_of = do
      -- Run the write and bind its result to a new variable
      local_var <- newAnonymousVar ObjectLevel
      let var_exp = ExpM $ VarE defaultExpInfo local_var
      return $ letViaBoxed (local_var ::: data_type) tail_exp (case_of var_exp)
    
    -- Deconstruct a value.
    deconstruct_value tail_exp case_of = return $ case_of tail_exp

-- | Given a list of initializer expressions and argument flattening
--   specifications, flatten all initializer values.  All variables in the 
--   flattened arguments are bound.
flattenReturnFields :: (EvalMonad m, ReprDictMonad m) =>
                       [(ExpM, FlatArg)] -> ExpM -> m ExpM
flattenReturnFields fields e = foldM flatten_field e fields
  where
    flatten_field consumer (exp, arg) =
      flattenLocal (FlatLocal arg) exp consumer

-- | Flatten a local value.  The flattened values are bound to variables
--   in the context of a consumer expression.
--
--   When the return value is a bare object initializer, it is first bound to
--   a variable, then the variable is flattened.
--
--   The return value is flattened to a value or tuple using 'flattenReturn', 
--   then the result is bound to variables.
flattenLocal :: (EvalMonad m, ReprDictMonad m) =>
                FlatLocal -> ExpM -> ExpM -> m ExpM
flattenLocal (FlatLocal (FlatArg old_binder decomp)) expr consumer =
  case decomp
  of IdDecomp ->
       -- Only allowed for value or boxed objects.
       -- Bind the value to the pattern.
       return $ ExpM $ LetE defaultExpInfo old_binder expr consumer
     DeadDecomp _ ->
       -- The expression is not used
       return consumer
     DeconDecomp mono_con flat_args ->
       -- Deconstruct this value
       deconReturn mono_con flat_args
       (flatten_fields flat_args) (flatten_patterns flat_args) expr
  where
    flatten_fields flat_args initializers =
      flattenReturnFields (zip initializers flat_args) consumer
    
    flatten_patterns flat_args =
      return $ flattenParameters flat_args consumer

-- | Transform a flattened return value to packed form
packReturn :: (EvalMonad m, ReprDictMonad m) =>
              FlatRet -> ExpM -> m ExpM
packReturn (FlatRet _ IdDecomp) orig_exp = return orig_exp

packReturn (FlatRet _ (DeadDecomp {})) orig_exp = internalError "packReturn"

packReturn flat_ret orig_exp =
  case flattenedReturnParameters flat_ret
  of Nothing ->
       -- Return value is not decomposed at all
       case frDecomp flat_ret
       of IdDecomp     -> return orig_exp
          DeadDecomp e -> -- FIXME: This eliminates the source value. 
                          -- What if the source raised an exception?
                          return e
     Just patterns -> do
       -- Return value was deconstructed (DeconDecomp).
       -- Rebuild the data structure.
       repack_exp <-
         packParameterWrite' (internalError "packReturn") (frDecomp flat_ret)
       
       let inf = case orig_exp of ExpM e -> expInfo e
       return $! bindFlattenedReturn inf patterns orig_exp repack_exp

-------------------------------------------------------------------------------
-- * Decisions on how to flatten

-- | Decide how to flatten a function arguments
planParameters :: (ReprDictMonad m, EvalMonad m) =>
                  [PatM] -> m [FlatArg]
planParameters pats = mapM planParameter pats

-- | Decide how to flatten a function argument
planParameter :: (ReprDictMonad m, EvalMonad m) => PatM -> m FlatArg
planParameter pat =
  case specificity $ patMDmd pat
  of Used -> used_parameter

     -- Don't remove or flatten dictionary parameters
     _ | is_dictionary_pattern -> used_parameter

     Inspected -> do
       -- If data type has a single constructor, then deconstruct it.
       tenv <- getTypeEnv
       whnf_type <- reduceToWhnf (patMType pat)
       case fromVarApp whnf_type of
         Just (op, args)
           | Just data_con <- fromProductTyCon tenv op ->
               decon_decomp (dataConCon data_con) args Nothing
         _ -> id_decomp

     Decond (MonoCon op ty_args ex_types) spcs ->
       decon_decomp op ty_args (Just spcs)

     Decond (MonoTuple _) spcs ->
       -- Currently don't know how to unpack unboxed tuples
       used_parameter

     Unused -> do
       dead_expr <- deadValue (patMType pat)
       return $ FlatArg new_pat (DeadDecomp dead_expr)
  where
    used_parameter = do
      -- if pattern is a Stored type, then deconstruct it.
      -- Otherwise leave it unchanged.
      whnf_type <- reduceToWhnf (patMType pat)
      case fromVarApp whnf_type of
        Just (op, [arg])
          | op `isPyonBuiltin` the_Stored ->
              decon_decomp (pyonBuiltin the_stored) [arg] Nothing
        _ -> id_decomp
    
    is_dictionary_pattern =
      case fromVarApp $ patMType pat
      of Just (op, _) -> isDictionaryTypeCon op
         _ -> False

    -- Flattening alters the way that variables are demanded, so
    -- clear the demand information
    new_pat = setPatMDmd unknownDmd pat

    id_decomp = return $ FlatArg new_pat IdDecomp

    decon_decomp data_con args spcs = do
      d <- planDeconstructedValue data_con args spcs
      return $ FlatArg new_pat d

-- | Deconstruct a parameter into its component fields.
--
--   Specificity about the fields of the data value, if available, is used
--   to direct the deconstruction plan.  Types inside the specificity are
--   ignored.
planDeconstructedValue :: (ReprDictMonad m, EvalMonad m) =>
                          Var -> [Type] -> Maybe [Specificity]
                       -> m Decomp
planDeconstructedValue con ty_args maybe_fields = do
  tenv <- getTypeEnv
  case lookupDataCon con tenv of
    Just datacon_type -> do
      -- Instantiate the data constructor type
      (ex_params, field_types, _) <-
        instantiateDataConTypeWithFreshVariables datacon_type ty_args

      -- Create new parameters for each field
      let field_specificities = fromMaybe (repeat Used) maybe_fields
          field_info = zip field_types field_specificities
      field_plans <- foldr assumeBinder (plan_fields field_info) ex_params

      -- Construct the deconstruction plan
      return $ DeconDecomp (MonoCon con ty_args ex_params) field_plans

    _ -> internalError "planDeconstructedValue: Unknown data constructor"
  where
    plan_fields ((f_type, f_specificity):fs) = do
      -- Create a new pattern for this field
      v <- newAnonymousVar ObjectLevel
      let uses = case f_specificity
                 of Unused -> Dead
                    _ -> ManyUnsafe
          field_pattern = setPatMDmd (Dmd uses f_specificity) $
                          patM (v ::: f_type)

      -- Decide how to deconstruct
      f_plan <- planParameter field_pattern
      
      -- Process remaining fields
      fs_plans <- assume v f_type $ plan_fields fs
      return (f_plan : fs_plans)
    
    plan_fields [] = return []

-- | Construct an arbitrary value of the given type.  The value will not be
--   used in the program.
deadValue t = do
  tenv <- getTypeEnv
  case toBaseKind $ typeKind tenv t of
    ValK -> do
      whnf_t <- reduceToWhnf t
      case whnf_t of
        VarT v
          | v `isPyonBuiltin` the_int ->
              return $ ExpM $ LitE defaultExpInfo $ IntL 0 whnf_t
          | v `isPyonBuiltin` the_float ->
              return $ ExpM $ LitE defaultExpInfo $ FloatL 0 whnf_t
        _ -> internalError "deadValue: Not implemented for this type"
    BoxK ->
      return dead_box
    BareK ->
      return dead_bare
    _ -> internalError "deadValue: Unexpected kind"
  where
    dead_box = ExpM $ AppE defaultExpInfo dead_box_op [TypM t] []
    dead_bare = ExpM $ AppE defaultExpInfo dead_bare_op [TypM t] []
    dead_box_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_deadBox)
    dead_bare_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_deadRef)


planReturn :: (ReprDictMonad m, EvalMonad m) => TypM -> m FlatRet
planReturn (TypM ty) = do
  tenv <- getTypeEnv
  ty' <- reduceToWhnf ty
  case fromVarApp ty' of
    Just (op, args)
      | Just dcon_type <- fromProductTyCon tenv op -> do
          decon <- planDeconstructedValue (dataConCon dcon_type) args Nothing
          return $ FlatRet ty' decon
    _ -> return $ FlatRet ty' IdDecomp

-- | Determine how to decompose a return value based on its type.
--   The returned plan is for transforming a return-by-value function only.
planValueReturn :: (ReprDictMonad m, EvalMonad m) =>
                   TypM -> m PlanRet
planValueReturn ty = liftM PlanRetValue $ planReturn ty

-- | Determine how to decompose a return value based on its type.
--   The returned plan is for transforming an initializer function only.
planOutputReturn :: (ReprDictMonad m, EvalMonad m) =>
                    PatM -> m PlanRet
planOutputReturn pat = do
  tenv <- getTypeEnv
  flat_ret <- planReturn $ TypM $ patMType pat

  -- Only perform decomposition if everything was converted to a value
  let real_ret =
        if unpacksToAValue tenv flat_ret
        then flat_ret
        else FlatRet (frType flat_ret) IdDecomp
  return $ PlanRetWriter pat real_ret

-- | A flattened local variable.
--
--   An assignment to a flattened local variable is flattened in the 
--   same manner as a 'FlatRet'.  Unlike a 'FlatRet', however, the flattened
--   value can be assigned to a variable.
--   When re-packing local variables, the result is bound to the original  
--   pattern, the same as repacking a 'FlatArg'.
newtype FlatLocal = FlatLocal FlatArg

flatLocalReturn :: FlatLocal -> FlatRet
flatLocalReturn (FlatLocal arg) = flatArgReturn arg

-- | Given a flattening that should be applied to @e@, produce a
--   flattening to apply to the boxed object @boxed(e)@.  The boxed object  
--   is assumed to be bound to the given variable.  The new
--   flattening says to flatten the @boxed@ constructor, then perform the
--   original flattening.
flattenBoxedValue :: Var -> FlatLocal -> FlatLocal
flattenBoxedValue boxed_var (FlatLocal arg) =
  let arg_type = patMType $ faPattern arg
      boxed_type = varApp (pyonBuiltin the_Boxed) [arg_type]
      boxed_param = patM (boxed_var ::: boxed_type)
      
      boxed_mono_con = MonoCon (pyonBuiltin the_boxed) [arg_type] []
      boxed_decomp = DeconDecomp boxed_mono_con [arg]

  in FlatLocal (FlatArg boxed_param boxed_decomp)

-- | Create the original form of the local variable, using the flattened
--   variables
packLocal :: (ReprDictMonad m, EvalMonad m) => FlatLocal -> ExpM -> m ExpM
packLocal (FlatLocal flat_arg) consumer
  | isIdArg flat_arg =
      return consumer -- Local variable is already in scope
  | otherwise = do
      repack_exp <- packParameterWrite flat_arg
      return $
        ExpM $ LetE defaultExpInfo (faPattern flat_arg) repack_exp consumer

-- | Determine how to decompose a let-bound value based on its type.
--
--   The decomposition strategy is the same as for decomposing a return value.
planLocal :: (ReprDictMonad m, EvalMonad m) => PatM -> m FlatLocal
planLocal pat = do
  tenv <- getTypeEnv
  choose_flattening tenv =<< planReturn (TypM $ patMType pat)
  where
    id_plan = FlatLocal (FlatArg pat IdDecomp)

    choose_flattening tenv flat_ret = 
      case frDecomp flat_ret
      of IdDecomp -> return id_plan
         DeadDecomp _ -> return id_plan
         decomp@(DeconDecomp {})
           -- Don't decompose if some fields are bare references
           | not $ unpacksToAValue tenv flat_ret -> return id_plan
           | otherwise -> return $ FlatLocal (FlatArg pat decomp)

-------------------------------------------------------------------------------
-- * The argument flattening transformation on a function

-- | A return value specification in an argument flattening plan
data PlanRet =
    -- | A return plan for a function that originally returned by value
    PlanRetValue !FlatRet

    -- | A return plan for a function that originally returned by reference.
    --   If the decomposition is 'IdDecomp', then the flattened function 
    --   returns by reference.  Otherwise the flattened function returns by
    --   value.
  | PlanRetWriter !PatM !FlatRet

planRetFlatRet :: PlanRet -> FlatRet
planRetFlatRet (PlanRetValue fr) = fr
planRetFlatRet (PlanRetWriter _ fr) = fr

-- | Get the original return parameter and return
--   type of a return flattening plan.
--   They are used in the wrapper function.
planRetOriginalInterface :: PlanRet -> ([PatM], TypM)
planRetOriginalInterface (PlanRetValue fr) = ([], TypM $ frType fr)
planRetOriginalInterface (PlanRetWriter p _) = ([p], TypM $ patMType p)

-- | Get the flattened return parameter and return type
--   of a return flattening plan.
--   They are used in the worker function.
planRetFlattenedInterface :: TypeEnv -> PlanRet -> ([PatM], TypM)
planRetFlattenedInterface _ (PlanRetValue fr) = ([], TypM $ frType fr)
planRetFlattenedInterface tenv (PlanRetWriter p fr) =
  case frDecomp fr
  of IdDecomp ->
       ([p], TypM $ varApp (pyonBuiltin the_IEffect) [frType fr])
     DeadDecomp {} ->
       -- Dead return values aren't handled currently
       internalError "planRetFlattenedInterface"
     DeconDecomp {} ->
       ([], flattenedReturnType tenv fr)

type PlanArg = FlatArg
type PlanArgs = FlatArgs

data FunctionPlan =
  FunctionPlan
  { originalTyParams :: [TyPatM]
  , flatParams       :: PlanArgs
  , flatReturn       :: PlanRet
  }

-- | True if the plan does not change how function parameters or returns
--   are passed
isIdPlan :: FunctionPlan -> Bool
isIdPlan p = all isIdArg (flatParams p) &&
             isIdRet (planRetFlatRet $ flatReturn p)

originalFunctionInterface :: FunctionPlan -> ([TyPatM], [PatM], TypM)
originalFunctionInterface p =
  let -- Output parameters and return types depend on whether the function
      -- returns by value
      (output_params, return_type) = planRetOriginalInterface $ flatReturn p

      -- Get a list of all original parameters
      input_params = packedParameters $ flatParams p
      params = input_params ++ output_params

  in (originalTyParams p, params, return_type)

flattenedFunctionInterface :: TypeEnv -> FunctionPlan
                           -> ([TyPatM], [PatM], TypM)
flattenedFunctionInterface tenv p =
  let (output_params, return_type) =
        planRetFlattenedInterface tenv $ flatReturn p

      -- Get flattened parameters
      (new_ty_params, input_params) = flattenedParameters $ flatParams p
      
      params = input_params ++ output_params
      ty_params = originalTyParams p ++ new_ty_params
  in (ty_params, params, return_type)

planFunction :: FunM -> AF FunctionPlan
planFunction (FunM f) = assumeTyPats (funTyParams f) $ do
  -- Partition parameters into input and output parameters
  tenv <- getTypeEnv
  let (input_params, output_params) = partition_parameters tenv $ funParams f

  params <- planParameters input_params

  -- There should be either one or zero output parameters
  ret <- case output_params
         of []  -> planValueReturn $ funReturn f
            [p] -> planOutputReturn p

  return $ FunctionPlan (funTyParams f) params ret
  where
    -- Separate the function parameters into input and output parameters.
    -- Output parameters must follow input parameters.
    partition_parameters tenv params = go id params 
      where
        go hd (p:ps) =
          case toBaseKind $ typeKind tenv (patMType p)
          of OutK -> (hd [], check_out_kinds (p:ps))
             _    -> go (hd . (p:)) ps

        go hd [] = (hd [], [])
        
        check_out_kinds ps
          | and [OutK == toBaseKind (typeKind tenv (patMType p)) | p <- ps] = ps
          | otherwise =
            internalError "planFunction: Cannot handle function parameters"

-- | Create a wrapper function.  The wrapper function unpacks function
--   parameters, calls the worker, an repacks the worker's results.
mkWrapperFunction :: FunctionPlan
                  -> Var        -- ^ Wrapper function name
                  -> Var        -- ^ Worker function name
                  -> AF (Def Mem)
mkWrapperFunction plan wrapper_name worker_name = do
  wrapper_body <- make_wrapper_body
  let (wrapper_ty_params, wrapper_params, wrapper_ret) = 
        originalFunctionInterface plan
      wrapper = FunM $ Fun { funInfo = defaultExpInfo
                           , funTyParams = wrapper_ty_params
                           , funParams = wrapper_params
                           , funReturn = wrapper_ret
                           , funBody = wrapper_body}
  return $ mkWrapperDef wrapper_name wrapper
  where
    make_wrapper_body = assumeTyPats (originalTyParams plan) $ do
      -- Call the worker function and re-pack its arguments
      body <- packReturn (planRetFlatRet $ flatReturn plan) worker_call
      
      -- Flatten function parameters
      return $ flattenParameters (flatParams plan) body

    -- A call to the worker function.  The worker function takes flattened 
    -- function arguments.
    worker_call =
      let orig_ty_params =
            [TypM (VarT a) | TyPatM (a ::: _) <- originalTyParams plan]
          (new_ty_params, params) = flattenedParameterValues (flatParams plan)
          ty_params = orig_ty_params ++ new_ty_params
          worker_e = ExpM $ VarE defaultExpInfo worker_name
      in ExpM $ AppE defaultExpInfo worker_e ty_params params

-- | Create a worker function.  The worker function takes unpacked arguments
--   and returns an unpacked return value.  The worker function body repacks
--   the arguments, runs the original function body, and unpacks its
--   return value.
mkWorkerFunction :: FunctionPlan
                 -> Var         -- ^ Worker function name
                 -> ExpM        -- ^ Original function body
                 -> AF (Def Mem)
mkWorkerFunction plan worker_name original_body = do
  worker_body <- create_worker_body
  tenv <- getTypeEnv
  let (worker_ty_params, worker_params, worker_ret) = 
        flattenedFunctionInterface tenv plan
      worker = FunM $ Fun { funInfo = defaultExpInfo
                          , funTyParams = worker_ty_params
                          , funParams = worker_params
                          , funReturn = worker_ret
                          , funBody = worker_body}
  return $ mkDef worker_name worker
  where
    create_worker_body = assumeTyPats (originalTyParams plan) $ do
      -- Repack the return value
      flat_body <-
        flattenReturnWrite (planRetFlatRet $ flatReturn plan) original_body

      -- Repack the parameters
      (_, param_context) <- packParametersRead $ flatParams plan
      return $ param_context flat_body

-------------------------------------------------------------------------------
-- * The argument flattening pass

-- | Argument flattening traverses the program and flattens parameters and  
--   returns in all function definitions.  Flattening is controlled by type
--   and demand information.
--
--   Given a function @f@, if any of its arguments and/or its return
--   value are judged suitable for flattening, then @f@ is replaced by
--   a /wrapper/ function @f@ and a /worker/ function @f_w@.  The
--   wrapper function has the same name as @f@, while the worker
--   function has a new name.  The wrapper function, created by
--   'mkWrapperFunction' unpacks its arguments, calls @f_w@, and packs
--   the result value.  The worker function, created by
--   'mkWorkerFunction', repacks its arguments, runs the original
--   function body, and unpacks the result value.
--      
--   Flattening on expressions just traverses the program to visit all
--   functions.

-- | Flatten the function's arguments and return value.
--   The original function is replaced by a wrapper function.
--   A new worker function is created containing the original function body.
--
--   If flattening would not change the function arguments, then the function
--   body is transformed and a single definition is returned.  Otherwise,
--   the worker is returned, followed by the wrapper.
flattenFunctionArguments :: Def Mem -> AF (Maybe (Def Mem), Def Mem)
flattenFunctionArguments def = do
  let fun_name = definiendum def
      FunM fun = definiens def
  plan <- planFunction (definiens def)
  
  -- Flatten inside the function body
  body <- assumeTyPats (funTyParams fun) $ assumePats (funParams fun) $ do
    flattenInExp $ funBody fun
  
  -- Construct wrapper if it's beneficial
  if isIdPlan plan
    then let fun' = fun {funBody = body} 
         in return (Nothing, mkDef fun_name (FunM fun'))
    else do
      worker_name <- newClonedVar fun_name
      worker <- mkWorkerFunction plan worker_name body
      wrapper <- mkWrapperFunction plan fun_name worker_name
      return (Just worker, wrapper)

-- | Perform flattening in the body of a function, but don't change the
--   function's arguments
flattenInFun :: FunM -> AF FunM
flattenInFun (FunM f) =
  assumeTyPats (funTyParams f) $ assumePats (funParams f) $ do
    fun_body <- flattenInExp $ funBody f
    return $ FunM $ f {funBody = fun_body}

flattenInGroup :: DefGroup (Def Mem) -> AF [DefGroup (Def Mem)]
flattenInGroup (NonRec def) = do
  (m_worker, wrapper) <- flattenFunctionArguments def
  -- Wrapper can reference worker, but not vice versa; produce two groups
  return $ case m_worker
           of Nothing -> [NonRec wrapper]
              Just w  -> [NonRec w, NonRec wrapper]

flattenInGroup (Rec defs) = do
  flattened <- mapM flattenFunctionArguments defs
  return [Rec $ catMaybes $ concat [[m_worker, Just wrapper]
                                   | (m_worker, wrapper) <- flattened]]

flattenInExp :: ExpM -> AF ExpM
flattenInExp expression =
  case fromExpM expression
  of VarE {} -> return expression
     LitE {} -> return expression
     AppE inf op ty_args args -> do
       op' <- flattenInExp op
       args' <- mapM flattenInExp args
       return $ ExpM $ AppE inf op' ty_args args'
     LamE inf f -> do
       f' <- flattenInFun f
       return $ ExpM $ LamE inf f'
     LetE inf pat rhs body -> do
       rhs' <- flattenInExp rhs
       body' <- flattenInExp body
       return $ ExpM $ LetE inf pat rhs' body'
     LetfunE inf defs body -> do
       new_defs <- flattenInGroup defs
       body' <- flattenInExp body
       let mk_letfun d e = ExpM (LetfunE inf d e)
       return $ foldr mk_letfun body' new_defs
     CaseE inf scr alts -> do
       scr' <- flattenInExp scr
       alts' <- mapM flattenInAlt alts
       return $ ExpM $ CaseE inf scr' alts'
     ExceptE {} -> return expression

flattenInAlt :: AltM -> AF AltM
flattenInAlt (AltM alt) =
  assumeTyPats (getAltExTypes alt) $ assumePats (altParams alt) $ do
    body' <- flattenInExp (altBody alt)
    return $ AltM $ alt {altBody = body'}

flattenInExport :: Export Mem -> AF (Export Mem)
flattenInExport export = do
  f <- flattenInFun $ exportFunction export
  return $ export {exportFunction = f}

flattenModuleContents :: (Module Mem) -> AF (Module Mem)
flattenModuleContents (Module mod_name defss exports) = do
  defss' <- mapM flattenInGroup defss
  exports' <- mapM flattenInExport exports
  return $ Module mod_name (concat defss') exports'

flattenArguments :: Module Mem -> IO (Module Mem)
flattenArguments mod =
  withTheNewVarIdentSupply $ \id_supply -> do
    (dict_env, intindex_env) <- runFreshVarM id_supply createDictEnv
    type_env <- readInitGlobalVarIO the_memTypes
    let env = AFLVEnv id_supply type_env dict_env intindex_env ()
    runReaderT (unAF $ flattenModuleContents mod) env

-------------------------------------------------------------------------------
-- * The local variable flattening pass

-- | Local variable flattening does something similar to argument flattening,
--   but for local variable definitions whose RHS is a complicated expression.
--   In this case, the benefit of the transformation is that it replaces 
--   expensive, large temporary variables by cheap, small ones.
--
--   Local variable flattening is applied to all @let@ expressions, and
--   @case@ expressions where the scrutinee is a boxed object.
--   For example:
--
--   > case boxed(case foo of {A. expr_1; B. expr_2})
--   > of boxed (t). case t
--   >               of (x, y, z). ... use y and z ...
--    
--   In this example, local variable flattening eliminates the storage of
--   the unused variable @x@.  Moreover, if @y@ and @z@ can be
--   register-allocated, we can replace the heap-allocated boxed tuple by a
--   register-allocated unboxed tuple.
--
--   A value is flattened if: 
--
--   * Its demand is @D{...}@.  A \"deconstructed\" demand indicates that the
--     value will only be deconstructed by a case statement.  This is good
--     because it means only the fields of the object are needed, not the
--     object itself.  We are free to replace the object with a cheaper object.
--
--   * Its type is @Stored a@ for some value type @a@.  We predict that
--     that value types are always cheaper than stored types, even if the
--     object will have to be reconstructed later.

-- | During local variable flattening, keep track of the mapping between
--   local variables and their unpacked form
type LocalVarEnv = IntMap.IntMap FlatLocal

-- | The local variable flattening monad
type LF = AFMonad LocalVarEnv

-- | Keep track of a variable that has been unpacked.  This is performed by
--   let-bindings.
withUnpackedLocalVariable :: FlatLocal -> LF a -> LF a
withUnpackedLocalVariable fl@(FlatLocal (FlatArg pat _)) m =
  let var_id = fromIdent $ varID $ patMVar pat
      ins env = env {afOther = IntMap.insert var_id fl $ afOther env}
  in AF $ local ins $ unAF m

-- | Look up the unpacked version of a variable, given the original variable.
--   If 'Nothing' is returned, this variable will not be unpacked.
lookupUnpackedLocalVariable :: Var -> LF (Maybe FlatLocal)
lookupUnpackedLocalVariable v = AF $ asks (lookup_var . afOther)
  where
    lookup_var m = IntMap.lookup (fromIdent $ varID v) m

-- | Remove the unpacked version of a variable from the environment.
--   If the variable is seen during the execution of @m@,it won't be unpacked.
deleteUnpackedLocalVariable :: Var -> LF a -> LF a
deleteUnpackedLocalVariable v m = AF $ local delete_var $ unAF m
  where
    delete_var env =
      env {afOther = IntMap.delete (fromIdent $ varID v) $ afOther env}

-- | Perform local variable flattening on the body of a function
lvInFun :: FunM -> LF FunM
lvInFun (FunM f) =
  assumeTyPats (funTyParams f) $ assumePats (funParams f) $ do
    fun_body <- lvExp $ funBody f
    return $ FunM $ f {funBody = fun_body}

lvDef :: Def Mem -> LF (Def Mem)
lvDef def = mapMDefiniens lvInFun def

lvExp :: ExpM -> LF ExpM
lvExp expression =
  case fromExpM expression
  of VarE _ v -> do
       -- It's an error to see an unpacked local variable here.
       -- Any appearances of an unpacked local variable should have been
       -- transformed by the App or Case rules.
       m_unpacking <- lookupUnpackedLocalVariable v
       when (isJust m_unpacking) $
         internalError "lvExp: Unexpected unpacked variable"
       return expression
     LitE {} -> return expression
     AppE inf op ty_args args ->
       lvApp inf op ty_args args
     LamE inf f -> do
       f' <- lvInFun f
       return $ ExpM $ LamE inf f'
     LetE inf pat rhs body -> lvLet inf pat rhs body
     LetfunE inf defs body -> do
       new_defs <- mapM lvDef defs
       body' <- lvExp body
       return $ ExpM $ LetfunE inf new_defs body'
     CaseE inf scr alts -> lvCase inf scr alts
     ExceptE _ _ -> return expression

lvApp inf op ty_args args = do
  op' <- lvExp op
  args' <- mapM lvExp args
  return $ ExpM $ AppE inf op' ty_args args'

lvLet :: ExpInfo -> PatM -> ExpM -> ExpM -> LF ExpM
lvLet inf binder rhs body = do
  rhs' <- lvExp rhs
  binder_plan <- planLocal binder
  lvFlattenBinding inf binder_plan rhs' body

-- | Transform local variables for a case statement.
-- First, if the scrutinee was a transformed local variable, then insert code
-- to repack the variable just before the case statement.
--
-- > let original_variable = (recreate the original value)
-- > in case original_variable of ...
lvCase inf scr alts =
  case scr
  of ExpM (VarE scr_info scr_var) -> do
       m_unpacking <- lookupUnpackedLocalVariable scr_var
       case m_unpacking of
         Just flattening -> do
           -- The scrutinee is a variable that has been unpacked.
           -- Generate code to repack the scrutinee variable.  Process the
           -- case statement as normal.
           exp <- deleteUnpackedLocalVariable scr_var transform_case
           packLocal flattening exp
         Nothing -> transform_case
     _ -> transform_case
  where
    transform_case = do
      scr' <- lvExp scr
      lvTransformCase inf scr alts

-- | Transform case bindings of @boxed@ type.
--
--   A case whose scrutinee has type @Boxed a@ is essentially a let-binding
--   for a bare value.  Try to flatten the local variable as if it were a
--   let binding.
--      
--   The scrutinee has already been transformed; the case alternatives have
--   not been transformed.
lvTransformCase inf scr [altm]
  | (mono_con@(MonoCon alt_con [ty] []), [param], body) <- altToMonoCon altm,
    alt_con `isPyonBuiltin` the_boxed = do
      binder_plan <- planLocal param
      case binder_plan of
        FlatLocal (FlatArg _ IdDecomp) ->
          -- The scrutinee isn't deconstructed except for the outermost
          -- 'boxed' constructor.  Don't transform this case statement.
          lvRecurseCase inf scr [altm]

        FlatLocal (FlatArg _ decomp) -> do
          -- Will deconstruct the bare value.
          -- To get to the bare value, the scrutinee must be deconstructed.
          scrutinee_var <- newAnonymousVar ObjectLevel
          let plan = flattenBoxedValue scrutinee_var binder_plan

          -- Add the case alternative's variable bindings and
          -- unpacked variable to the environment.
          -- 'lvFlattenBinding' only adds the newly created scrutinee variable,
          -- which isn't used by the program.
          assumePat param $ withUnpackedLocalVariable binder_plan $
            lvFlattenBinding inf plan scr body

lvTransformCase inf scr alts = lvRecurseCase inf scr alts

-- | Perform local variable flattening inside a case statement.
--   The scrutinee has already been transformed; the case alternatives have
--   not been transformed.
lvRecurseCase inf scr alts = do
  alts' <- mapM lvInAlt alts
  return $ ExpM $ CaseE inf scr alts'

lvFlattenBinding :: ExpInfo -> FlatLocal -> ExpM -> ExpM -> LF ExpM
lvFlattenBinding inf flat_local@(FlatLocal (FlatArg pat decomp)) rhs body
  | isIdDecomp decomp = do
      -- Don't deconstruct the source expression
      body' <- assumePat pat $ lvExp body
      tenv <- getTypeEnv
      return $ bindVariable tenv (patMBinder pat) rhs body'

  | otherwise = do
      -- Flatten the source value
      let ret = flatLocalReturn flat_local
      flat_rhs <- flattenLocal flat_local rhs $ flattenedReturnValue ret

      -- Transform the body   
      body' <- assumePat pat $
               withUnpackedLocalVariable flat_local $
               lvExp body
      
      -- Bind the flattened value
      let flattened_params =
            case flattenedReturnParameters ret of Just ps -> ps
      return $ bindFlattenedReturn inf flattened_params flat_rhs body'

lvInAlt :: AltM -> LF AltM
lvInAlt (AltM alt) =
  assumeTyPats (getAltExTypes alt) $ assumePats (altParams alt) $ do
    body' <- lvExp (altBody alt)
    return $ AltM $ alt {altBody = body'}

lvInExport :: Export Mem -> LF (Export Mem)
lvInExport export = do
  f <- lvInFun $ exportFunction export
  return $ export {exportFunction = f}

lvModuleContents :: (Module Mem) -> LF (Module Mem)
lvModuleContents (Module mod_name defss exports) = do
  defss' <- mapM (mapM lvDef) defss
  exports' <- mapM lvInExport exports
  return $ Module mod_name defss' exports'

flattenLocals :: Module Mem -> IO (Module Mem)
flattenLocals mod =
  withTheNewVarIdentSupply $ \id_supply -> do
    (dict_env, intindex_env) <- runFreshVarM id_supply createDictEnv
    type_env <- readInitGlobalVarIO the_memTypes
    let env = AFLVEnv id_supply type_env dict_env intindex_env IntMap.empty
    mod' <- runReaderT (unAF $ lvModuleContents mod) env
    
    -- Flattening creates multiple local variables with the same name.
    -- Rename them.
    runFreshVarM id_supply $ freshenModuleFully mod'

