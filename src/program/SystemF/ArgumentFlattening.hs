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
module SystemF.ArgumentFlattening(flattenArguments)
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
import SystemF.Floating2
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import SystemF.Rename
import SystemF.ReprDict
import SystemF.TypecheckMem
import Type.Compare
import Type.Environment
import Type.Eval
import qualified Type.Rename as Rename
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
  of Just (op, [arg]) | op `isPyonBuiltin` The_OutPtr -> arg
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

noneValue :: ExpM
noneValue = conE defaultExpInfo (VarCon (pyonBuiltin The_None) [] []) []

-------------------------------------------------------------------------------
-- * The argument flattening monad

-- | Reader environment used during argument flattening and local variable
--   flattening.
data AFLVEnv a =
  AFLVEnv
  { afVarSupply :: {-# UNPACK #-}!(IdentSupply Var)
  , afTypeEnv :: TypeEnv
  , afDictEnv :: SingletonValueEnv
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
  localDictEnv f m =
    AF $ local (\env -> env {afDictEnv = f $ afDictEnv env}) $ unAF m

instance EvalMonad (AFMonad e) where
  liftTypeEvalM m = AF $ ReaderT $ \env -> do
    runTypeEvalM m (afVarSupply env) (afTypeEnv env)

assumePat :: (EvalMonad m, ReprDictMonad m) =>
             PatM -> m a -> m a
assumePat pat m = assumeBinder (patMBinder pat) $ saveReprDictPattern pat m

assumePats :: (EvalMonad m, ReprDictMonad m) =>
              [PatM] -> m a -> m a
assumePats pats m = foldr assumePat m pats

assumeDef :: TypeEnvMonad m => Def Mem -> m a -> m a
assumeDef d m = assume (definiendum d) (functionType $ definiens d) m

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
       ((), body') <- assumeDefGroup defs (return ()) $ mapOverTailExps f body
       return $ ExpM $ LetfunE inf defs body'
     CaseE inf scr alts -> do
       alts' <- mapM map_alt alts
       return $ ExpM $ CaseE inf scr alts'
     _ -> f expression
  where
    map_alt (AltM alt) =
      assumeBinders (deConExTypes $ fromDeCInstM $ altCon alt) $
      assumePats (altParams alt) $ do
        body <- mapOverTailExps f $ altBody alt
        return $ AltM (alt {altBody = body})

-------------------------------------------------------------------------------
-- * Argument flattening types 

-- | A decomposition of a value into components
data Decomp =
    -- | Value is unchanged
    IdDecomp

    -- | Value is deconstructed.
    --   The fields of the deconstructed value cannot contain a dummy
    --   parameter.
  | DeconDecomp !DeConInst FlatArgs

    -- | Value is dead
    --
    --   An expression is provided to fabricate a value of the correct type.
    --   The exact value doesn't matter since it's dead.
  | DeadDecomp ExpM

pprDecomp :: Decomp -> Doc
pprDecomp IdDecomp = text "U"
pprDecomp (DeconDecomp (VarDeCon con ty_args ex_types) fields) =
  text "D{" <> app <> text "}"
  where
    ty_args_doc = [pprTypePrec t ?+ appPrec | t <- ty_args]
    ex_types_doc = [parens (pprVar v <+> text ":" <+> pprType t)
                   | (v ::: t) <- ex_types]
    fields_doc = map pprFlatArg fields
    app = sep (pprVar con : ty_args_doc ++ ex_types_doc ++ fields_doc)

pprDecomp (DeconDecomp (TupleDeCon _) fields) =
  -- Tuples should not be decomposed
  text "ERROR"

pprDecomp (DeadDecomp e) = text "0" <+> braces (pprExp e)

isIdDecomp IdDecomp = True
isIdDecomp _ = False

isDeadDecomp (DeadDecomp _) = True
isDeadDecomp _ = False

-- | Decide whether the data produced by decomposition are all \"small\".   
--   Data are deemed small if they are value or boxed types.
--
--   The significance of this test is that small data are probably cheap
--   to copy, so it's probably cheap to decompose or rebuild a value if
--   its results are small.
isSmallDecomp :: TypeEnv -> (Type, Decomp) -> Bool
isSmallDecomp tenv (ty, decomp) =
  case decomp
  of IdDecomp -> is_small_type ty
     DeadDecomp {} -> True
     DeconDecomp decon fields ->
       let local_tenv = foldr assume_binder tenv $ deConExTypes decon
       in all (isSmallDecomp local_tenv)
          [(patMType p, d) | FlatArg p d <- fields]
  where
    assume_binder (v ::: t) tenv = insertType v t tenv

    is_small_type t =
      case toBaseKind $ typeKind tenv ty
      of ValK -> True
         BoxK -> True
         _    -> False

-- | Determine whether all decomposed items are values or boxed objects.
--   If so, then it's possible to unpack a return value with this type.
unpacksToAValue :: TypeEnv -> FlatRet -> Bool
unpacksToAValue tenv (FlatRet ty IdDecomp) =
  case toBaseKind $ typeKind tenv ty
  of ValK -> True
     BoxK -> True
     _    -> False

unpacksToAValue tenv (FlatRet _ (DeconDecomp decon fs)) =
  null (deConExTypes decon) &&
  and [unpacksToAValue tenv (flatArgReturn f) | f <- fs]

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
    go _ (DeadDecomp _) = mempty
    go _ (DeconDecomp decon fields) =
      mconcat $ map (typaram . TyPatM) (deConExTypes decon) ++
                [go (field p) d | (p, d) <- map fromFlatArg fields]

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
--
--   This data type is not used for representing output pointer arguments.
data FlatArg =
    FlatArg { faPattern        :: !PatM   -- ^ The original function parameter
            , faTransformation :: !Decomp -- ^ How the parameter is decomposed
            }
    
  | DummyArg { faDummyPattern :: !PatM} -- ^ A new parameter for which
                                        -- there was no original
                                        -- parameter.  The parameter
                                        -- has type @NoneType@ and
                                        -- value @None@.

fromFlatArg (FlatArg p d) = (p, d)
fromFlatArg (DummyArg _) = internalError "fromFlatArg: Unexpected dummy argument"

assumePackedArg (FlatArg pat _) m = assumePat pat m
assumePackedArg (DummyArg _)    m = m

type FlatArgs = [FlatArg]

pprFlatArg (FlatArg pat decomp) = hang (brackets (pprDecomp decomp)) 8 pat_doc
  where
    pat_doc = pprVar (patMVar pat) <+> text ":" <+> pprType (patMType pat)

pprFlatArg (DummyArg pat) = text "dummy"

isIdArg (FlatArg _ trans) = isIdDecomp trans 
isIdArg (DummyArg _) = False

isDeadArg (FlatArg _ trans) =
  let true = Any True
      -- The argument is dead if flattening produces no parameters or
      -- type parameters.
      not_dead = getAny $ flattenDecomp (const true) (const true) true trans
  in not not_dead

isDeadArg (DummyArg _) = False

-- | A flattened return.
--
--   The flattened return specifies the original return type, the flattened
--   return type, and how to convert from one to the other.  If the return
--   type is bare, then the return type describes an initializer function;
--   otherwise, it describes a returned value or returned boxed object.
--
--   The 'frType' field holds the type of the returned data.  It is not the
--   type of an output pointer or side effect.
--
--   A return value may be flattened to a sequence of values.
--   Returned values containing existential types cannot be flattened.
--   If flattening produces one value, its type is the flattened return type. 
--   If it produces many values, they are aggregated into an unboxed tuple.
--   The unboxed tuple type is the flattened return type.
data FlatRet =
  FlatRet { frType :: Type      -- ^ Type of the returned data
          , frDecomp :: Decomp  -- ^ How the return value is decomposed
          }

isIdRet (FlatRet _ IdDecomp) = True 
isIdRet _ = False

-- | Get the flattened return specification corresponding to a 'FlatArg'.
flatArgReturn :: FlatArg -> FlatRet
flatArgReturn (FlatArg pat decomp) = FlatRet (patMType pat) decomp
flatArgReturn (DummyArg _) = internalError "flatArgReturn: Unexpected dummy argument"

-- | Get the packed argument list from a sequence of flattened parameters
packedParameters :: FlatArgs -> [PatM]
packedParameters xs = mapMaybe packedParameter xs

-- | Get the packed argument from a flattened parameter
packedParameter :: FlatArg -> Maybe PatM
packedParameter (FlatArg pat _) = Just pat
packedParameter (DummyArg _)    = Nothing

-- | Get the flattened argument list from a flattened parameter
flattenedParameter :: FlatArg -> ([TyPatM], [PatM])
flattenedParameter (FlatArg pat decomp) =
  flattenDecomp put_typat put_pat (put_pat pat) decomp
  where
    put_typat p = ([p], [])
    put_pat p = ([], [p])

flattenedParameter (DummyArg pat) = ([], [pat])

-- | Get the flattened argument list from a sequence of flattened parameters
flattenedParameters :: FlatArgs -> ([TyPatM], [PatM])
flattenedParameters xs = mconcat $ map flattenedParameter xs

flattenedParameterValue :: FlatArg -> ([TypM], [ExpM])
flattenedParameterValue (FlatArg pat decomp) =
  flattenDecomp put_typat put_pat (put_pat pat) decomp
  where
    put_typat (TyPatM (a ::: _)) = ([TypM (VarT a)], [])
    put_pat p = ([], [ExpM $ VarE defaultExpInfo (patMVar p)])

flattenedParameterValue (DummyArg _) =
  ([], [noneValue])

-- | Get the flattened parameter values from a sequence of flattened
--   parameters.  Each value is a type variable or variable expression.
flattenedParameterValues :: FlatArgs -> ([TypM], [ExpM])
flattenedParameterValues xs = mconcat $ map flattenedParameterValue xs

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
  of Just [e] -> fst e
     Just es  -> let (values, types) = unzip es
                 in ExpM $ ConE defaultExpInfo (CInstM (TupleCon types)) values
     Nothing -> internalError "flattenedReturnValue"
  where
    var_exp pat = (ExpM $ VarE defaultExpInfo (patMVar pat), patMType pat)

-- | Given the variable bindings returned by 'flattenedReturnParameters', 
--   and a flattened return value, bind the flattened return variables.
bindFlattenedReturn :: ExpInfo -> [PatM] -> ExpM -> ExpM -> ExpM
bindFlattenedReturn inf [p] source_exp body =
  -- Single value.  Assign the expression result to the pattern variable.
  ExpM $ LetE inf p source_exp body

bindFlattenedReturn inf patterns source_exp body =
  -- Multiple or zero return values.  Deconstruct the
  -- expression result with a case statement, then repack.
  let pattern_types = map patMType patterns
      decon = TupleDeCon pattern_types
  in ExpM $ CaseE defaultExpInfo source_exp
     [AltM $ Alt (DeCInstM decon) patterns body]

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
     DeconDecomp decon fields ->
       let pattern_exp = ExpM $ VarE defaultExpInfo (patMVar pat)
           body' = flattenParameters fields body
           alt = AltM $ Alt (DeCInstM decon) (map faPattern fields) body'
       in ExpM $ CaseE defaultExpInfo pattern_exp [alt]
     DeadDecomp _ -> body

flattenParameter (DummyArg _) body = body

flattenParameters :: [FlatArg] -> ExpM -> ExpM
flattenParameters args e = foldr flattenParameter e args

packParametersWrite :: (ReprDictMonad m, EvalMonad m) => FlatArgs -> m [ExpM]
packParametersWrite (arg:args) = do
  e <- packParameterWrite arg
  es <- assumePackedArg arg $ packParametersWrite args
  return (maybe id (:) e es)

packParametersWrite [] = return []

-- | Pack a parameter whose result will be written to a destination
--
--   TODO: Don't return the parameter expression.  It's always just the
--   pattern variable.
packParameterWrite :: (ReprDictMonad m, EvalMonad m) =>
                      FlatArg -> m (Maybe ExpM)
packParameterWrite (FlatArg pat flat_arg) =
  liftM Just $ packParameterWrite' pat flat_arg

packParameterWrite (DummyArg _) = return Nothing
  
packParameterWrite' pat flat_arg =
  case flat_arg
  of IdDecomp -> copy_expr (patMType pat) (var_exp $ patMVar pat)
     DeconDecomp (VarDeCon con_var types ex_types) fields ->
       assumeBinders ex_types $ do
         exps <- packParametersWrite fields
         
         -- Construct/initialize a value
         let con = VarCon con_var types [VarT a | a ::: _ <- ex_types]
         return $ conE defaultExpInfo con exps

     DeadDecomp e -> return e
  where
    var_exp v = ExpM $ VarE defaultExpInfo v
    
    copy_expr ty src = do
       tenv <- getTypeEnv
       case toBaseKind $ typeKind tenv ty of
         BareK -> do
           -- Insert a copy operation
           dict <- getReprDict ty
           return $ appE defaultExpInfo copy_op [TypM ty] [dict, src]
         _ ->
           return src
    
    copy_op = ExpM $ VarE defaultExpInfo (pyonBuiltin The_copy)

-- | Pack a parameter, so that the result is readable
packParametersRead :: (ReprDictMonad m, EvalMonad m) =>
                      FlatArgs -> m ([ExpM], ExpM -> ExpM)
packParametersRead (arg : args) = do
  (val, ctx) <- packParameterRead arg
  (vals, ctxs) <- assumePackedArg arg $ packParametersRead args
  return (maybe id (:) val vals, ctx . ctxs)

packParametersRead [] = return ([], id)

-- | Pack a parameter
--
--   TODO: Don't return the parameter expression.  It's always just the
--   pattern variable.
packParameterRead :: (ReprDictMonad m, EvalMonad m) =>
                     FlatArg -> m (Maybe ExpM, ExpM -> ExpM)
packParameterRead (FlatArg pat flat_arg) =
  case flat_arg
  of IdDecomp ->
       return (Just (var_exp $ patMVar pat), id)
     DeconDecomp (VarDeCon con_var types ex_types) fields ->
       assumeBinders ex_types $ do
         exps <- packParametersWrite fields
         let con = VarCon con_var types [VarT a | a ::: _ <- ex_types]
         let packed = conE defaultExpInfo con exps
         
         -- If this is a bare type, define a local variable with the
         -- packed parameter.  Otherwise, just assign a local variable.
         tenv <- getTypeEnv
         return (Just (var_exp $ patMVar pat),
                 bindVariable tenv (patMBinder pat) packed)

     DeadDecomp e ->
       -- Assign the expression to a temporary variable
       return (Just (var_exp $ patMVar pat),
               \body -> ExpM $ LetE defaultExpInfo pat e body)
  where
    var_exp v = ExpM $ VarE defaultExpInfo v

packParameterRead (DummyArg _) = return (Nothing, id)

-- | Transform an expression's return value to flattened form.  Deconstruct
--   the return value into its component fields, then pack the
--   components into the correct form to return from the expression.
--
--   The expression should be a value or an initializer expression.  If the
--   given expression came from a function that returns by initializing a
--   variable, the caller should lambda-abstract over the output pointer
--   using 'lambdaAbstractReturn'.
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
       (flatten_args flat_args) (flatten_fields flat_args) orig_exp
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

    -- If the return value was pattern-matched and deconstructed,
    -- then read and flatten the individual field values
    flatten_fields flat_fields =
      return $ flattenParameters flat_fields flattened_value

    -- The 'FlatRet' parameter determines the flattened return value
    flattened_value = flattenedReturnValue flat_ret
 
-- | Deconstruct a return value according to the given pattern.
--   The given expression to deconstruct should be a value or initializer
--   expression.
--   The deconstruction code is moved to tail position and constructor
--   applications are eliminated when possible.
--
--   If a constructor application can be matched and deconstructed,
--   the initializer expressions are used to construct the final expression.
--   Otherwise, the constructor's result is deconstructed, its fields are 
--   bound to the given 'FlatArgs' patterns, and code is generated to
--   deconstruct those patterns.
deconReturn :: (EvalMonad m, ReprDictMonad m) =>
               DeConInst          -- ^ Constructor to match against
            -> FlatArgs           -- ^ Fields to deconstruct
            -> ([ExpM] -> m ExpM) -- ^ Deconstruct initializers
            -> m ExpM             -- ^ Deconstruct values bound to patterns
            -> ExpM               -- ^ Expression to deconstruct
            -> m ExpM             -- ^ Deconstructor
deconReturn decon dc_fields decon_initializers decon_patterns expression =
  mapOverTailExps decon_tail expression
  where
    decon_tail tail_exp = do
      tenv <- getTypeEnv

      -- Attempt to deconstruct the tail expression
      case tail_exp of
        ExpM (ConE inf (CInstM con) fields)
          | summarizeDeconstructor decon /= summarizeConstructor con ->
            internalError "deconReturn: Unexpected data constructor"
          | otherwise ->
            -- Eliminate the data constructor.
            -- Continue processing with the initializers.
            decon_initializers fields
        _ ->
          bind_and_deconstruct tail_exp
          
    -- Unable to deconstruct the expression.  Bind the expression's result to 
    -- a variable, then deconstruct it.
    bind_and_deconstruct tail_exp = do
      consumer_exp <- decon_patterns

      -- Deconstruct the expression result
      let match = AltM $ Alt (DeCInstM decon) (map faPattern dc_fields) consumer_exp
          case_of scrutinee = ExpM $ CaseE defaultExpInfo scrutinee [match]

      -- Bind the expression result
      (_, data_type) <-
        conType (case decon
                 of VarDeCon v ty_args ex_types ->
                      VarCon v ty_args [VarT v | v ::: _ <- ex_types]
                    TupleDeCon ty_args ->
                      TupleCon ty_args)
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
      flattenLocalWrite (FlatLocal arg) exp consumer

-- | Flatten a local value.  The flattened values are bound to variables
--   in the context of a consumer expression.
--
--   When the return value is a bare object initializer, it is first bound to
--   a variable, then the variable is flattened.
--
--   The return value is flattened to a value or tuple using 'flattenReturn', 
--   then the result is bound to variables.
flattenLocalWrite :: (EvalMonad m, ReprDictMonad m) =>
                     FlatLocal -> ExpM -> ExpM -> m ExpM
flattenLocalWrite (FlatLocal (FlatArg old_binder decomp)) expr consumer =
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

-- | Flatten a local read value.
--
--   For value or boxed types, this simply calls 'flattenLocalWrite'.
--   For bare types, the value is bound to a variable, then deconstructed
--   with 'flattenParameter'.
flattenLocalRead :: (EvalMonad m, ReprDictMonad m) =>
                    FlatLocal -> ExpM -> ExpM -> m ExpM
flattenLocalRead flat_local@(FlatLocal flat_arg) expr consumer = do
  tenv <- getTypeEnv
  case toBaseKind $ typeKind tenv arg_type of
    BareK -> return decon_value
    ValK  -> flattenLocalWrite flat_local expr consumer
    BoxK  -> flattenLocalWrite flat_local expr consumer
  where
    arg_type = patMType $ faPattern flat_arg

    -- Bind the value to the original pattern, deconstruct it,
    -- and finally consume it
    decon_value =
      let decon_expr = flattenParameter flat_arg consumer
      in ExpM $ LetE defaultExpInfo (faPattern flat_arg) expr decon_expr

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
          DeconDecomp {} ->
            -- This can occur when returning something isomorphic to the
            -- unit value.  In this case, we should return a unit value.
            internalError "packReturn: No return value"
     Just patterns -> do
       -- Return value was deconstructed (DeconDecomp).
       -- Rebuild the data structure.
       repack_exp <-
         packParameterWrite' (internalError "packReturn") (frDecomp flat_ret)
       
       let inf = case orig_exp of ExpM e -> expInfo e
       return $! bindFlattenedReturn inf patterns orig_exp repack_exp

-- | Lambda-abstract the expression over the given parameter. 
--
--   We use this for abstracting over output pointers.
lambdaAbstractReturn :: (ReprDictMonad m, TypeEnvMonad m) =>
                        TypM    -- ^ Expression's return type
                     -> PatM    -- ^ Parameter to abstract over
                     -> ExpM    -- ^ Expression
                     -> m ExpM  -- ^ Create a new expression
lambdaAbstractReturn rtype pat exp = mapOverTailExps lambda_abstract exp
  where
    lambda_abstract e =
      return $ ExpM $ LamE defaultExpInfo $
               FunM $ Fun { funInfo = defaultExpInfo
                          , funTyParams = []
                          , funParams = [pat]
                          , funReturn = rtype
                          , funBody = e}

-------------------------------------------------------------------------------
-- * Decisions on how to flatten

-- | Flattening decisions are made differently for parameter types,
--   return types, and local variables.
--       
--   It is always possible to undo flattening for parameter and return values.
--   However, local variables can only be unflattened around function calls and
--   case statements; these are also the only kinds of uses that may produce a
--   demand other than 'Used'.  Local variables are flattened parsimoniously,
--   guaranteeing that they can be unflattened where necessary.  Parameters and
--   returns are flattened liberally.
--
--   Return values with existential types cannot be flattened.
data PlanMode = PlanMode { eagerness :: !Eagerness
                         , existentialHandling :: !ExistentialHandling}
              deriving(Eq)

data Eagerness = Parsimonious    -- ^ Don't flatten unless it's determined to
                                 --   be beneficial
               | LiberalStored   -- ^ Flatten @Stored@ data types even if it
                                 --   doesn't appear to be beneficial
               | LiberalSmall    -- ^ Flatten small data types even if it
                                 --   doesn't seem to be beneficial.  A type
                                 --   is small if it can be unpacked to
                                 --   produce only value and boxed types.
                 deriving(Eq)

data ExistentialHandling =
    UnpackExistentials
  | Don'tUnpackExistentials
    deriving(Eq)

-- | Decide how to flatten a function arguments
planParameters :: (ReprDictMonad m, EvalMonad m) =>
                  PlanMode -> [PatM] -> m [FlatArg]
planParameters mode pats = do mapM (planParameter mode) pats

-- | Decide how to flatten a function argument.
planParameter :: (ReprDictMonad m, EvalMonad m) =>
                 PlanMode -> PatM -> m FlatArg
planParameter mode pat = do
  (whnf_type, decomp) <-
    planFlattening mode (patMType pat) (specificity $ patMDmd pat)

  -- Create a new pattern with unknown demand information
  return $ FlatArg (patM (patMVar pat ::: whnf_type)) decomp

-- | Decide how to decompose a data structure.
--   Return the data type and its decomposition.  The data type is the
--   parameter @ty@ reduced to HNF form.
--
--   This function does the real work of 'planParameter', 'planReturn', and 
--   'planLocal'.
planFlattening :: (ReprDictMonad m, EvalMonad m) =>
                  PlanMode -> Type -> Specificity -> m (Type, Decomp)
planFlattening mode ty spc = do
  tenv <- getTypeEnv
  whnf_type <- reduceToWhnf ty
  let
    -- The return value will have of these decompositions 
    id_decomp = return (whnf_type, IdDecomp)

    dead_decomp = do
      dead_expr <- deadValue whnf_type
      return (whnf_type, DeadDecomp dead_expr)
      
    decon_decomp con spcs =
      -- Data type must be a constructor application.
      -- Get its type arguments from the pattern type.
      case fromVarApp whnf_type
      of Just (op, args) -> do
           decomp <- planDeconstructedValue mode con args spcs
           return (whnf_type, decomp)
         Nothing -> internalError "planParameter': Type mismatch"

    -- If data type has a singleton constructor, then deconstruct it.
    -- However, deconstructing may be disallowed when the constructor has
    -- existential types.
    singleton_decomp =
      case fromVarApp whnf_type
      of Just (op, _) | Just data_con <- fromProductTyCon tenv op ->
           -- Check for existential types
           if (case existentialHandling mode
               of UnpackExistentials -> True
                  Don'tUnpackExistentials ->
                    null $ dataConPatternExTypes data_con)
           then decon_decomp (dataConCon data_con) Nothing
           else id_decomp
         _ -> id_decomp

    -- Similar to singleton_decomp, except that decomposition only occurs if
    -- the result of decomposition is small.
    liberal_decomp =
      case fromVarApp whnf_type
      of Just (op, _) | Just data_con <- fromProductTyCon tenv op ->
           -- Check for existential types
           if (case existentialHandling mode
               of UnpackExistentials -> True
                  Don'tUnpackExistentials ->
                    null $ dataConPatternExTypes data_con)
           then do
             -- Create a decomposition
             ret <- decon_decomp (dataConCon data_con) Nothing

             -- Ensure that the decomposed value is samll
             if isSmallDecomp tenv ret
               then return ret
               else id_decomp
           else id_decomp
         _ -> id_decomp

    -- If data type is a Stored type, then deconstruct it.
    stored_decomp =
      case fromVarApp whnf_type
      of Just (op, [arg]) | op `isPyonBuiltin` The_Stored ->
           decon_decomp (pyonBuiltin The_stored) Nothing
         _ -> id_decomp

  case spc of
    -- Don't flatten or remove Repr parameters, because later stages of the
    -- compiler might want to access them. 
    _ | is_repr_pattern whnf_type -> id_decomp

    -- Remove dead fields
    Unused -> dead_decomp

    -- Don't flatten dictionary parameters or abstract data types.
    -- They can be removed if dead.
    _ | is_dictionary_pattern whnf_type || is_abstract tenv whnf_type ->
      id_decomp

    Decond (VarDeCon spc_con _ _) spcs -> decon_decomp spc_con (Just spcs)

    -- Unpacking is not implemented for unboxed tuples
    Decond (TupleDeCon _) spcs -> id_decomp

    Inspected -> singleton_decomp

    Used -> 
      case eagerness mode
      of Parsimonious -> id_decomp
         LiberalStored -> stored_decomp
         LiberalSmall -> liberal_decomp
           
  where
    is_repr_pattern t =
      case fromVarApp t
      of Just (op, _) -> op == pyonBuiltin The_Repr
         _ -> False

    is_dictionary_pattern t =
      case fromVarApp t
      of Just (op, _) -> isDictionaryTypeCon op
         _ -> False
    
    is_abstract tenv t =
      case fromVarApp t
      of Just (op, _) | Just dtype <- lookupDataType op tenv ->
           dataTypeIsAbstract dtype
         _ -> False

-- | Deconstruct a parameter into its component fields.
--
--   Specificity about the fields of the data value, if available, is used
--   to direct the deconstruction plan.  Types inside the specificity are
--   ignored.
planDeconstructedValue :: (ReprDictMonad m, EvalMonad m) =>
                          PlanMode -> Var -> [Type] -> Maybe [Specificity]
                       -> m Decomp
planDeconstructedValue mode con ty_args maybe_fields = do
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
      return $ DeconDecomp (VarDeCon con ty_args ex_params) field_plans

    _ -> internalError "planDeconstructedValue: Unknown data constructor"
  where
    plan_fields ((f_type, f_specificity):fs) = do
      -- Decide how to deconstruct
      (whnf_f_type, f_decomp) <- planFlattening mode f_type f_specificity
      
      -- Create a new pattern for this field
      v <- newAnonymousVar ObjectLevel
      let f_plan = FlatArg (patM (v ::: whnf_f_type)) f_decomp

      -- Process remaining fields
      fs_plans <- assume v f_type $ plan_fields fs
      return (f_plan : fs_plans)
    
    plan_fields [] = return []

-- | Construct an arbitrary value of the given type to replace an expression 
--   whose value is dead.  The argument should be in WHNF.
deadValue t = do
  tenv <- getTypeEnv
  case toBaseKind $ typeKind tenv t of
    ValK ->
      case fromTypeApp t
      of (VarT con, [])
           | con `isPyonBuiltin` The_NoneType ->
               return noneValue
           | con `isPyonBuiltin` The_int ->
               return $ ExpM $ LitE defaultExpInfo $ IntL 0 t
           | con `isPyonBuiltin` The_float ->
               return $ ExpM $ LitE defaultExpInfo $ FloatL 0 t
         (VarT con, [p])
           | con `isPyonBuiltin` The_Pf ->
               return $ ExpM $ AppE defaultExpInfo dead_proof_op [TypM p] [] 
           | con `isPyonBuiltin` The_FIInt -> do
               -- Use 'finIndInt' as the data constructor
               -- Get types of data constructor parameters
               let Just datacon_type =
                     lookupType (pyonBuiltin The_fiInt) tenv
               Just monotype <- liftTypeEvalM $ typeOfTypeApp datacon_type intindexT p
               let (dom, _) = fromFunType monotype

               -- Create arguments to data constructor
               args <- mapM deadValue dom
               let expr = ExpM $ AppE defaultExpInfo dead_finindint_op
                          [TypM p] args
               return expr
         (CoT BoxK, [t1, t2]) ->
           return $ ExpM $ AppE defaultExpInfo make_coercion_op [TypM t1, TypM t2] []
         _ -> traceShow (pprType t) $ internalError "deadValue: Not implemented for this type"
    BoxK ->
      return dead_box
    BareK ->
      return dead_bare
    _ -> internalError "deadValue: Unexpected kind"
  where
    dead_box = ExpM $ AppE defaultExpInfo dead_box_op [TypM t] []
    dead_bare = ExpM $ AppE defaultExpInfo dead_bare_op [TypM t] []
    dead_box_op = ExpM $ VarE defaultExpInfo (pyonBuiltin The_deadBox)
    dead_bare_op = ExpM $ VarE defaultExpInfo (pyonBuiltin The_deadRef)
    dead_proof_op = ExpM $ VarE defaultExpInfo (pyonBuiltin The_deadProof)
    dead_finindint_op = ExpM $ VarE defaultExpInfo (pyonBuiltin The_fiInt)
    make_coercion_op = ExpM $ VarE defaultExpInfo (pyonBuiltin The_unsafeMakeCoercion)

planReturn :: (ReprDictMonad m, EvalMonad m) =>
              PlanMode -> Specificity -> TypM -> m FlatRet
planReturn mode spc (TypM ty) = do
  (whnf_type, decomp) <- planFlattening mode ty spc
  return $ FlatRet whnf_type decomp

-- | Determine how to decompose a return value based on its type.
--   The returned plan is for transforming a return-by-value function only.
planValueReturn :: (ReprDictMonad m, EvalMonad m) =>
                   TypM -> m PlanRet
planValueReturn ty = liftM PlanRetValue $ planReturn mode Used ty
  where
    mode = PlanMode LiberalSmall Don'tUnpackExistentials

-- | Determine how to decompose a return value based on its type.
--   The returned plan is for transforming an initializer function only.
planOutputReturn :: (ReprDictMonad m, EvalMonad m) =>
                    PatM -> m PlanRet
planOutputReturn pat = do
  tenv <- getTypeEnv
  let return_type =
        case fromVarApp $ patMType pat
        of Just (op, [arg]) | op `isPyonBuiltin` The_OutPtr -> arg
           _ -> internalError "planOutputReturn: Expecting an output pointer"
  flat_ret <- planReturn mode Used $ TypM return_type

  -- Only perform decomposition if everything was converted to a value
  let real_ret =
        if unpacksToAValue tenv flat_ret
        then flat_ret
        else FlatRet (frType flat_ret) IdDecomp
  return $ PlanRetWriter pat real_ret
  where
    mode = PlanMode LiberalSmall Don'tUnpackExistentials

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
      boxed_type = varApp (pyonBuiltin The_Boxed) [arg_type]
      boxed_param = patM (boxed_var ::: boxed_type)
      
      boxed_mono_con = VarDeCon (pyonBuiltin The_boxed) [arg_type] []
      boxed_decomp = DeconDecomp boxed_mono_con [arg]

  in FlatLocal (FlatArg boxed_param boxed_decomp)

-- | Create the original form of the local variable, using the flattened
--   variables
packLocal :: (ReprDictMonad m, EvalMonad m) => FlatLocal -> ExpM -> m ExpM
packLocal (FlatLocal flat_arg) consumer = do
  (_, packing_context) <- packParameterRead flat_arg
  return $ packing_context consumer

-- | Determine how to decompose a let-bound value based on its type.
--
--   The decomposition strategy is the same as for decomposing a return value.
planLocal :: (ReprDictMonad m, EvalMonad m) => PatM -> m FlatLocal
planLocal pat = do
  flat_arg <- planParameter mode pat
  tenv <- getTypeEnv
  choose_flattening tenv flat_arg
  where
    mode = PlanMode Parsimonious UnpackExistentials
    choose_flattening tenv flat_arg@(FlatArg pat decomp) = 
      case decomp
      of DeconDecomp {}
           -- Don't decompose if some fields are bare references
           | not $ unpacksToAValue tenv $ flatArgReturn flat_arg ->
               return $ FlatLocal (FlatArg pat IdDecomp)
         _ -> return $ FlatLocal flat_arg

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
planRetOriginalInterface (PlanRetValue fr) =
  ([], TypM $ frType fr)

planRetOriginalInterface (PlanRetWriter p fr) =
  -- The return type is an effect type
  let ret_type = varApp (pyonBuiltin The_IEffect) [frType fr]
  in ([p], TypM ret_type)

-- | Get the flattened return parameter and return type
--   of a return flattening plan.
--   They are used in the worker function.
planRetFlattenedInterface :: TypeEnv -> PlanRet -> ([PatM], TypM)
planRetFlattenedInterface tenv (PlanRetValue fr) =
  ([], flattenedReturnType tenv fr)

planRetFlattenedInterface tenv (PlanRetWriter p fr) =
  case frDecomp fr
  of IdDecomp ->
       ([p], TypM $ varApp (pyonBuiltin The_IEffect) [frType fr])
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

printPlan :: Var -> FunctionPlan -> IO ()
printPlan f (FunctionPlan ty_params args ret) = do
  putStrLn $ "Plan for function " ++ show f
  print $ text "Parameters" <+> vcat (map pprFlatArg args)
  flat_ret <-
    case ret
    of PlanRetValue r -> do
         print $ text "Returns by value" <+> pprType (frType r)
         return r
       PlanRetWriter p r -> do
         print $ text "Returns by output pointer" <+> pprPat p
         return r
  print $ nest 4 $ pprDecomp $ frDecomp flat_ret
  
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
  in if null params && null ty_params
     then -- If this happens, the 'FunctionPlan' value is wrong.
          internalError "flattenedFunctionInterface: No parameters"
     else (ty_params, params, return_type)

planFunction :: FunM -> AF FunctionPlan
planFunction (FunM f) = assumeTyPatMs (funTyParams f) $ do
  -- Partition parameters into input and output parameters
  tenv <- getTypeEnv
  let (input_params, output_params) = partitionParameters tenv $ funParams f

  params <- planParameters (PlanMode LiberalStored UnpackExistentials) input_params

  -- There should be either one or zero output parameters
  ret <- case output_params
         of []  -> planValueReturn $ funReturn f
            [p] -> planOutputReturn p

  -- If all parameters are dead and there's no output parameter, then add a
  -- dummy parameter
  let no_flattened_output_params =
        case planRetFlattenedInterface tenv ret
        of ([], _) -> True
           _ -> False
  x_params <-
    if all isDeadArg params && no_flattened_output_params
    then do pat_var <- newAnonymousVar ObjectLevel
            let dummy_pat = patM (pat_var ::: VarT (pyonBuiltin The_NoneType))
                dummy = DummyArg dummy_pat
            return (dummy : params)
    else return params

  return $ FunctionPlan (funTyParams f) x_params ret

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
    make_wrapper_body = assumeTyPatMs (originalTyParams plan) $ do
      -- Call the worker function and re-pack its arguments
      tenv <- getTypeEnv
      body <- packReturn (planRetFlatRet $ flatReturn plan) (worker_call tenv)
      
      -- Apply the return argument, if the original function had one
      let ret_body =
            case planRetOriginalInterface $ flatReturn plan
            of ([], _) -> body
               ([p], _) -> let pat_exp = ExpM $ VarE defaultExpInfo (patMVar p)
                           in ExpM $ AppE defaultExpInfo body [] [pat_exp]
      
      -- Flatten function parameters
      return $ flattenParameters (flatParams plan) ret_body

    -- A call to the worker function.  The worker function takes flattened 
    -- function arguments.
    worker_call tenv =
      let orig_ty_args =
            [TypM (VarT a) | TyPatM (a ::: _) <- originalTyParams plan]
          (new_ty_args, input_args) =
            flattenedParameterValues (flatParams plan)
          (output_params, return_type) =
            planRetFlattenedInterface tenv $ flatReturn plan
          output_args = [ExpM $ VarE defaultExpInfo (patMVar p)
                        | p <- output_params]

          ty_args = orig_ty_args ++ new_ty_args
          args = input_args ++ output_args
          worker_e = ExpM $ VarE defaultExpInfo worker_name
          worker_call = appE defaultExpInfo worker_e ty_args args
      in -- If the worker function returns by reference, then lambda-abstract
         -- over its output parameter
         case output_params
         of [] -> worker_call
            [p] -> ExpM $ LamE defaultExpInfo $
                   FunM $ Fun { funInfo = defaultExpInfo
                              , funTyParams = []
                              , funParams = [p]
                              , funReturn = return_type
                              , funBody = worker_call}

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
    create_worker_body = assumeTyPatMs (originalTyParams plan) $ do
      -- If the function returned by reference, then lambda-abstract over 
      -- the original return parameter
      abstracted_body <-
        case flatReturn plan
        of PlanRetValue _ -> return original_body
           PlanRetWriter p fr ->
             let original_ret_type =
                   TypM $ varApp (pyonBuiltin The_IEffect) [frType fr]
             in lambdaAbstractReturn original_ret_type p original_body

      -- Repack the return value
      flat_body <-
        flattenReturnWrite (planRetFlatRet $ flatReturn plan) abstracted_body
      
      -- If the new function returns by reference, then apply to the new
      -- return parameter
      tenv <- getTypeEnv
      let worker_body =
            case planRetFlattenedInterface tenv (flatReturn plan)
            of ([], _) -> flat_body
               ([p], _) -> let out_exp = ExpM $ VarE defaultExpInfo (patMVar p)
                           in appE defaultExpInfo flat_body [] [out_exp]

      -- Repack the parameters
      (_, param_context) <- packParametersRead $ flatParams plan
      return $ param_context worker_body

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
  
  -- For debugging, print the flattening
  when False $ liftIO $ printPlan fun_name plan

  -- Flatten inside the function body
  body <- assumeTyPatMs (funTyParams fun) $ assumePats (funParams fun) $ do
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
  assumeTyPatMs (funTyParams f) $ assumePats (funParams f) $ do
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
     ConE inf con args -> do
       args' <- mapM flattenInExp args
       return $ ExpM $ ConE inf con args'
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
     CoerceE inf from_type to_type body -> do
       body' <- flattenInExp body
       return $ ExpM $ CoerceE inf from_type to_type body'

flattenInAlt :: AltM -> AF AltM
flattenInAlt (AltM alt) =
  assumeBinders (deConExTypes $ fromDeCInstM $ altCon alt) $
  assumePats (altParams alt) $ do
    body' <- flattenInExp (altBody alt)
    return $ AltM $ alt {altBody = body'}

flattenInExport :: Export Mem -> AF (Export Mem)
flattenInExport export = do
  f <- flattenInFun $ exportFunction export
  return $ export {exportFunction = f}

flattenModuleContents :: (Module Mem) -> AF (Module Mem)
flattenModuleContents (Module mod_name imports defss exports) = do
  defss' <- mapM flattenInGroup defss
  exports' <- mapM flattenInExport exports
  return $ Module mod_name imports (concat defss') exports'

flattenArguments :: Module Mem -> IO (Module Mem)
flattenArguments mod =
  withTheNewVarIdentSupply $ \id_supply -> do
    dict_env <- runFreshVarM id_supply createDictEnv
    type_env <- readInitGlobalVarIO the_memTypes
    let env = AFLVEnv id_supply type_env dict_env ()
    runReaderT (unAF $ flattenModuleContents mod) env
