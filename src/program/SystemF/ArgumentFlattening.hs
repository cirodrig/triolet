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

{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, KindSignatures, FlexibleContexts, ConstraintKinds #-}
{-# OPTIONS_HADDOCK ignore-exports #-}
module SystemF.ArgumentFlattening(flattenArguments)
where

import Prelude hiding (mapM, sequence)

import Control.Applicative
import Control.Monad.Reader hiding(mapM, forM, sequence)
import Control.Monad.State hiding(mapM, forM, sequence)
import qualified Data.IntMap as IntMap
import Data.List
import Data.Maybe
import Data.Monoid(Monoid(..), Any(..))
import Data.Traversable
import qualified Data.Set as Set
import Debug.Trace
import GHC.Exts

import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.SourcePos
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
import SystemF.Datatypes.Code
import SystemF.Datatypes.InfoCall
import qualified LowLevel.Syntax as LL
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
fromProductTyCon :: EvalMonad m => Var -> m (Maybe DataConType)
fromProductTyCon ty_op = do
  m_dtype <- lookupDataType ty_op
  case m_dtype of
    Nothing -> return Nothing
    Just data_type ->
      case dataTypeDataConstructors data_type
      of [con] -> do
           m_dcon <- lookupDataCon con
           case m_dcon of
             Just dcon_type -> return $ Just dcon_type
             Nothing -> internalError "fromProductTyCon"
         _ -> return Nothing

fromOutPtrType :: Type -> Type
fromOutPtrType t =
  case fromVarApp t
  of Just (op, [arg]) | op == outPtrV -> arg
     _ -> internalError "fromOutPtrType: Not an output pointer"

storeType = storeT

-- | Bind a variable to a value.
--
--   Creates either a let expression or a case-of-boxed expression, depending
--   on the data type that will be bound.
bindVariable :: Binder -> ExpM -> AF (ExpM -> ExpM)
bindVariable binder rhs = do
  k <- typeBaseKind $ binderType binder
  case k of
    BareK -> bare_binding
    ValK  -> value_binding
    BoxK  -> value_binding
  where
    bare_binding = do
      -- TODO: Restrict to types with known representation, since we can
      -- only generate info for types with known representation
      Just (op, args) <- liftTypeEvalM $ deconVarAppType (binderType binder)
      Just data_type <- lookupDataType op
      rep <- liftMaybeGen $
             callConstantUnboxedInfoFunction data_type args
      return $ \body -> letViaBoxed binder rep rhs body

    value_binding =
      let mk body = ExpM $ LetE defaultExpInfo (patM binder) rhs body
      in return mk

-------------------------------------------------------------------------------
-- * The argument flattening monad

-- | Reader environment used during argument flattening and local variable
--   flattening.
data AFLVEnv a =
  AFLVEnv
  { afVarSupply :: {-# UNPACK #-}!(IdentSupply Var)
  , afLLVarSupply :: {-# UNPACK #-}!(IdentSupply LL.Var)
  , afTypeEnv :: TypeEnv
  , afOther :: a
  }

-- | The monad for argument and local variable flattening
newtype AF a =
  AF {unAF :: ReaderT (AFLVEnv ()) IO a}
  deriving(Functor, Applicative, Monad, MonadIO)

instance Supplies AF (Ident Var) where
  fresh = AF $ ReaderT $ \env -> supplyValue $ afVarSupply env

getLLVarSupply = AF $ asks afLLVarSupply

liftMaybeGen :: Gen (Maybe ExpM) -> AF ExpM
liftMaybeGen m = do
  s <- getLLVarSupply
  liftTypeEvalM $ runMaybeGen s m

liftFreshVarAF :: FreshVarM a -> AF a
liftFreshVarAF m = AF $ ReaderT $ \env -> runFreshVarM (afVarSupply env) m

instance TypeEnvMonad AF where
  type EvalBoxingMode AF = UnboxedMode
  getTypeEnv = AF $ asks afTypeEnv
  {-assumeWithProperties v t b m = AF $ local insert_type $ unAF m
    where
      insert_type env =
        env {afTypeEnv = insertTypeWithProperties v t b $ afTypeEnv env}-}

{-instance ReprDictMonad (AFMonad e) where
  getVarIDs = AF $ asks afVarSupply
  getDictEnv = AF $ asks afDictEnv
  localDictEnv f m =
    AF $ local (\env -> env {afDictEnv = f $ afDictEnv env}) $ unAF m-}

instance EvalMonad AF where
  liftTypeEvalM m = AF $ ReaderT $ \env -> do
    runTypeEvalM m (afVarSupply env) (afTypeEnv env)

assumePat :: EvalMonad m => PatM -> m a -> m a
assumePat pat m = assumeBinder (patMBinder pat) m

assumePats :: EvalMonad m => [PatM] -> m a -> m a
assumePats pats m = foldr assumePat m pats

assumeDef :: TypeEnvMonad m => FDef Mem -> m a -> m a
assumeDef d m = assume (definiendum d) (functionType $ definiens d) m

-- | Apply the transformation to each expression in tail position.
--   Look through let, letfun, and case statements.
mapOverTailExps :: EvalMonad m =>
                   (ExpM -> m ExpM) -> ExpM -> m ExpM
mapOverTailExps f expression =
  case fromExpM expression
  of LetE inf binder rhs body -> do
       body' <- assumePat binder $ mapOverTailExps f body
       return $ ExpM $ LetE inf binder rhs body'
     LetfunE inf defs body -> do
       ((), body') <- assumeFDefGroup defs (return ()) $ mapOverTailExps f body
       return $ ExpM $ LetfunE inf defs body'
     CaseE inf scr sps alts -> do
       alts' <- mapM map_alt alts
       return $ ExpM $ CaseE inf scr sps alts'
     _ -> f expression
  where
    map_alt (AltM alt) =
      assumeBinders (deConExTypes $ altCon alt) $
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
isSmallDecomp :: EvalMonad m => (Type, Decomp) -> m Bool
isSmallDecomp (ty, decomp) =
  case decomp
  of IdDecomp -> is_small_type ty
     DeadDecomp {} -> return True
     DeconDecomp decon fields ->
       -- True if all fields are small
       assumeBinders (deConExTypes decon) $
       allM isSmallDecomp [(patMType p, d) | FlatArg p d <- fields]          
  where
    is_small_type t = do
      t' <- reduceToWhnf t
      k <- typeBaseKind t
      cond ()
        [ -- Values and boxed objects are cheap to copy
          do aguard $ k == ValK || k == BoxK
             return True

          -- 'Stored' contains a value, which is cheap to copy
        , do Just (op, [arg]) <- lift $ liftTypeEvalM $ deconVarAppType t'
             aguard $ op == storedV
             return True

          -- Tuples are cheap to copy if their contents are
        , do Just (op, args) <- lift $ liftTypeEvalM $ deconVarAppType t'
             aguard $ isTupleTypeCon op
             lift $ allM (\x -> isSmallDecomp (x, IdDecomp)) args
        , return False
        ]

-- | Determine whether all decomposed items are values or boxed objects.
--   If so, then it's possible to unpack a return value with this type.
unpacksToAValue :: EvalMonad m => FlatRet -> m Bool
unpacksToAValue (FlatRet ty IdDecomp) = do
  k <- typeBaseKind ty
  return $! case k
            of ValK -> True
               BoxK -> True
               _    -> False

unpacksToAValue (FlatRet _ (DeconDecomp decon fs))
  | null (deConExTypes decon) =
      allM unpacksToAValue [(flatArgReturn f) | f <- fs]
  | otherwise =
      return False

unpacksToAValue (FlatRet _ (DeadDecomp _)) = return True

-- | Flatten a decomposition.  Decomposed type parameters and fields are
--   transformed and collected by a monoid.
flattenDecomp :: Monoid a =>
                 (TyPat -> a)  -- ^ Extract value from a type parameter
              -> (PatM -> a)    -- ^ Extract value from a field
              -> a              -- ^ Value of an identity decomposition
              -> Decomp         -- ^ Decomposition to flatten
              -> a              -- ^ Flattened value
flattenDecomp typaram field x decomp = go x decomp
  where
    go x IdDecomp = x
    go _ (DeadDecomp _) = mempty
    go _ (DeconDecomp decon fields) =
      mconcat $ map (typaram . TyPat) (deConExTypes decon) ++
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

-- | Add a packed argument to the environment
assumePackedArg (FlatArg pat _) m = assumePat pat m
assumePackedArg (DummyArg _)    m = m

-- | Add a packed argument to the environment.
--
--   The packed argument may be needed to generate copying
--   code, even if the argument was labeled \'deconstructed\' or \'unused\'
--   (which would cause the argument to be eliminated).
--
--   Only a few type-indexed values can be used this way.  First the 
--   type is checked to see if it may be needed.  If so, code is added
--   to the dictionary environment to rebuild the argument.
assumeRepackedArg (DummyArg _)    m = m
assumeRepackedArg (FlatArg pat IdDecomp) m =
  -- The argument is available as a function parameter
  assumePat pat m

assumeRepackedArg flat_arg@(FlatArg pat decomp) m = do
  -- The argument is not available as a function parameter.
  -- Reconstruct it based on available data.
  assumePat pat m
  {-
  assumeBinder (patMBinder pat) m
  ty <- reduceToWhnf $ patMType pat
  case fromVarApp ty of
    Just (op, [arg])
      | op `isCoreBuiltin` The_Repr -> 
          assumeBinder (patMBinder pat) $ save_dict saveReprDict arg
        | op `isCoreBuiltin` The_ShapeDict -> 
          assumeBinder (patMBinder pat) $ save_dict saveShapeDict arg
        | op `isCoreBuiltin` The_FIInt ->
          assumeBinder (patMBinder pat) $ save_dict saveIndexedInt arg
    _ -> m
  where
    save_dict save ty = save ty (rebuild_dict flat_arg) m

    rebuild_dict flat_arg = MkDict $ do
      -- If the argument was dead, we don't have enough information to
      -- rebuild it.  In that case, we should never needed the argument.
      when (case decomp of {DeadDecomp _ -> True; _ -> False}) $
        internalError "assumeRepackedArg: Attempted to use dead argument"

      -- Since this is not a bare type, the return value can also be read from
      Just e <- packParameterWrite flat_arg
      return e -}

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
flattenedParameter :: FlatArg -> ([TyPat], [PatM])
flattenedParameter (FlatArg pat decomp) =
  flattenDecomp put_typat put_pat (put_pat pat) decomp
  where
    put_typat p = ([p], [])
    put_pat p = ([], [p])

flattenedParameter (DummyArg pat) = ([], [pat])

-- | Get the flattened argument list from a sequence of flattened parameters
flattenedParameters :: FlatArgs -> ([TyPat], [PatM])
flattenedParameters xs = mconcat $ map flattenedParameter xs

flattenedParameterValue :: FlatArg -> ([Type], [ExpM])
flattenedParameterValue (FlatArg pat decomp) =
  flattenDecomp put_typat put_pat (put_pat pat) decomp
  where
    put_typat (TyPat (a ::: _)) = ([VarT a], [])
    put_pat p = ([], [ExpM $ VarE defaultExpInfo (patMVar p)])

flattenedParameterValue (DummyArg _) =
  ([], [noneE defaultExpInfo])

-- | Get the flattened parameter values from a sequence of flattened
--   parameters.  Each value is a type variable or variable expression.
flattenedParameterValues :: FlatArgs -> ([Type], [ExpM])
flattenedParameterValues xs = mconcat $ map flattenedParameterValue xs

-- | Information about a list of decomposed return parameters.
-- @Nothing@ means that return parameters are not decomposed.
-- @Just xs@ describes a return parameter that has been decomposed into a list
-- of @length xs@ parameters.
newtype ReturnParameters a = ReturnParameters (Maybe [a])

instance Monoid (ReturnParameters a) where
  -- 'mempty' corresponds to an empty list of decomposed parameters.
  mempty = ReturnParameters (Just [])
  ReturnParameters x `mappend` ReturnParameters y =
    ReturnParameters (x `mappend` y)

flattenReturnDecomp :: (PatM -> a) -> Decomp -> Maybe [a]
flattenReturnDecomp f decomp =
  let append_parameter p = ReturnParameters (Just [f p])
      not_decomposed = ReturnParameters Nothing
  in case flattenMonoDecomp append_parameter not_decomposed decomp
     of ReturnParameters x -> x

-- | Get the flattened return type.  Only valid if
--   @flattenedReturnsBySideEffect flat_ret == False@.
flattenedReturnType :: EvalMonad m => FlatRet -> m Type
flattenedReturnType flat_ret =
  let flat_type = frType flat_ret
      flat_decomp = frDecomp flat_ret
  in case flattenReturnDecomp patMType flat_decomp
     of Just [t] -> return t
        Just ts  -> liftTypeEvalM $ unboxedTupleType ts
        Nothing  -> return flat_type

-- | Get the parameter list to use to bind the flattened return values
flattenedReturnParameters :: FlatRet -> Maybe [PatM]
flattenedReturnParameters flat_ret =
  flattenReturnDecomp id $ frDecomp flat_ret

-- | Get the flattened return value expression for a return value that has
--   been decomposed.  The expression is either a tuple or a single variable,
--   containing bound return value patterns.
--   It's an error to call this function if the return value does not specify
--   to decompose.
flattenedReturnValue :: FlatRet -> ExpM
flattenedReturnValue flat_ret =
  case flattenReturnDecomp var_exp $ frDecomp flat_ret
  of Just [e] -> fst e
     Just es  -> let (values, types) = unzip es
                 in valConE' (TupleCon types) values
     Nothing  -> internalError "flattenedReturnValue"
  where
    var_exp pat = (ExpM $ VarE defaultExpInfo (patMVar pat), patMType pat)

-- | Given the variable bindings returned by 'flattenedReturnParameters', 
--   and a flattened return value, bind the flattened return variables.
bindFlattenedReturn :: (EvalBoxingMode m ~ UnboxedMode, EvalMonad m) =>
                       ExpInfo -> [PatM] -> ExpM -> ExpM -> m ExpM
bindFlattenedReturn inf [p] source_exp body =
  -- Single value.  Assign the expression result to the pattern variable.
  return $ ExpM $ LetE inf p source_exp body

bindFlattenedReturn inf patterns source_exp body =
  -- Multiple or zero return values.  Deconstruct the
  -- expression result with a case statement, then repack.
  let pattern_types = map patMType patterns
      decon = TupleDeCon pattern_types
  in return $ ExpM $ CaseE defaultExpInfo source_exp []
     [AltM $ Alt decon Nothing patterns body]

-------------------------------------------------------------------------------
-- * Value packing and unpacking transformations

-- | Generate code to flatten a parameter in the context of an expression.
--
--   The parameter is assumed to be bound in the surrounding code.  The
--   generated code deconstructs the parameter variable and binds its fields.
flattenParameter :: FlatArg -> ExpM -> AF ExpM
flattenParameter (FlatArg pat decomp) body =
  case decomp
  of IdDecomp -> return body
     DeconDecomp decon fields -> do
       -- Further deconstruct the fields of the parameter value
       body' <- flattenParameters fields body

       -- Deconstruct the parameter variable
       decon_param <- deconExpression decon (map faPattern fields) body'
       let pattern_exp = ExpM $ VarE defaultExpInfo (patMVar pat)       
       return $ decon_param pattern_exp
     DeadDecomp _ -> return body

flattenParameter (DummyArg _) body = return body

flattenParameters :: [FlatArg] -> ExpM -> AF ExpM
flattenParameters (arg:args) e =
  flattenParameter arg =<< flattenParameters args e

flattenParameters [] e = return e

packParametersWrite :: FlatArgs -> AF [ExpM]
packParametersWrite (arg:args) = do
  e <- packParameterWrite arg
  es <- assumeRepackedArg arg $ packParametersWrite args
  return (maybe id (:) e es)

packParametersWrite [] = return []

-- | Pack a parameter whose result will be written to a destination
--
--   TODO: Don't return the parameter expression.  It's always just the
--   pattern variable.
packParameterWrite :: FlatArg -> AF (Maybe ExpM)
packParameterWrite (FlatArg pat flat_arg) =
  liftM Just $ packParameterWrite' pat flat_arg

packParameterWrite (DummyArg _) = return Nothing
  
packParameterWrite' :: PatM -> Decomp -> AF ExpM
packParameterWrite' pat flat_arg =
  case flat_arg
  of IdDecomp -> copy_expr (patMType pat) (var_exp $ patMVar pat)
     DeconDecomp (VarDeCon con_var types ex_params) fields ->
       assumeBinders ex_params $ do
         exps <- packParametersWrite fields
         
         let ex_types = [VarT a | a ::: _ <- ex_params]

         -- Generate size parameters
         Just dcon_type <- lookupDataCon con_var
         let data_type = dataConType dcon_type
         size_param_types <- instantiateSizeParams data_type types
         sps <- forM size_param_types $ \kt ->
           liftMaybeGen $ constructConstantSizeParameter kt

         -- Generate type object
         ty_ob <- case dataTypeKind data_type
                  of BoxK -> do
                       e <- liftMaybeGen $
                            callConstantBoxedInfoFunction dcon_type types ex_types
                       return $ Just e
                     _ -> return Nothing

         -- Construct/initialize a value
         let con = VarCon con_var types ex_types
             
         return $ conE' con sps ty_ob exps

     DeadDecomp e -> return e
  where
    var_exp v = ExpM $ VarE defaultExpInfo v
    
    copy_expr ty src = do
      k <- typeBaseKind ty
      case k of
        BareK -> do
          -- Insert a copy operation
          -- The type must have a statically known size
          size <- liftMaybeGen $
                  constructConstantSizeParameter (KindedType BareK ty)
          return $ appE defaultExpInfo copy_op [ty] [size, src]
        _ ->
          return src
    
    copy_op = ExpM $ VarE defaultExpInfo (coreBuiltin The_blockcopy)

-- | Pack a parameter, so that the result is readable
packParametersRead :: FlatArgs -> AF (ExpM -> ExpM)
packParametersRead (arg : args) = do
  ctx <- packParameterRead arg
  ctxs <- assumePackedArg arg $ packParametersRead args
  return (ctx . ctxs)

packParametersRead [] = return id

-- | Pack a parameter
--
--   TODO: Don't return the parameter expression.  It's always just the
--   pattern variable.
packParameterRead :: FlatArg -> AF (ExpM -> ExpM)
packParameterRead (FlatArg pat flat_arg) =
  case flat_arg
  of IdDecomp ->
       return id
     DeconDecomp (VarDeCon con_var types ex_types) fields ->
       assumeBinders ex_types $ do
         exps <- packParametersWrite fields
         let con = VarCon con_var types [VarT a | a ::: _ <- ex_types]
         packed <- conExpression con exps
         
         -- If this is a bare type, define a local variable with the
         -- packed parameter.  Otherwise, just assign a local variable.
         bindVariable (patMBinder pat) packed

     DeadDecomp e -> do
       -- Assign the expression to a temporary variable
       bindVariable (patMBinder pat) e
  where
    var_exp v = ExpM $ VarE defaultExpInfo v

packParameterRead (DummyArg _) = return id

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
flattenReturnWrite :: FlatRet -> ExpM -> AF ExpM
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
      flattenParameters flat_fields flattened_value

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
deconReturn :: DeConInst          -- ^ Constructor to match against
            -> FlatArgs           -- ^ Fields to deconstruct
            -> ([ExpM] -> AF ExpM) -- ^ Deconstruct initializers
            -> AF ExpM             -- ^ Deconstruct values bound to patterns
            -> ExpM               -- ^ Expression to deconstruct
            -> AF ExpM             -- ^ Deconstructor
deconReturn decon dc_fields decon_initializers decon_patterns expression =
  mapOverTailExps decon_tail expression
  where
    decon_tail tail_exp = do
      tenv <- getTypeEnv

      -- Attempt to deconstruct the tail expression
      case tail_exp of
        ExpM (ConE inf con _ _ fields)
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
      case_of <- deconExpression decon (map faPattern dc_fields) consumer_exp

      -- Bind the expression result
      (_, data_type) <-
        conType (case decon
                 of VarDeCon v ty_args ex_types ->
                      VarCon v ty_args [VarT v | v ::: _ <- ex_types]
                    TupleDeCon ty_args ->
                      TupleCon ty_args)
      k <- typeBaseKind data_type
      case k of
        BareK -> deconstruct_writer data_type tail_exp case_of
        ValK  -> deconstruct_value tail_exp case_of
        BoxK  -> deconstruct_value tail_exp case_of

    -- Deconstruct the result of a writer expression.
    -- The result is bound to a local variable, then deconstructed to bind
    -- its fields to variables.
    deconstruct_writer local_type tail_exp case_of = do
      -- Run the write and bind its result to a new variable
      local_var <- newAnonymousVar ObjectLevel
      let VarDeCon dcon ty_args _ = decon
      Just (data_type, _) <- lookupDataConWithType dcon
      let var_exp = ExpM $ VarE defaultExpInfo local_var

      -- TODO: representation for 'letViaboxed'
      rep <- liftMaybeGen $
             callConstantUnboxedInfoFunction data_type ty_args
      return $ letViaBoxed (local_var ::: local_type) rep tail_exp (case_of var_exp)
    
    -- Deconstruct a value.
    deconstruct_value tail_exp case_of = return $ case_of tail_exp

-- | Create a deconstructor expression
deconExpression decon@(VarDeCon con ty_args ex_binders) params body = do
  Just (data_type, dcon_type) <- lookupDataConWithType con

  -- Construct type object parameter
  ty_ob_param <-
    case dataTypeKind data_type
    of BoxK -> do info_type <- instantiateInfoType data_type ty_args 
                  v <- newAnonymousVar ObjectLevel
                  return $ Just $ patM (v ::: info_type)
       _ -> return Nothing

  -- Construct size parameters
  sp_types <- instantiateSizeParams data_type ty_args
  sps <- forM sp_types $ \kt -> liftMaybeGen $
                                constructConstantSizeParameter kt

  let match = AltM $ Alt decon ty_ob_param params body
      case_of scrutinee = ExpM $ CaseE defaultExpInfo scrutinee sps [match]
  return case_of

deconExpression decon@(TupleDeCon ty_args) params body =
  let match = AltM $ Alt decon Nothing params body
      case_of scrutinee = ExpM $ CaseE defaultExpInfo scrutinee [] [match]
  in return case_of

conExpression con@(VarCon v ty_args ex_args) fields = do
  Just (data_type, dcon_type) <- lookupDataConWithType v

  -- Construct type object
  ty_ob <-
    case dataTypeKind data_type
    of BoxK -> liftM Just $ liftMaybeGen $
               callConstantBoxedInfoFunction dcon_type ty_args ex_args
       _ -> return Nothing

  -- Construct size parameters
  sp_types <- instantiateSizeParams data_type ty_args
  sps <- forM sp_types $ \kt -> liftMaybeGen $
                                constructConstantSizeParameter kt

  return $ conE' con sps ty_ob fields

-- | Given a list of initializer expressions and argument flattening
--   specifications, flatten all initializer values.  All variables in the 
--   flattened arguments are bound.
flattenReturnFields :: [(ExpM, FlatArg)] -> ExpM -> AF ExpM
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
flattenLocalWrite :: FlatLocal -> ExpM -> ExpM -> AF ExpM
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
      flattenParameters flat_args consumer

{-
-- | Flatten a local read value.
--
--   For value or boxed types, this simply calls 'flattenLocalWrite'.
--   For bare types, the value is bound to a variable, then deconstructed
--   with 'flattenParameter'.
flattenLocalRead :: FlatLocal -> ExpM -> ExpM -> AF ExpM
flattenLocalRead flat_local@(FlatLocal flat_arg) expr consumer = do
  k <- typeBaseKind arg_type
  case k of
    BareK -> decon_value
    ValK  -> flattenLocalWrite flat_local expr consumer
    BoxK  -> flattenLocalWrite flat_local expr consumer
  where
    arg_type = patMType $ faPattern flat_arg

    -- Bind the value to the original pattern, deconstruct it,
    -- and finally consume it
    decon_value = do
      decon_expr <- flattenParameter flat_arg consumer
      return $ ExpM $ LetE defaultExpInfo (faPattern flat_arg) expr decon_expr
-}

-- | Transform a flattened return value to packed form
packReturn :: FlatRet -> ExpM -> AF ExpM
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
          DeconDecomp _ _ ->
            -- This can occur when returning something isomorphic to the
            -- unit value.  In this case, we should return a zero-tuple.
            return $ valConE' (TupleCon []) []

     Just patterns -> do
       -- Return value was deconstructed (DeconDecomp).
       -- Rebuild the data structure.
       repack_exp <-
         packParameterWrite' (internalError "packReturn") (frDecomp flat_ret)
       
       let inf = case orig_exp of ExpM e -> expInfo e
       bindFlattenedReturn inf patterns orig_exp repack_exp

-- | Lambda-abstract the expression over the given parameter. 
--
--   We use this for abstracting over output pointers.
lambdaAbstractReturn :: EvalMonad m =>
                        Type    -- ^ Expression's return type
                     -> PatM    -- ^ Parameter to abstract over
                     -> ExpM    -- ^ Expression
                     -> m ExpM  -- ^ Create a new expression
lambdaAbstractReturn rtype pat exp =
  mapOverTailExps (lambdaAbstract defaultExpInfo rtype pat) exp

-- | Lambda-abstract over a single parameter, which may already be in scope.
--   Rename the pattern variable to avoid name shadowing.
lambdaAbstract inf rtype pat e = do
  let old_var = patMVar pat
  pat_var <- newClonedVar old_var
  let pat' = patM (pat_var ::: patMType pat)
      renaming = Rename.singleton old_var pat_var
      e' = Rename.rename renaming e
  return $ ExpM $ LamE inf $
           FunM $ Fun { funInfo = inf
                      , funTyParams = []
                      , funParams = [pat']
                      , funReturn = rtype
                      , funBody = e'}

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
planParameters :: PlanMode -> [PatM] -> AF [FlatArg]
planParameters mode pats = do mapM (planParameter mode) pats

-- | Decide how to flatten a function argument.
planParameter :: PlanMode -> PatM -> AF FlatArg
planParameter mode pat = do
  (whnf_type, decomp) <-
    planFlattening mode (patMType pat) (specificity $ patMDmd pat)

  -- Create a new pattern with unknown demand information
  return $ FlatArg (patM (patMVar pat ::: whnf_type)) decomp

-- | Decide how to decompose a data structure.
--   Return the data type and its decomposition.  The data type is the
--   parameter @ty@ reduced to HNF form.
--
--   This function does the real work of 'planParameter' and 'planReturn'.
planFlattening :: PlanMode -> Type -> Specificity -> AF (Type, Decomp)
planFlattening mode ty spc = do
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
           decomp <- planDeconstructedValue mode con args (fmap (map specificity) spcs)
           return (whnf_type, decomp)
         Nothing -> internalError "planParameter': Type mismatch"

    -- If data type has a singleton constructor, then deconstruct it.
    -- However, deconstructing may be disallowed when the constructor has
    -- existential types.
    singleton_decomp =
      cond (fromVarApp whnf_type) $
      [ do Just (op, _) <- it
           Just data_con <- lift $ fromProductTyCon op

           -- Check for existential types
           if (case existentialHandling mode
               of UnpackExistentials -> True
                  Don'tUnpackExistentials ->
                    null $ dataConExTypes data_con)
             then lift $ decon_decomp (dataConCon data_con) Nothing
             else lift $ id_decomp

      , lift id_decomp
      ]

    -- Similar to singleton_decomp, except that decomposition only occurs if
    -- the result of decomposition is small.
    liberal_decomp =
      cond (fromVarApp whnf_type) $
      [ do Just (op, _) <- it
           Just data_con <- lift $ fromProductTyCon op

           -- Check for existential types
           if (case existentialHandling mode
               of UnpackExistentials -> True
                  Don'tUnpackExistentials ->
                    null $ dataConExTypes data_con)
             then lift $ do
               -- Create a decomposition
               ret <- decon_decomp (dataConCon data_con) Nothing

               -- Ensure that the decomposed value is samll
               ifM (isSmallDecomp ret) (return ret) id_decomp
             else lift id_decomp
       , lift id_decomp
       ]

    -- If data type is a Stored type, then deconstruct it.
    stored_decomp =
      case fromVarApp whnf_type
      of Just (op, [arg]) | op == storedV ->
           decon_decomp stored_conV Nothing
         _ -> id_decomp

  cond spc $
    [ -- Don't flatten or remove Repr or FIInt parameters, because later
      -- stages of the compiler might want to access them.
      do Just (op, _) <- return $ fromVarApp whnf_type
         aguard (op == coreBuiltin The_Repr || op == coreBuiltin The_FIInt)
         lift id_decomp

    , -- Remove dead fields
      do Unused <- return spc
         lift dead_decomp

    , -- Don't flatten dictionary parameters.
      -- They can be removed if dead.
      do Just (op, _) <- return $ fromVarApp whnf_type
         aguard $ isDictionaryTypeCon op
         lift id_decomp

    , -- Don't flatten abstract data types.
      -- They can be removed if dead.
      do Just (op, _) <- return $ fromVarApp whnf_type
         Just dtype <- lift $ lookupDataType op
         aguard $ dataTypeIsAbstract dtype
         lift id_decomp

      -- Don't flatten data types whose layout is not statically fixed. 
      -- (Polymorphism can produce types with non-fixed layout).
    , do known_rep <- lift $ liftTypeEvalM $ hasConstantLayout whnf_type
         aguard (not known_rep)
         lift id_decomp

    , do Decond (VarDeCon spc_con _ _) spcs <- it
         lift $ decon_decomp spc_con (Just spcs)

    , -- Unpacking is not implemented for unboxed tuples
      do Decond (TupleDeCon _) spcs <- it
         lift id_decomp

    , do Inspected <- it
         lift singleton_decomp

    , do Copied <- it
         lift singleton_decomp

    , do Used <- it
         lift $ case eagerness mode
                of Parsimonious -> id_decomp
                   LiberalStored -> stored_decomp
                   LiberalSmall -> liberal_decomp
    ]

-- | Deconstruct a parameter into its component fields.
--
--   Specificity about the fields of the data value, if available, is used
--   to direct the deconstruction plan.  Types inside the specificity are
--   ignored.
planDeconstructedValue :: PlanMode -> Var -> [Type] -> Maybe [Specificity]
                       -> AF Decomp
planDeconstructedValue mode con ty_args maybe_fields = do
  m_dcon <- lookupDataCon con
  case m_dcon of
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
  k <- typeBaseKind t
  case k of
    ValK ->
      case fromTypeApp t
      of (VarT con, [])
           | con `isCoreBuiltin` The_NoneType ->
               return $ noneE defaultExpInfo
           | con == intV ->
               return $ ExpM $ LitE defaultExpInfo $ IntL 0 t
           | con == floatV ->
               return $ ExpM $ LitE defaultExpInfo $ FloatL 0 t
           | con `isCoreBuiltin` The_LinearMap -> do
               n <- deadValue (VarT intV)
               let con = VarCon (coreBuiltin The_LinearMap) [] []
               return $ valConE' con [n, n]
         (VarT con, [p])
           | con `isCoreBuiltin` The_FIInt -> do
               -- Use 'finIndInt' as the data constructor
               -- Get types of data constructor parameters
               Just datacon_type <- lookupType $ coreBuiltin The_fiInt
               monotype <- liftTypeEvalM $
                           typeOfTypeApp noSourcePos 1 datacon_type intindexT p
               let (dom, _) = fromFunType monotype

               -- Create arguments to data constructor
               args <- mapM deadValue dom
               let expr = valConE' (dead_finindint_op p) args
               return expr
           | con `isCoreBuiltin` The_IInt -> do
               -- Use 'iInt' as the data constructor
               Just datacon_type <- lookupType (coreBuiltin The_iInt)
               monotype <- liftTypeEvalM $
                           typeOfTypeApp noSourcePos 1 datacon_type intindexT p
               let (dom, _) = fromFunType monotype

               -- Create arguments to data constructor
               args <- mapM deadValue dom
               let expr = valConE' (dead_indint_op p) args
               return expr
           | con `isCoreBuiltin` The_MaybeVal -> do
               -- Create a 'nothing' value
               let op = VarCon (coreBuiltin The_nothingVal) [t] []
                   expr = valConE' op []
               return expr
         (CoT (VarT k), [t1, t2])
           | k == boxV ->
               return $ appE' make_x_coercion_op [t1, t2] []
           | k == bareV ->
               return $ appE' make_b_coercion_op [t1, t2] []
         _ -> internalError "deadValue: Not implemented for this type"
    BoxK ->
      return dead_box
    BareK ->
      return dead_bare
    _ -> internalError "deadValue: Unexpected kind"
  where
    dead_box = appE' dead_box_op [t] []
    dead_bare = appE' dead_bare_op [t] []
    dead_box_op = varE' (coreBuiltin The_deadBox)
    dead_bare_op = varE' (coreBuiltin The_deadRef)
    dead_finindint_op i = VarCon (coreBuiltin The_fiInt) [i] []
    dead_indint_op i = VarCon (coreBuiltin The_iInt) [i] []
    make_x_coercion_op = varE' (coreBuiltin The_unsafeMakeCoercion)
    make_b_coercion_op = varE' (coreBuiltin The_unsafeMakeBareCoercion)

planReturn :: PlanMode -> Specificity -> Type -> AF FlatRet
planReturn mode spc ty = do
  (whnf_type, decomp) <- planFlattening mode ty spc
  return $ FlatRet whnf_type decomp

-- | Determine how to decompose a return value based on its type.
--   The returned plan is for transforming a return-by-value function only.
planValueReturn :: Type -> AF PlanRet
planValueReturn ty = liftM PlanRetValue $ planReturn mode Used ty
  where
    mode = PlanMode LiberalSmall Don'tUnpackExistentials

-- | Determine how to decompose a return value based on its type.
--   The returned plan is for transforming an initializer function only.
planOutputReturn :: PatM -> AF PlanRet
planOutputReturn pat = do
  let return_type = fromOutPtrType $ patMType pat
  flat_ret <- planReturn mode Used return_type

  -- Only perform decomposition if everything was converted to a value
  real_ret <- do
    value <- unpacksToAValue flat_ret
    return $! if value
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
      boxed_type = varApp (coreBuiltin The_Boxed) [arg_type]
      boxed_param = patM (boxed_var ::: boxed_type)
      
      boxed_mono_con = VarDeCon (coreBuiltin The_boxed) [arg_type] []
      boxed_decomp = DeconDecomp boxed_mono_con [arg]

  in FlatLocal (FlatArg boxed_param boxed_decomp)

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
planRetOriginalInterface :: PlanRet -> ([PatM], Type)
planRetOriginalInterface (PlanRetValue fr) =
  ([], frType fr)

planRetOriginalInterface (PlanRetWriter p fr) =
  -- The return type is an effect type
  ([p], storeType)

-- | Get the flattened return parameter and return type
--   of a return flattening plan.
--   They are used in the worker function.
planRetFlattenedInterface :: EvalMonad m => PlanRet -> m ([PatM], Type)
planRetFlattenedInterface (PlanRetValue fr) = do
  rt <- flattenedReturnType fr
  return ([], rt)

planRetFlattenedInterface (PlanRetWriter p fr) =
  case frDecomp fr
  of IdDecomp ->
       return ([p], storeType)
     DeadDecomp {} ->
       -- Dead return values aren't handled currently
       internalError "planRetFlattenedInterface"
     DeconDecomp {} -> do
       rt <- flattenedReturnType fr
       return ([], rt)

type PlanArg = FlatArg
type PlanArgs = FlatArgs

data FunctionPlan =
  FunctionPlan
  { originalTyParams :: [TyPat]
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
  
originalFunctionInterface :: FunctionPlan -> ([TyPat], [PatM], Type)
originalFunctionInterface p =
  let -- Output parameters and return types depend on whether the function
      -- returns by value
      (output_params, return_type) = planRetOriginalInterface $ flatReturn p

      -- Get a list of all original parameters
      input_params = packedParameters $ flatParams p
      params = input_params ++ output_params

  in (originalTyParams p, params, return_type)

flattenedFunctionInterface :: EvalMonad m => FunctionPlan
                           -> m ([TyPat], [PatM], Type)
flattenedFunctionInterface p = do
  (output_params, return_type) <-
    planRetFlattenedInterface $ flatReturn p

  -- Get flattened parameters
  let (new_ty_params, input_params) = flattenedParameters $ flatParams p
      
      params = input_params ++ output_params
      ty_params = originalTyParams p ++ new_ty_params
  if null params && null ty_params
     then -- If this happens, the 'FunctionPlan' value is wrong.
          internalError "flattenedFunctionInterface: No parameters"
     else return (ty_params, params, return_type)

planFunction :: FunM -> AF FunctionPlan
planFunction (FunM f) = assumeTyPats (funTyParams f) $ do
  -- Partition parameters into input and output parameters
  (input_params, output_params) <- liftTypeEvalM $ partitionParameters $ funParams f

  params <- planParameters (PlanMode LiberalSmall UnpackExistentials) input_params

  -- There should be either one or zero output parameters
  ret <- case output_params
         of []  -> planValueReturn $ funReturn f
            [p] -> planOutputReturn p

  -- If all parameters are dead and there's no output parameter, then add a
  -- dummy parameter
  flattened_interface <- planRetFlattenedInterface ret
  let no_flattened_output_params =
        case flattened_interface
        of ([], _) -> True
           _ -> False
  x_params <-
    if all isDeadArg params && no_flattened_output_params
    then do pat_var <- newAnonymousVar ObjectLevel
            let dummy_pat = patM (pat_var ::: VarT (coreBuiltin The_NoneType))
                dummy = DummyArg dummy_pat
            return (dummy : params)
    else return params

  return $ FunctionPlan (funTyParams f) x_params ret

-- | Create a wrapper function.  The wrapper function unpacks function
--   parameters, calls the worker, an repacks the worker's results.
mkWrapperFunction :: FunctionPlan
                  -> DefAnn
                  -> Var        -- ^ Wrapper function name
                  -> Var        -- ^ Worker function name
                  -> AF (FDef Mem)
mkWrapperFunction plan annotation wrapper_name worker_name = do
  wrapper_body <- make_wrapper_body
  let (wrapper_ty_params, wrapper_params, wrapper_ret) = 
        originalFunctionInterface plan
      wrapper = FunM $ Fun { funInfo = defaultExpInfo
                           , funTyParams = wrapper_ty_params
                           , funParams = wrapper_params
                           , funReturn = wrapper_ret
                           , funBody = wrapper_body}
  return $ mkWrapperDef annotation wrapper_name wrapper
  where
    make_wrapper_body = assumeTyPats (originalTyParams plan) $ do
      -- Call the worker function and re-pack its arguments
      worker_call_exp <- worker_call
      body <- packReturn (planRetFlatRet $ flatReturn plan) worker_call_exp
      
      -- Apply the return argument, if the original function had one
      let ret_body =
            case planRetOriginalInterface $ flatReturn plan
            of ([], _) -> body
               ([p], _) -> let pat_exp = ExpM $ VarE defaultExpInfo (patMVar p)
                           in ExpM $ AppE defaultExpInfo body [] [pat_exp]
      
      -- Flatten function parameters
      flattenParameters (flatParams plan) ret_body

    -- A call to the worker function.  The worker function takes flattened 
    -- function arguments.
    worker_call = do
      let orig_ty_args =
            [VarT a | TyPat (a ::: _) <- originalTyParams plan]
          (new_ty_args, input_args) =
            flattenedParameterValues (flatParams plan)
      (output_params, return_type) <-
        planRetFlattenedInterface $ flatReturn plan
      let output_args = [ExpM $ VarE defaultExpInfo (patMVar p)
                        | p <- output_params]

          ty_args = orig_ty_args ++ new_ty_args
          args = input_args ++ output_args
          worker_e = ExpM $ VarE defaultExpInfo worker_name
          worker_call_exp = appE defaultExpInfo worker_e ty_args args

      -- If the worker function returns by reference, then lambda-abstract
      -- over its output parameter
      case output_params of
        [] -> return worker_call_exp
        [p] -> lambdaAbstract defaultExpInfo return_type p worker_call_exp

-- | Create a worker function.  The worker function takes unpacked arguments
--   and returns an unpacked return value.  The worker function body repacks
--   the arguments, runs the original function body, and unpacks its
--   return value.
mkWorkerFunction :: FunctionPlan
                 -> DefAnn
                 -> Var         -- ^ Worker function name
                 -> ExpM        -- ^ Original function body
                 -> AF (FDef Mem)
mkWorkerFunction plan annotation worker_name original_body = do
  worker_body <- create_worker_body
  (worker_ty_params, worker_params, worker_ret) <-
    flattenedFunctionInterface plan
  let worker = FunM $ Fun { funInfo = defaultExpInfo
                          , funTyParams = worker_ty_params
                          , funParams = worker_params
                          , funReturn = worker_ret
                          , funBody = worker_body}
  return $ mkWorkerDef annotation worker_name worker
  where
    create_worker_body = assumeTyPats (originalTyParams plan) $ do
      -- If the function returned by reference, then lambda-abstract over 
      -- the original return parameter
      abstracted_body <-
        case flatReturn plan
        of PlanRetValue _ -> return original_body
           PlanRetWriter p fr ->
             lambdaAbstractReturn storeType p original_body

      -- Repack the return value
      flat_body <-
        flattenReturnWrite (planRetFlatRet $ flatReturn plan) abstracted_body
      
      -- If the new function returns by reference, then apply to the new
      -- return parameter
      flattened_interface <- planRetFlattenedInterface (flatReturn plan)
      let worker_body =
            case flattened_interface
            of ([], _) -> flat_body
               ([p], _) -> let out_exp = ExpM $ VarE defaultExpInfo (patMVar p)
                           in appE defaultExpInfo flat_body [] [out_exp]

      -- Repack the parameters
      param_context <- packParametersRead $ flatParams plan
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
flattenFunctionArguments :: FDef Mem -> AF (Maybe (FDef Mem), FDef Mem)
flattenFunctionArguments def = do
  let fun_name = definiendum def
      fun_annotation = defAnnotation def
      FunM fun = definiens def
  plan <- planFunction (definiens def)
  
  -- For debugging, print the flattening
  when False $ liftIO $ printPlan fun_name plan

  -- Flatten inside the function body
  body <- assumeTyPats (funTyParams fun) $ assumePats (funParams fun) $ do
    flattenInExp $ funBody fun
  
  -- Construct wrapper if it's beneficial
  if isIdPlan plan
    then let fun' = fun {funBody = body} 
         in return (Nothing, mkDef fun_name (FunM fun'))
    else do
      worker_name <- newClonedVar fun_name
      worker <- mkWorkerFunction plan fun_annotation worker_name body
      wrapper <- mkWrapperFunction plan fun_annotation fun_name worker_name
      return (Just worker, wrapper)

-- | Perform flattening in the body of a function, but don't change the
--   function's arguments
flattenInFun :: FunM -> AF FunM
flattenInFun (FunM f) =
  assumeTyPats (funTyParams f) $ assumePats (funParams f) $ do
    fun_body <- flattenInExp $ funBody f
    return $ FunM $ f {funBody = fun_body}

flattenInGroup :: (Def t Mem -> AF (Maybe (Def t Mem), Def t Mem))
               -> DefGroup (Def t Mem) -> AF [DefGroup (Def t Mem)]
flattenInGroup flatten_def (NonRec def) = do
  (m_worker, wrapper) <- flatten_def def
  -- Wrapper can reference worker, but not vice versa; produce two groups
  return $ case m_worker
           of Nothing -> [NonRec wrapper]
              Just w  -> [NonRec w, NonRec wrapper]

flattenInGroup flatten_def (Rec defs) = do
  flattened <- mapM flatten_def defs
  return [Rec $ catMaybes $ concat [[m_worker, Just wrapper]
                                   | (m_worker, wrapper) <- flattened]]

flattenGlobalDef (Def v ann (FunEnt f)) = do
  (m_worker, wrapper) <- flattenFunctionArguments (Def v ann f)
  return (fmap inject_def m_worker, inject_def wrapper)
  where
    inject_def (Def v ann f) = Def v ann (FunEnt f)

flattenGlobalDef def@(Def _ _ (DataEnt _)) =
  return (Nothing, def)

flattenInExp :: ExpM -> AF ExpM
flattenInExp expression =
  case fromExpM expression
  of VarE {} -> return expression
     LitE {} -> return expression
     ConE inf con ty_ob sps args -> do
       ty_ob' <- mapM flattenInExp ty_ob
       sps' <- mapM flattenInExp sps
       args' <- mapM flattenInExp args
       return $ ExpM $ ConE inf con ty_ob' sps' args'
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
       new_defs <- flattenInGroup flattenFunctionArguments defs
       body' <- flattenInExp body
       let mk_letfun d e = ExpM (LetfunE inf d e)
       return $ foldr mk_letfun body' new_defs
     CaseE inf scr sps alts -> do
       scr' <- flattenInExp scr
       sps' <- mapM flattenInExp sps
       alts' <- mapM flattenInAlt alts
       return $ ExpM $ CaseE inf scr' sps' alts'
     ExceptE {} -> return expression
     CoerceE inf from_type to_type body -> do
       body' <- flattenInExp body
       return $ ExpM $ CoerceE inf from_type to_type body'
     ArrayE inf ty es -> do
       es' <- mapM flattenInExp es
       return $ ExpM $ ArrayE inf ty es'

flattenInAlt :: AltM -> AF AltM
flattenInAlt (AltM alt) =
  assumeBinders (deConExTypes $ altCon alt) $
  assumePats (altParams alt) $ do
    body' <- flattenInExp (altBody alt)
    return $ AltM $ alt {altBody = body'}

flattenInExport :: Export Mem -> AF (Export Mem)
flattenInExport export = do
  f <- flattenInFun $ exportFunction export
  return $ export {exportFunction = f}

flattenModuleContents :: (Module Mem) -> AF (Module Mem)
flattenModuleContents (Module mod_name imports defss exports) = do
  defss' <- mapM (flattenInGroup flattenGlobalDef) defss
  exports' <- mapM flattenInExport exports
  return $ Module mod_name imports (concat defss') exports'

flattenArguments :: Module Mem -> IO (Module Mem)
flattenArguments mod =
  withTheNewVarIdentSupply $ \id_supply ->
  withTheLLVarIdentSupply $ \ll_id_supply -> do
    i_type_env <- readInitGlobalVarIO the_memTypes
    type_env <- thawTypeEnv i_type_env
    let env = AFLVEnv id_supply ll_id_supply type_env ()
    runReaderT (unAF $ flattenModuleContents mod) env

