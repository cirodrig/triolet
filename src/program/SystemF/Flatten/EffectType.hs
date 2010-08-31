{-| The effect-annotated types defined in this module closely follow the
--  structure of Core types.  The main difference is in effect and region
--  types.  Unlike in Core, there is no structure to regions: two given 
--  regions are either equal or non-overlapping.  There is no notion of one
--  region being a sub-region of another, or two regions being fields of the 
--  same object.  Effect types are sets of regions.  
--
--  By adopting a simple interpretation of memory, we make unification easy.
--  Core allows a complex view of memory, but we make no attempt to infer
--  effects in core.
-}

{-# LANGUAGE Rank2Types #-}
module SystemF.Flatten.EffectType where

import Control.Monad
import qualified Data.IntMap as IntMap
import Data.Maybe
import qualified Data.Set as Set
import Debug.Trace

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.MonadLogic
import qualified Gluon.Core as Gluon
import Gluon.Core(Con, Var, Binder(..), Binder'(..), Level(..), HasLevel(..))
import Gluon.Eval.Eval
import qualified SystemF.Builtins as SF
import qualified SystemF.Syntax as SF
import qualified Core.Syntax as Core
import Core.Syntax(PassConv(..))
import SystemF.Flatten.Effect

-------------------------------------------------------------------------------
-- Effect types

-- | A function parameter type.  Function parameter types have several parts. 
--   In all cases, one of several possible parameter-passing conventions is 
--   used, and the data that is actually passed has its own type.  Some
--   passing conventions have additional properties.  When a parameter is
--   passed by borrowed reference, it's labeled with a region.
data EParamType =
    -- | A pass-by-value parameter.  The @Maybe Var@ term is the bound
    --   variable of a dependently typed function, or Nothing if this
    --   parameter is not used dependently.
    ValPT (Maybe Var) EType

    -- | A pass-by-owned-reference parameter.
  | OwnPT EType

    -- | A pass-by-read-reference parameter.  The parameter's region is
    -- given.
  | ReadPT RVar EType

paramTypeType :: EParamType -> EType
paramTypeType (ValPT _ t) = t
paramTypeType (OwnPT t) = t
paramTypeType (ReadPT _ t) = t

paramTypeRegion :: EParamType -> Maybe RVar
paramTypeRegion (ReadPT r _) = Just r
paramTypeRegion _ = Nothing

data EReturnType =
    -- | Return by value
    ValRT EType

    -- | Return an owned reference
  | OwnRT EType

    -- | Return a borrowed reference to data that already exists.  Variable
    --   references use this convention.
  | ReadRT RVar EType

    -- | Return by writing into a borrowed reference.  The return region
    -- doesn't reference another region, but rather defines a local region.
  | WriteRT RVar EType

returnTypeType :: EReturnType -> EType
returnTypeType (ValRT t) = t
returnTypeType (OwnRT t) = t
returnTypeType (ReadRT _ t) = t
returnTypeType (WriteRT _ t) = t

-- | A type elaborated with side effect information.
data EType =
    -- | A type application
    AppT EType [EType]

    -- | An application of an effect-polymorphic variable or type constructor
    -- to effect operands.  If the operand list is empty, the variable or
    -- constructor may be either polymorphic (with zero parameters) or
    -- monomorphic.
  | InstT !(Either Var Con) [Effect]
    
    -- | A function type
  | FunT EParamType Effect EReturnType

    -- | An effect-monomorphic type variable
  | VarT !Var
    
    -- | An effect-monomorphic type constructor
  | ConT !Con
  
    -- | A literal or kind
  | LitT !Gluon.Lit

instance HasLevel EType where
  getLevel (AppT op _) = getLevel op
  getLevel (InstT op _) = either getLevel getLevel op
  getLevel (FunT _ _ rt) = getLevel $ returnTypeType rt
  getLevel (VarT v) = getLevel v
  getLevel (ConT c) = getLevel c
  getLevel (LitT l) = Gluon.litLevel l

-- | Get the parameter-passing convention of a value whose type is a
-- fully applied instance of the given data type constructor.  For example,
-- when called with the \'list\' type constructor, the parameter-passing
-- convention for lists is returned.
dataTypePassConv :: Con -> PassConv
dataTypePassConv c 
  | getLevel c /= TypeLevel = internalError "dataTypePassConv: Not a type"
  | otherwise =
      case IntMap.lookup (fromIdent $ Gluon.conID c) dataTypeTable
      of Just (pc, _) -> pc
         Nothing -> internalError $ "dataTypePassConv: No information " ++
                    "for constructor " ++ showLabel (Gluon.conName c)

-- | A table of information about data types, indexed by the type constructor.
dataTypeTable =
  IntMap.fromList [(fromIdent $ Gluon.conID c, (pc, arity)) 
                  | (c, pc, arity) <- assocs]
  where  
    assocs =
      [ (SF.pyonBuiltin SF.the_PassConv, Borrowed, 0)
      , (SF.pyonBuiltin SF.the_int, ByValue, 0)
      , (SF.pyonBuiltin SF.the_float, ByValue, 0)
      , (SF.pyonBuiltin SF.the_bool, ByValue, 0)
      , (SF.pyonBuiltin SF.the_NoneType, ByValue, 0)
      , (SF.pyonBuiltin SF.the_Any, ByValue, 0)
      , (SF.pyonBuiltin SF.the_list, Borrowed, 0)
      , (SF.pyonBuiltin SF.the_Stream, Owned, 1)
      ]

-- | A table of information about functions and data constructors.
dataConTable =
  IntMap.fromList [(fromIdent $ Gluon.conID c, arity)
                  | (c, arity) <- assocs]
  where  
    assocs =
      []

-- | Get the number of effect arguments a type constructor takes.
dataTypeEffectArity :: Con -> Int
dataTypeEffectArity c
  | getLevel c /= TypeLevel = internalError "dataTypeEffectArity: Not a type"
  | otherwise =
      case IntMap.lookup (fromIdent $ Gluon.conID c) dataTypeTable
      of Just (_, arity) -> arity
         Nothing -> internalError $ "dataTypeEffectArity: No information " ++
                    "for constructor " ++ showLabel (Gluon.conName c)

-- | Get the number of effect arguments a data constructor or function takes.
dataConEffectArity :: Con -> Int
dataConEffectArity c
  | getLevel c /= ObjectLevel =
    internalError "dataConEffectArity: Not a value"
  | otherwise =
      case IntMap.lookup (fromIdent $ Gluon.conID c) dataConTable
      of Just arity -> arity
         Nothing -> internalError $ "dataConEffectArity: No information " ++
                    "for constructor " ++ showLabel (Gluon.conName c)

-- | Get the parameter-passing convention to use for an effect type.  The type
-- must be fully applied (this condition is not checked).
--
-- The parameter-passing convention can always be determined from the head
-- term of a type application, so other terms are ignored.
etypePassConv :: EType -> PassConv
etypePassConv ty = head_pass_conv ty
  where
    -- Inspect the head to choose the parameter-passing convention
    head_pass_conv ty =
      case ty
      of AppT op _ -> head_pass_conv op
         InstT (Left v) _ -> Borrowed -- Unknown types are passed 'borrowed'
         InstT (Right c) _ -> dataTypePassConv c
         FunT _ _ _ 
           | getLevel ty == TypeLevel -> Owned -- Functions are passed 'owned'
           | getLevel ty == KindLevel -> ByValue -- Types are passed by value
           | otherwise -> internalError "etypePassConv"
         VarT _ -> Borrowed
         ConT c -> dataTypePassConv c
         LitT (Gluon.KindL _) -> ByValue -- Types are passed by value
         LitT _ -> internalError "etypePassConv: Unexpected literal"

-- | Convert an effect type to a parameter type.  If a parameter variable is
-- given, then the parameter will be used dependently.  An error will be raised
-- if a variable is given and the type is not passed by value.
etypeToParamType :: EType -> Maybe Var -> RegionM EParamType
etypeToParamType ty param_var =
  case etypePassConv ty
  of ByValue -> return $ ValPT param_var ty
     Owned
       | isNothing param_var -> return $ OwnPT ty
       | otherwise -> no_dependent_type
     Borrowed 
       | isNothing param_var -> do
           rgn <- newRegionVar
           return $ ReadPT rgn ty
       | otherwise -> no_dependent_type
  where
    no_dependent_type =
      internalError "etypeToParamType: Parameter cannot be used dependently"

-- | Convert an effect type to a return type
etypeToReturnType :: EType -> RegionM EReturnType
etypeToReturnType ty =
  case etypePassConv ty
  of ByValue  -> return $ ValRT ty
     Owned    -> return $ OwnRT ty
     Borrowed -> do
       rgn <- newRegionVar
       return $ WriteRT rgn ty

-- | An effect type that is assigned to a variable or constructor in the
-- environment
data EffectAssignment =
    MonoEffect EReturnType        -- ^ A monotype
  | PolyEffect [EVar] EReturnType -- ^ An effect-polymorphic type
  | RecEffect EReturnType         -- ^ A recursively defined variable's effect

-------------------------------------------------------------------------------
-- Free effect variables

-- | A set of free effect variables.  Free effect variables are always
-- computed after evaluating the results of unification, so that each 
-- variable is an actual region or effect variable (not an effect).
--
-- Free variables are classified by whether they appear in positive or 
-- negative contexts (or both).  A variable appearing only in positive
-- contexts can be safely underapproximated, while conversely one appearing 
-- only in negative contexts can be safely overapproximated.  If a variable
-- appears in both contexts, it must not be approximated.
data FreeEffectVars =
  FreeEffectVars
  { freePositiveVars :: !(Set.Set EffectVar)
  , freeNegativeVars :: !(Set.Set EffectVar)
  }

modifyPositiveFV, modifyNegativeFV, mapFV
  :: (Set.Set EffectVar -> Set.Set EffectVar)
  -> FreeEffectVars -> FreeEffectVars
modifyPositiveFV f fv = fv {freePositiveVars = f $ freePositiveVars fv}
modifyNegativeFV f fv = fv {freeNegativeVars = f $ freeNegativeVars fv}
mapFV f (FreeEffectVars pos neg) = FreeEffectVars (f pos) (f neg)

emptyFV :: FreeEffectVars
emptyFV = FreeEffectVars Set.empty Set.empty

covariant, contravariant, invariant :: FreeEffectVars -> FreeEffectVars
covariant x = x
contravariant (FreeEffectVars pos neg) = FreeEffectVars neg pos
invariant (FreeEffectVars pos neg) = let u = Set.union pos neg
                                     in FreeEffectVars u u

unionFV :: FreeEffectVars -> FreeEffectVars -> FreeEffectVars
unionFV (FreeEffectVars a b) (FreeEffectVars c d) =
  FreeEffectVars (Set.union a c) (Set.union b d)

unionsFV :: [FreeEffectVars] -> FreeEffectVars
unionsFV = foldr unionFV emptyFV

deleteFV :: EffectVar -> FreeEffectVars -> FreeEffectVars
deleteFV v fv = mapFV (Set.delete v) fv

-------------------------------------------------------------------------------
-- Parametric types

class Parametric e where
  -- | Get the set of free effect variables mentioned in positive and negative
  -- positions, respectively.  A variable amy appear in both positions.
  freeEffectVars :: e -> IO FreeEffectVars

  -- | Replace variables that have been unified with their canonical value
  evaluate :: e -> IO e

  -- | Rename a type variable
  renameT :: Var -> Var -> e -> e

  -- | Rename an effect variable.  The old and new variables must not have
  -- been assigned values.  The argument should be expanded before renaming.
  --
  -- Note that the caller of 'renameE' should expand its expression argument.  
  -- When renameE calls itself recursively, it's not necessary to expand the
  -- argument again.
  renameE :: EffectVar -> EffectVar -> e -> e
  
  -- | Assign a type variable
  assignT :: Var -> EType -> e -> e
  
  -- | Assign an effect variable
  assignE :: EffectVar -> Effect -> e -> e
  
  -- | True if the value mentions the given effect variable;
  -- variable assignments are expanded first
  mentionsE :: e -> EffectVar -> IO Bool
  
  -- | True if the value mentions any of the given effect variables;
  -- variable assignments are expanded first
  mentionsAnyE :: e -> Set.Set EffectVar -> IO Bool

evalAndRenameE :: Parametric exp => EffectVar -> EffectVar -> exp -> IO exp
evalAndRenameE old_v new_v e = liftM (renameE old_v new_v) $ evaluate e

mapParametricEType :: (forall a. Parametric a => a -> a) -> EType -> EType
mapParametricEType f expression =
  case expression
  of AppT ty args   -> AppT (f ty) (map f args)
     InstT op args  -> InstT op (map f args)
     FunT pt eff rt -> FunT (f pt) (f eff) (f rt)
     VarT _         -> expression
     ConT _         -> expression
     LitT _         -> expression

mapParametricEParamType :: (forall a. Parametric a => a -> a)
                        -> EParamType -> EParamType
mapParametricEParamType f expression =
  case expression
  of ValPT pv ty -> ValPT pv (f ty)
     OwnPT ty -> OwnPT (f ty)
     ReadPT rgn ty -> ReadPT rgn (f ty)

mapParametricEReturnType :: (forall a. Parametric a => a -> a)
                         -> EReturnType -> EReturnType
mapParametricEReturnType f expression =
  case expression
  of ValRT ty -> ValRT (f ty)
     OwnRT ty -> OwnRT (f ty)
     ReadRT rgn ty -> ReadRT rgn (f ty)
     WriteRT rgn ty -> WriteRT rgn (f ty)

instance Parametric () where
  freeEffectVars () = return emptyFV
  evaluate () = return ()
  renameT _ _ () = ()
  renameE _ _ () = ()
  assignT _ _ () = ()
  assignE _ _ () = ()
  mentionsE () _ = return False
  mentionsAnyE () _ = return False

mapParametricPair :: (Parametric a, Parametric b) =>
                     (forall c. Parametric c => c -> c)
                  -> (a, b) -> (a, b)
mapParametricPair f (x, y) = (f x, f y)

instance (Parametric a, Parametric b) => Parametric (a, b) where
  freeEffectVars (x, y) = liftM2 unionFV (freeEffectVars x) (freeEffectVars y)
  evaluate (x, y) = liftM2 (,) (evaluate x) (evaluate y)
  renameT old_v new_v = mapParametricPair (renameT old_v new_v)
  renameE old_v new_v = mapParametricPair (renameE old_v new_v)
  assignT old_v new_e = mapParametricPair (assignT old_v new_e)
  assignE old_v new_e = mapParametricPair (assignE old_v new_e)
  (x, y) `mentionsE` v = x `mentionsE` v >||> y `mentionsE` v
  (x, y) `mentionsAnyE` vs = x `mentionsAnyE` vs >||> y `mentionsAnyE` vs

instance Parametric EType where
  freeEffectVars expression =
    case expression
    of AppT op args ->
         liftM (invariant . unionsFV) $ mapM freeEffectVars (op : args)
       InstT op args ->
         -- FIXME: Covariant effect types!
         trace "FIXME: covariant effect types" $
         liftM (invariant . unionsFV) $ mapM freeEffectVars args
       FunT pt eff rt -> do
         fv_param <- freeEffectVars pt
         fv_eff <- freeEffectVars eff
         fv_rt <- freeEffectVars rt
         let fv_range = unionFV fv_eff fv_rt

         -- The parameter variable is not free
         let fv_range_minus_param =
               case paramTypeRegion pt
               of Nothing -> fv_range
                  Just rv -> deleteFV rv fv_range

         return $ unionFV (contravariant fv_param) fv_range_minus_param

       VarT _ -> return emptyFV
       ConT _ -> return emptyFV
       LitT _ -> return emptyFV

  evaluate expression = 
    case expression
    of AppT op args -> AppT `liftM` evaluate op `ap` mapM evaluate args
       InstT op args -> InstT op `liftM` mapM evaluate args
       FunT pt eff rt -> FunT `liftM` evaluate pt `ap` evaluate eff `ap`
                         evaluate rt
       VarT _ -> return expression
       ConT _ -> return expression
       LitT _ -> return expression

  renameT old_v new_v expression =
    case expression
    of VarT v | v == old_v -> VarT new_v
       InstT (Left v) args | v == old_v -> InstT (Left new_v) args
       _ -> mapParametricEType (renameT old_v new_v) expression

  assignT old_v val expression =
    case expression
    of VarT v | v == old_v -> val
       InstT (Left v) [] | v == old_v -> val
       InstT (Left v) _ | v == old_v -> internalError "assignT: Cannot assign polymorphic value"
       _ -> mapParametricEType (assignT old_v val) expression

  renameE old_v new_v expression =
    mapParametricEType (renameE old_v new_v) expression

  assignE old_v val expression =
    mapParametricEType (assignE old_v val) expression

  expression `mentionsE` v =
    case expression
    of AppT op args   -> op `mentionsE` v >||> anyM (`mentionsE` v) args
       InstT _ args   -> anyM (`mentionsE` v) args
       FunT pt eff rt -> pt `mentionsE` v >||>
                         eff `mentionsE` v >||>
                         rt `mentionsE` v
       VarT _         -> return False
       ConT _         -> return False
       LitT _         -> return False

  expression `mentionsAnyE` vs =
    case expression
    of AppT op args -> op `mentionsAnyE` vs >||> anyM (`mentionsAnyE` vs) args
       InstT _ args   -> anyM (`mentionsAnyE` vs) args
       FunT pt eff rt -> pt `mentionsAnyE` vs >||>
                         eff `mentionsAnyE` vs >||>
                         rt `mentionsAnyE` vs
       VarT _        -> return False
       ConT _        -> return False
       LitT _        -> return False

instance Parametric EParamType where
  freeEffectVars (ValPT _ ty) = freeEffectVars ty
  freeEffectVars (OwnPT ty) = freeEffectVars ty
  freeEffectVars (ReadPT rgn ty) = liftM (deleteFV rgn) $ freeEffectVars ty
  
  evaluate (ValPT pv ty) = ValPT pv `liftM` evaluate ty
  evaluate (OwnPT ty) = OwnPT `liftM` evaluate ty
  evaluate (ReadPT rgn ty) = ReadPT rgn `liftM` evaluate ty
  
  renameT old_v new_v expr =
    mapParametricEParamType (renameT old_v new_v) expr

  renameE old_v new_v expr =
    mapParametricEParamType (renameE old_v new_v) expr
  
  assignT v t expr =
    mapParametricEParamType (assignT v t) expr

  assignE v t expr =
    mapParametricEParamType (assignE v t) expr

  expr `mentionsE` v =
    case expr
    of ValPT _ t  -> t `mentionsE` v
       OwnPT t    -> t `mentionsE` v
       ReadPT _ t -> t `mentionsE` v

  expr `mentionsAnyE` v =
    case expr
    of ValPT _ t  -> t `mentionsAnyE` v
       OwnPT t    -> t `mentionsAnyE` v
       ReadPT _ t -> t `mentionsAnyE` v

instance Parametric EReturnType where
  freeEffectVars (ValRT t) = freeEffectVars t
  freeEffectVars (OwnRT t) = freeEffectVars t
  freeEffectVars (ReadRT rgn t) = do
    vs <- freeEffectVars t
    return $ modifyPositiveFV (Set.insert rgn) vs
  freeEffectVars (WriteRT _ t) = freeEffectVars t -- Return region is not free
  
  evaluate (ValRT t) = ValRT `liftM` evaluate t
  evaluate (OwnRT t) = OwnRT `liftM` evaluate t
  evaluate (ReadRT rgn t) = ReadRT rgn `liftM` evaluate t
  evaluate (WriteRT rgn t) = WriteRT rgn `liftM` evaluate t
  
  renameT old_v new_v e =
    mapParametricEReturnType (renameT old_v new_v) e

  renameE old_v new_v expr =
    case expr
    of ReadRT rgn t | old_v == rgn -> ReadRT new_v (renameE old_v new_v t)
       _ -> mapParametricEReturnType (renameE old_v new_v) expr

  assignT old_v new_v e =
    mapParametricEReturnType (assignT old_v new_v) e

  assignE old_v new_v expr =
    case expr
    of ReadRT rgn t | old_v == rgn ->
         internalError "assignE: Cannot replace rigid variable"
       _ -> mapParametricEReturnType (assignE old_v new_v) expr

  expr `mentionsE` v =
    case expr
    of ValRT t -> t `mentionsE` v
       OwnRT t -> t `mentionsE` v
       ReadRT rgn t | rgn == v -> return True
                    | otherwise -> t `mentionsE` v
       WriteRT _ t -> t `mentionsE` v

  expr `mentionsAnyE` vs =
    case expr
    of ValRT t -> t `mentionsAnyE` vs
       OwnRT t -> t `mentionsAnyE` vs
       ReadRT rgn t | rgn `Set.member` vs -> return True
                    | otherwise -> t `mentionsAnyE` vs
       WriteRT _ t -> t `mentionsAnyE` vs

instance Parametric Effect where
  freeEffectVars eff = do
    vars <- effectMembers eff
    return $ FreeEffectVars (Set.fromList vars) Set.empty
  
  evaluate = evalEffect
  
  -- There aren't any types inside effects
  renameT _ _ e = e
  assignT _ _ e = e
  
  renameE = renameInEffect
  assignE = assignInEffect
  
  eff `mentionsE` v = liftM (`effectMentions` v) $ evaluate eff
  eff `mentionsAnyE` vs = do eff' <- evaluate eff
                             return $ any (eff' `effectMentions`) (Set.toList vs)

-------------------------------------------------------------------------------
-- Conversion from System F to effect types

-- | True for dictionary type constructors
isDictionaryTypeCon c =
  c `elem` [ SF.pyonBuiltin SF.the_PassConv
           , SF.pyonBuiltin SF.the_AdditiveDict
           ]

-- | Instantiate a type constructor by inserting new type parameters.  The
-- parameters will acquire values by unification.
instantiateTypeCon :: Bool -> Con -> RegionM EType
instantiateTypeCon no_effects c
  | no_effects = return $ mkPureInstT (Right c) arity
  | otherwise  = mkInstT (Right c) arity
  where
    arity = dataTypeEffectArity c

-- | Create an instance expression where all effect parameters are empty.
mkPureInstT :: Either Var Con -> Int -> EType
mkPureInstT op arity = InstT op (replicate arity emptyEffect)

-- | Create an instance expression from a variable or constructor.
mkInstT :: Either Var Con       -- ^ Variable or constructor to instantiate
        -> Int                  -- ^ Arity (number of effect parameters)
        -> RegionM EType
mkInstT op arity = do
  args <- replicateM arity newEffectVar
  return $ InstT op $ map varEffect args


-- | Convert a System F type to the corresponding effect type.  New effect
-- variables are created to stand for each side effect.  Function types are
-- conservatively assumed to access all their parameters.
toEffectType :: Gluon.WSRExp -> RegionM EType
toEffectType = makeEffectType False

-- | Convert a System F type to the corresponding effect type, with all side
--   effect parameters set to the empty effect.  This conversion is used in
--   type parameters of type classes.
toPureEffectType :: Gluon.WSRExp -> RegionM EType
toPureEffectType = makeEffectType True

-- | This function does the real work of 'initEffectType' and
-- 'initPureEffectType'.
makeEffectType :: Bool -> Gluon.WSRExp -> RegionM EType
makeEffectType no_effects expr =
  case getLevel $ Gluon.fromWhnf $ Gluon.substFullyUnderWhnf expr
  of KindLevel -> makeEffectKind expr
     TypeLevel ->
       case Gluon.unpackRenamedWhnfAppE expr
       of Just (con, args) -> makeConstructorApplication no_effects con args
          Nothing ->
            case Gluon.fromWhnf expr
            of Gluon.FunE {} -> makeFunctionType no_effects expr
     _ -> internalError "makeEffectType"

-- | Convert a kind expression to the representation used in effect types.
-- Kind expressions only contain literals and non-dependnet function types.
-- No effect types are inserted here.
makeEffectKind expr =
  case Gluon.fromWhnf expr
  of Gluon.LitE {Gluon.expLit = lit} -> return $ LitT lit
     Gluon.FunE { Gluon.expMParam = Binder' Nothing dom ()
                , Gluon.expRange = rng} -> do
       dom' <- makeEffectKind =<< evalHead dom
       param <- etypeToParamType dom' Nothing
       rng' <- etypeToReturnType =<< makeEffectKind =<< evalHead rng
       return $ FunT param emptyEffect rng'

makeConstructorApplication no_effects con args = do
  con_inst <- instantiateTypeCon no_local_effects con
  args' <- mapM (makeEffectType no_local_effects <=< evalHead) args
  return $ AppT con_inst args'
  where
    -- Don't let side effects appear in parameters to dictionary types 
    no_local_effects = no_effects || isDictionaryTypeCon con

-- | Create a function type from the expression.  In the type, assume that 
-- all parameters are read.  Side effects from parameters will be placed on 
-- the last arrow.  In other words, the function only produces side effects
-- after all parameters are applied.
makeFunctionType no_effects expr =
  case Gluon.fromWhnf expr
  of Gluon.FunE {Gluon.expMParam = param, Gluon.expRange = rng} -> do
       -- Convert the domain type
       (param, param_effects) <- make_domain_type emptyEffect param

       -- Continue with the range
       (rng', here_effect) <- make_range_type param_effects =<< evalHead rng
       return_type <- etypeToReturnType rng'

       return (FunT param here_effect return_type)

     _ -> internalError "makeFunctionType: Not a function type"
  where
    -- Convert everything on the right hand side of an (->)
    make_range_type param_effects expr =
      case Gluon.fromWhnf expr
      of Gluon.FunE {Gluon.expMParam = param, Gluon.expRange = rng} -> do
           -- Convert the next parameter
           (param, param_effects') <- make_domain_type param_effects param

           -- Continue with the range
           (rng', here_effect) <-
             make_range_type param_effects' =<< evalHead rng
           return_type <- etypeToReturnType rng'

           return (FunT param here_effect return_type, emptyEffect)
         
         _ | getLevel (Gluon.fromWhnf expr) /= TypeLevel ->
               internalError "funTypeToPassType: Expecting a type"
           | otherwise -> do
               -- The function produces a side effect and returns its result
               rng' <- makeEffectType no_effects expr

               -- If side effect variables are allowed here,
               -- create a variable to stand for this expression's free effect
               param_effects' <-
                 if no_effects
                 then return emptyEffect
                 else do
                   effect_var <- newEffectVar
                   return $ param_effects `effectUnion` varEffect effect_var

               return (rng', param_effects')

    -- Convert the parameter on the left side of an (->)
    make_domain_type param_effects (Binder' mv dom ()) = do
      dom' <- makeEffectType no_effects =<< evalHead dom
      param <- etypeToParamType dom' mv
           
      -- Include this parameter in the function's side effect
      let param_effects' =
            param_effects `effectUnion` maybeVarEffect (paramTypeRegion param)
      return (param, param_effects')

-------------------------------------------------------------------------------
-- Conversion from core to effect types

{-
coreToEffectType :: Core.RCType -> RegionM EType -}