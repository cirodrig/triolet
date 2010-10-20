{-|
The effect-annotated types defined in this module closely follow the
structure of Core types.  The main difference is in effect and region
types.  Unlike in Core, there is no structure to regions: two given 
regions are either equal or non-overlapping.  There is no notion of one
region being a sub-region of another, or two regions being fields of the 
same object.  Effect types are sets of regions.  

By adopting a simple interpretation of memory, we make unification easy.
Core allows a complex view of memory, but we make no attempt to infer
effects in core.
-}

{-# LANGUAGE Rank2Types, ViewPatterns #-}
module SystemF.Flatten.EffectType
       (-- * Effect inference types
        EType(..),
        funT,
        conEffectParamVariance,
        etypeOrdinaryParamVariance,
        ERepType(..),
        etypeWithStandardRepr,
        discardTypeRepr,
        EParamType(..),
        paramTypeRepr,
        paramTypeType,
        paramTypeToReturnType,
        freshenParamTypeTypeParam,
        EReturnType(..),
        returnTypeRepr,
        returnTypeType,
        
        -- * Renaming
        Renaming(..),
        idRenaming,
        evalAndApplyRenaming,
        Parametric(..),
        FreeEffectVars(..),
        
        -- * Converting to effect types
        toEffectType,
        toPureEffectType,
        etypeToParamType,
        etypeToReturnType,
        coreToEffectType,
        
        -- * Pretty-printing
        pprEType, pprEReturnType, pprEParamType
       )
where

import Control.Monad
import Control.Monad.Reader
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.MonadLogic
import Gluon.Common.SourcePos
import qualified Gluon.Core as Gluon
import Gluon.Core(Con, Var, Binder(..), Binder'(..), Level(..), HasLevel(..))
import Gluon.Core.Variance
import Gluon.Eval.Eval
import qualified SystemF.Builtins as SF
import qualified SystemF.Syntax as SF
import qualified Core.Syntax as Core
import qualified Core.Print as Core
import Core.Syntax(Representation(..))
import SystemF.Flatten.Effect

-------------------------------------------------------------------------------
-- Effect types

-- | A function parameter type.  Function parameter types have several parts. 
--   In all cases, the parameter's representation and data type are encoded
--   here.  Some passing conventions have additional properties.
--   When a parameter is
--   passed by borrowed reference, it's labeled with a region.
data EParamType =
    -- | A value parameter.  The @Maybe Var@ term is the bound
    --   variable of a dependently typed function, or Nothing if this
    --   parameter is not used dependently.
    ValPT (Maybe Var) EType

    -- | A boxed parameter.
  | OwnPT EType

    -- | A reference parameter.  The parameter's region is given.
  | ReadPT RVar EType

instance HasLevel EParamType where getLevel t = getLevel $ paramTypeType t

paramTypeRepr :: EParamType -> Representation
paramTypeRepr (ValPT {}) = Value
paramTypeRepr (OwnPT {}) = Boxed
paramTypeRepr (ReadPT {}) = Referenced

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

    -- | Return a boxed object
  | OwnRT EType

    -- | Return a borrowed reference to data that already exists.  Variable
    --   references use this convention.
  | ReadRT RVar EType

    -- | Return by writing into a reference.  The return region
    -- doesn't reference another region, but rather defines a local region.
  | WriteRT RVar EType

instance HasLevel EReturnType where getLevel t = getLevel $ returnTypeType t

returnTypeRepr :: EReturnType -> Representation
returnTypeRepr (ValRT {}) = Value
returnTypeRepr (OwnRT {}) = Boxed
returnTypeRepr (ReadRT {}) = Referenced
returnTypeRepr (WriteRT {}) = Referenced

returnTypeType :: EReturnType -> EType
returnTypeType (ValRT t) = t
returnTypeType (OwnRT t) = t
returnTypeType (ReadRT _ t) = t
returnTypeType (WriteRT _ t) = t

-- | Convert a parameter type to a return type.  Given a parameter variable
-- bound at parameter type @p@, its uses will have return type
-- @paramTypeToReturnType p@.
paramTypeToReturnType :: EParamType -> EReturnType
paramTypeToReturnType (ValPT _ t) = ValRT t
paramTypeToReturnType (OwnPT t) = OwnRT t
paramTypeToReturnType (ReadPT rv t) = ReadRT rv t

-- | A type elaborated with representation and side effect information.
--
-- Since representations pertain to values, they are only meaningful on types
-- of kind @*@, that is, types that can be ascribed to values.
-- The representation attached to a type function @T : * -> ... -> *@ is the
-- representation of the corresponding, fully applied type @T a b : *@.
data ERepType = ERepType Representation EType

instance HasLevel ERepType where getLevel (ERepType _ t) = getLevel t

getTypeRepr :: ERepType -> Representation
getTypeRepr (ERepType r _) = r

discardTypeRepr :: ERepType -> EType
discardTypeRepr (ERepType _ t) = t

-- | A type elaborated with side effect information.
data EType =
    -- | A type application
    AppT
    { etypeOper :: EType 
    , etypeArgs :: [EType]
    }

    -- | An application of an effect-polymorphic variable or type constructor
    -- to effect operands.  If the operand list is empty, the variable or
    -- constructor may be either polymorphic (with zero parameters) or
    -- monomorphic.
  | InstT 
    { etypeVarCon :: !(Either Var Con) 
    , etypeEffects :: [Effect]
    }
    
    -- | A function type
  | FunT 
    { etypeParam :: EParamType 
    , etypeEffect :: Effect 
    , etypeReturn :: EReturnType
    }

    -- | An effect-monomorphic type variable
  | VarT 
    { etypeVar :: !Var
    }
    
    -- | An effect-monomorphic type constructor
  | ConT 
    { etypeCon :: !Con
    }
  
    -- | A literal or kind
  | LitT 
    { etypeLit :: !Gluon.Lit
    }

-- | Construct a type from a variable.
-- Inhabitants of variable types are always passed by reference.
varT v
  | getLevel v /= TypeLevel = internalError "varT: Not a type variable" 
  | otherwise = ERepType Referenced (VarT v)

-- | Construct a type from a constructor.
conT c = ERepType (conRepr c) (ConT c)

-- | Construct a type from a literal.
litT l = ERepType repr (LitT l)
  where
    repr = case l
           of Gluon.KindL {} -> Value
              _ -> internalError "litT: Unexpected literal"

appT :: ERepType -> [ERepType] -> ERepType
appT op [] = op
appT op args = ERepType (getTypeRepr op) $
               AppT (discardTypeRepr op) (map discardTypeRepr args)

instT (Left v) [] = varT v
instT (Right c) [] = conT c
instT op args = ERepType repr $ InstT op args
  where
    repr = case op
           of Left _  -> Referenced
              Right c -> conRepr c

funT param eff ret = 
  let repr = case getLevel ret
             of TypeLevel -> Boxed
                KindLevel -> Value
  in ERepType repr (FunT param eff ret)

conRepr :: Con -> Representation
conRepr = dataTypePassConv

instance HasLevel EType where
  getLevel (AppT {etypeOper = op}) = getLevel op
  getLevel (InstT {etypeVarCon = Left v}) = getLevel v
  getLevel (InstT {etypeVarCon = Right c}) = getLevel c
  getLevel (FunT {etypeReturn = rt}) = getLevel $ returnTypeType rt
  getLevel (VarT {etypeVar = v}) = getLevel v
  getLevel (ConT {etypeCon = c}) = getLevel c
  getLevel (LitT {etypeLit = l}) = Gluon.litLevel l

-- | Get the parameter-passing convention of a value whose type is a
-- fully applied instance of the given data type constructor.  For example,
-- when called with the \'list\' type constructor, the parameter-passing
-- convention for lists is returned.
dataTypePassConv :: Con -> Representation
dataTypePassConv c =
  case lookupDataTypeTable c
  of (pc, _, _, _) -> pc

conEffectParamVariance c =
  case lookupDataTypeTable c
  of (_, _, variance, _) -> variance

conOrdinaryParamVariance c =
  case lookupDataTypeTable c
  of (_, _, _, variance) -> variance

lookupDataTypeTable c
  | getLevel c /= TypeLevel = internalError "lookupDataTypeTable: Not a type"
  | c `SF.isPyonBuiltin` SF.the_Stream =
      -- All 'Stream' instances should have been converted to 'LazyStream'
      internalError "lookupDataTypeTable: Unexpected 'Stream' type"
  | otherwise =
      case IntMap.lookup (fromIdent $ Gluon.conID c) dataTypeTable
      of Just x -> x
         Nothing -> internalError $ "lookupDataTypeTable: No information " ++
                    "for constructor " ++ showLabel (Gluon.conName c)
    
-- | A table of information about data types, indexed by the type constructor.
dataTypeTable =
  IntMap.fromList [(fromIdent $ Gluon.conID c,
                    (pc, length eff_variance, eff_variance, param_variance)) 
                  | (c, pc, eff_variance, param_variance) <- assocs]
  where
    -- Fields of table:
    --  1. Type constructor
    --  2. Representation
    --  3. Variances of effect parameters
    --  4. Variances of type parameters
    assocs =
      [ (SF.pyonBuiltin SF.the_PassConv, Referenced, [], [Invariant])
      , (SF.pyonBuiltin SF.the_AdditiveDict, Referenced, [], [Invariant])
      , (SF.pyonBuiltin SF.the_TraversableDict, Referenced, [], [Invariant])
      , (SF.pyonBuiltin SF.the_int, Value, [], [])
      , (SF.pyonBuiltin SF.the_float, Value, [], [])
      , (SF.pyonBuiltin SF.the_bool, Value, [], [])
      , (SF.pyonBuiltin SF.the_NoneType, Value, [], [])
      , (SF.pyonBuiltin SF.the_Any, Value, [], [])
      , (SF.pyonBuiltin SF.the_list, Referenced, [], [Invariant])
      , (SF.pyonBuiltin SF.the_LazyStream, Boxed, [Covariant], [Covariant])
      ]

-- | Get the number of effect arguments a type constructor takes.
dataTypeEffectArity :: Con -> Int
dataTypeEffectArity c =
  case lookupDataTypeTable c
  of (_, arity, _, _) -> arity

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

-- | A table of information about functions and data constructors.
dataConTable =
  IntMap.fromList [(fromIdent $ Gluon.conID c, arity)
                  | (c, arity) <- assocs]
  where  
    assocs =
      []

-- | Get a type's variance with respect to each of its effect parameters.
etypeEffectParamVariance ty =
  case ty
  of ConT c -> conEffectParamVariance c
     VarT _ -> repeat Invariant
     _ -> internalError "etypeEffectParamVariance"

etypeOrdinaryParamVariance ty =
  case ty
  of ConT c -> conOrdinaryParamVariance c
     InstT (Right c) _ -> conOrdinaryParamVariance c
     _ -> repeat Invariant

-- | Get the standard representation to use for a type.  The representation
-- is chosen based on the type's head term.  The type must have kind @*@
-- (this condition is not checked).
etypeStandardRepr :: EType -> Representation
etypeStandardRepr ty = head_repr ty
  where
    -- Inspect the head to choose the parameter-passing convention
    head_repr ty =
      case ty
      of AppT op _ -> head_repr op
         InstT (Left v) _ -> Referenced
         InstT (Right c) _ -> conRepr c
         FunT _ _ _
           | getLevel ty == TypeLevel -> Boxed -- Functions are passed 'owned'
           | getLevel ty == KindLevel -> Value -- Types are passed by value
           | otherwise -> internalError "etypeStandardRepr"
         VarT _ -> Referenced
         ConT c -> conRepr c
         LitT (Gluon.KindL _) -> Value -- Types are passed by value
         LitT _ -> internalError "etypeStandardRepr: Unexpected literal"

etypeWithStandardRepr :: EType -> ERepType
etypeWithStandardRepr t = ERepType (etypeStandardRepr t) t

-- | Convert an effect type to a parameter type.  If a parameter variable is
-- given, then the parameter will be used dependently.  An error will be raised
-- if a variable is given and the type is not passed by value.
etypeToParamType :: ERepType -> Maybe Var -> RegionM EParamType
etypeToParamType (ERepType repr ty) param_var =
  case repr
  of Value -> return $ ValPT param_var ty
     Boxed
       | isNothing param_var -> return $ OwnPT ty
       | otherwise -> no_dependent_type
     Referenced 
       | isNothing param_var -> do
           rgn <- newRegionVar False
           return $ ReadPT rgn ty
       | otherwise -> no_dependent_type
  where
    no_dependent_type =
      internalError "etypeToParamType: Parameter cannot be used dependently"

-- | Convert an effect type to a return type for an expression that computes
-- a new result.
etypeToReturnType :: ERepType -> RegionM EReturnType
etypeToReturnType (ERepType repr ty) =
  case repr
  of Value      -> return $ ValRT ty
     Boxed      -> return $ OwnRT ty
     Referenced -> do
       -- This region may get its actual value by unification 
       rgn <- newRegionVar True
       return $ WriteRT rgn ty

-------------------------------------------------------------------------------
-- Pretty-printing

pprRepr :: Representation -> Doc
pprRepr Value = text "val"
pprRepr Boxed = text "box"
pprRepr Referenced = text "ref"

pprERepType :: ERepType -> Doc
pprERepType (ERepType repr ty) = pprRepr repr <+> pprEType ty

pprEType :: EType -> Doc
pprEType ty =
  case ty
  of AppT op args -> parens $ sep $ pprEType op : map pprEType args
     InstT varcon eff ->
       let varcon_doc = case varcon
                        of Left v  -> Gluon.pprVar v
                           Right c -> text (showLabel $ Gluon.conName c)
       in sep (varcon_doc : map pprEffect eff)
     FunT _ _ _ ->
       let (first_param_doc, rest) = pprArrowType ty
       in parens $ sep (first_param_doc : rest)
     VarT v -> Gluon.pprVar v
     ConT c -> text (showLabel $ Gluon.conName c)
     LitT l -> Gluon.pprExp (Gluon.mkLitE noSourcePos l)

pprArrowType :: EType -> (Doc, [Doc])
pprArrowType ty =
  case ty
  of FunT param eff rt ->
       let param_doc = pprEParamType param
           eff_doc = if isEmptyEffect eff
                     then empty
                     else parens $ pprEffect eff
           (rt_doc_1, rt_doc) = pprArrowReturnType rt
       in (param_doc, nest (-3) (text "->" <+> eff_doc <+> rt_doc_1) : rt_doc)
     _ -> (pprEType ty, [])

pprArrowReturnType :: EReturnType -> (Doc, [Doc])
pprArrowReturnType (OwnRT fun_type@(FunT {})) = pprArrowType fun_type
pprArrowReturnType ty = (pprEReturnType ty, [])

pprEParamType param_type = 
  let ty_doc = pprEType $ paramTypeType param_type
      conv_doc = text $ case param_type
                        of ValPT {} -> "val"
                           OwnPT {} -> "own"
                           ReadPT {} -> "read"
      rgn_doc = case param_type
                of ReadPT v _ -> pprEffectVar v
  in case param_type
     of ValPT (Just v) _ ->
          parens $ conv_doc <+> Gluon.pprVar v <+> text ":" <+> ty_doc
        ValPT Nothing _ -> conv_doc <+> ty_doc
        OwnPT _ -> conv_doc <+> ty_doc
        ReadPT v _ -> conv_doc <+> ty_doc <+> text "@" <+> rgn_doc

pprEReturnType return_type =
  let ty_doc = pprEType $ returnTypeType return_type
      conv_doc = text $ case return_type
                        of ValRT {} -> "val"
                           OwnRT {} -> "own"
                           ReadRT {} -> "read"
                           WriteRT {} -> "write"
      rgn_doc = case return_type
                of ReadRT v _ -> pprEffectVar v
                   WriteRT v _ -> pprEffectVar v
  in case return_type
     of ReadRT {} -> conv_doc <+> ty_doc <+> text "@" <+> rgn_doc
        WriteRT {} -> conv_doc <+> ty_doc <+> text "@" <+> rgn_doc
        _ -> conv_doc <+> ty_doc
  

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

  -- | Rename a type variable.  Renaming does not change the variable's
  -- representation.
  renameT :: Var -> Var -> e -> e

  -- | Rename an effect variable.  The old and new variables must not have
  -- been assigned values.  The argument should be expanded before renaming.
  --
  -- Note that the caller of 'renameE' should expand its expression argument.  
  -- When renameE calls itself recursively, it's not necessary to expand the
  -- argument again.
  renameE :: EffectVar -> EffectVar -> e -> e
  
  -- | Assign a type variable.  Assignment does not alter the variable's
  -- representation.
  assignT :: Var -> EType -> e -> e
  
  -- | Assign an effect variable
  assignE :: EffectVar -> Effect -> e -> e
  
  -- | True if the value mentions the given effect variable;
  -- variable assignments are expanded first
  mentionsE :: e -> EffectVar -> IO Bool
  
  -- | True if the value mentions any of the given effect variables;
  -- variable assignments are expanded first
  mentionsAnyE :: e -> Set.Set EffectVar -> IO Bool
  
  mentionsT :: e -> Var -> Bool

evalAndRenameE :: Parametric exp => EffectVar -> EffectVar -> exp -> IO exp
evalAndRenameE old_v new_v e = liftM (renameE old_v new_v) $ evaluate e

mapParametricEType :: (forall a. Parametric a => a -> a) -> EType -> EType
mapParametricEType f expression =
  case expression
  of AppT ty args   -> AppT (f ty) (map f args)
     InstT op args  -> InstT op (map f args)
     FunT pt eff rt -> FunT (f pt) (f eff) (f rt)
     VarT {}        -> expression
     ConT {}        -> expression
     LitT {}        -> expression

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
  mentionsT () _ = False

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
  (x, y) `mentionsT` v = x `mentionsT` v || y `mentionsT` v

instance Parametric ERepType where
  freeEffectVars t = freeEffectVars (discardTypeRepr t)
  evaluate (ERepType r t) = fmap (ERepType r) $ evaluate t
  renameT old_v new_v (ERepType r t) = ERepType r (renameT old_v new_v t)
  renameE old_v new_v (ERepType r t) = ERepType r (renameE old_v new_v t)
  assignT old_v new_e (ERepType r t) = ERepType r (assignT old_v new_e t)
  assignE old_v new_e (ERepType r t) = ERepType r (assignE old_v new_e t)
  ERepType _ t `mentionsE` v = t `mentionsE` v
  ERepType _ t `mentionsAnyE` vs = t `mentionsAnyE` vs
  ERepType _ t `mentionsT` v = t `mentionsT` v

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

       VarT {} -> return emptyFV
       ConT {} -> return emptyFV
       LitT {} -> return emptyFV

  evaluate expression = 
    case expression
    of AppT op args ->
         AppT `liftM` evaluate op `ap` mapM evaluate args
       InstT op args ->
         InstT op `liftM` mapM evaluate args
       FunT pt eff rt ->
         FunT `liftM` evaluate pt `ap` evaluate eff `ap` evaluate rt
       VarT {} -> return expression
       ConT {} -> return expression
       LitT {} -> return expression

  renameT old_v new_v expression =
    case expression
    of VarT v | v == old_v -> VarT new_v
       InstT (Left v) args | v == old_v -> InstT (Left new_v) args
       _ -> mapParametricEType (renameT old_v new_v) expression

  assignT old_v val expression =
    case expression
    of VarT v | v == old_v -> val
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
       VarT {}        -> return False
       ConT {}        -> return False
       LitT {}        -> return False

  expression `mentionsAnyE` vs =
    case expression
    of AppT op args ->
         op `mentionsAnyE` vs >||> anyM (`mentionsAnyE` vs) args
       InstT _ args   -> anyM (`mentionsAnyE` vs) args
       FunT pt eff rt -> pt `mentionsAnyE` vs >||>
                         eff `mentionsAnyE` vs >||>
                         rt `mentionsAnyE` vs
       VarT {}        -> return False
       ConT {}        -> return False
       LitT {}        -> return False
  
  expression `mentionsT` v =
    case expression
    of AppT op args   -> op `mentionsT` v || any (`mentionsT` v) args
       InstT _ args   -> any (`mentionsT` v) args
       FunT pt eff rt -> pt `mentionsT` v ||
                         eff `mentionsT` v ||
                         rt `mentionsT` v
       VarT v'        -> v == v'
       ConT {}        -> False
       LitT {}        -> False

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

  expr `mentionsT` v =
    case expr
    of ValPT _ t  -> t `mentionsT` v
       OwnPT t    -> t `mentionsT` v
       ReadPT _ t -> t `mentionsT` v

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

  expr `mentionsT` v =
    case expr
    of ValRT t -> t `mentionsT` v
       OwnRT t -> t `mentionsT` v
       ReadRT _ t -> t `mentionsT` v
       WriteRT _ t -> t `mentionsT` v

instance Parametric Effect where
  freeEffectVars eff = do
    vars <- effectMembers eff
    return $ FreeEffectVars (Set.fromList $ filter isEVar vars) Set.empty
  
  evaluate = evalEffect
  
  -- There aren't any types inside effects
  renameT _ _ e = e
  assignT _ _ e = e
  
  renameE = renameInEffect
  assignE = assignInEffect
  
  eff `mentionsE` v = liftM (`effectMentions` v) $ evaluate eff
  eff `mentionsAnyE` vs = do eff' <- evaluate eff
                             return $ any (eff' `effectMentions`) (Set.toList vs)

  eff `mentionsT` v = False

-- | A renaming on parametric types.
data Renaming =
  Renaming {applyRenaming :: forall a. Parametric a => a -> a}

idRenaming :: Renaming
idRenaming = Renaming id

evalAndApplyRenaming :: Parametric a => Renaming -> a -> IO a
evalAndApplyRenaming rn x = fmap (applyRenaming rn) (evaluate x)

-- | Freshen the type parameter variable in a 'ParamType'.
-- Returns a new expression and a renaming.
freshenParamTypeTypeParam :: EParamType -> RegionM (EParamType, Renaming)
freshenParamTypeTypeParam (ValPT (Just v) t) = do
  v' <- Gluon.newVar (Gluon.varName v) (getLevel v)
  return (ValPT (Just v') t, Renaming (renameT v v'))

freshenParamTypeTypeParam pt = return (pt, idRenaming)

-------------------------------------------------------------------------------
-- Conversion from System F to effect types

-- | True for dictionary type constructors
isDictionaryTypeCon c =
  c `elem` [ SF.pyonBuiltin SF.the_PassConv
           , SF.pyonBuiltin SF.the_AdditiveDict
           ]

-- | Instantiate a type constructor by inserting new type parameters.  The
--   parameters will acquire values by unification.
--
--   The newly created, unifiable effect variables are returned in a list.
instantiateTypeCon :: Bool -> Con -> RegionM (ERepType, [EVar])
instantiateTypeCon no_effects c
  | no_effects = return (mkPureInstT (Right c) arity, [])
  | otherwise  = mkInstT (Right c) arity
  where
    arity = dataTypeEffectArity c

-- | Create an instance expression where all effect parameters are empty.
mkPureInstT :: Either Var Con -> Int -> ERepType
mkPureInstT op arity = instT op (replicate arity emptyEffect)

-- | Create an instance expression from a variable or constructor.
mkInstT :: Either Var Con       -- ^ Variable or constructor to instantiate
        -> Int                  -- ^ Arity (number of effect parameters)
        -> RegionM (ERepType, [EVar])
mkInstT op arity = do
  args <- replicateM arity newEffectVar
  return (instT op $ map varEffect args, args)


-- | Convert a System F type to the corresponding effect type.  New effect
-- variables are created to stand for each side effect.  Function types are
-- conservatively assumed to access all their parameters.
toEffectType :: Gluon.WSRExp -> RegionM (ERepType, [EVar])
toEffectType = makeEffectType False

-- | Convert a System F type to the corresponding effect type, with all side
--   effect parameters set to the empty effect.  This conversion is used in
--   type parameters of type classes.
toPureEffectType :: Gluon.WSRExp -> RegionM ERepType
toPureEffectType t = fmap fst $ makeEffectType True t

-- | This function does the real work of 'toEffectType' and
-- 'toPureEffectType'.
makeEffectType :: Bool -> Gluon.WSRExp -> RegionM (ERepType, [EVar])
makeEffectType no_effects expr =
  case getLevel $ Gluon.fromWhnf $ Gluon.substFullyUnderWhnf expr
  of KindLevel -> do k <- makeEffectKind expr
                     return (k, [])
     TypeLevel ->
       case Gluon.unpackRenamedWhnfAppE expr
       of Just (con, args) -> makeConstructorApplication no_effects con args
          Nothing ->
            case Gluon.fromWhnf expr
            of Gluon.FunE {} -> makeFunctionType no_effects expr
               Gluon.AppE {Gluon.expOper = op, Gluon.expArgs = args} -> do 
                 (op', op_evars) <- makeEffectType no_effects =<< evalHead op
                 (unzip -> (args', concat -> args_evars)) <-
                   mapM (makeEffectType no_effects <=< evalHead) args
                 return (appT op' args', op_evars ++ args_evars)
               Gluon.VarE {Gluon.expVar = v} -> return (varT v, [])
               Gluon.LitE {Gluon.expLit = l} -> return (litT l, [])
               _ -> internalError "makeEffectType"
     _ -> internalError "makeEffectType"

-- | Convert a kind expression to the representation used in effect types.
-- Kind expressions only contain literals and non-dependnet function types.
-- No effect types are inserted here.
makeEffectKind :: Gluon.WSRExp -> RegionM ERepType
makeEffectKind expr =
  case Gluon.fromWhnf expr
  of Gluon.LitE {Gluon.expLit = lit} -> return $ litT lit
     Gluon.FunE { Gluon.expMParam = Binder' Nothing dom ()
                , Gluon.expRange = rng} -> do
       dom' <- makeEffectKind =<< evalHead dom
       param <- etypeToParamType dom' Nothing
       rng' <- etypeToReturnType =<< makeEffectKind =<< evalHead rng
       return $ funT param emptyEffect rng'
     _ -> internalError "makeEffectKind"

-- | Create an application of a type constructor.  System F types are
-- translated to core types here.
makeConstructorApplication no_effects sf_con args = do
  (con_inst, con_evars) <- instantiateTypeCon no_local_effects core_con
  (unzip -> (args', concat -> arg_evars)) <-
    mapM (makeEffectType no_local_effects <=< evalHead) args
  return (appT con_inst args', con_evars ++ arg_evars)
  where
    -- Don't let side effects appear in parameters to dictionary types 
    no_local_effects = no_effects || isDictionaryTypeCon sf_con
    
    core_con
      | sf_con `SF.isPyonBuiltin` SF.the_Stream = SF.pyonBuiltin SF.the_LazyStream
      | otherwise = sf_con

-- | Create a function type from the expression.  In the type, assume that 
-- all parameters are read.  Side effects from parameters will be placed on 
-- the last arrow.  In other words, the function only produces side effects
-- after all parameters are applied.
makeFunctionType :: Bool -> Gluon.WSRExp -> RegionM (ERepType, [EVar])
makeFunctionType no_effects expr =
  case Gluon.fromWhnf expr
  of Gluon.FunE {Gluon.expMParam = param, Gluon.expRange = rng} -> do
       -- Convert the domain type
       (param, param_effects, dom_evars) <- make_domain_type emptyEffect param

       -- Continue with the range
       (rng', here_effect, rng_evars) <-
         make_range_type param_effects =<< evalHead rng
       return_type <- etypeToReturnType rng'

       let fun_type = ERepType representation $
                      FunT param here_effect return_type
       return (fun_type, dom_evars ++ rng_evars)

     _ -> internalError "makeFunctionType: Not a function type"
  where
    -- The function's representation.  If it's a function type, the
    -- representation is 'Boxed'.  If it's a function kind, the representation
    -- is 'Value'.
    representation =
      case getLevel $ Gluon.fromWhnf expr
      of TypeLevel -> Boxed
         KindLevel -> Value
    
    -- Convert everything on the right hand side of an (->)
    make_range_type param_effects expr =
      case Gluon.fromWhnf expr
      of Gluon.FunE {Gluon.expMParam = param, Gluon.expRange = rng} -> do
           -- Convert the next parameter
           (param, param_effects', dom_evars) <-
             make_domain_type param_effects param

           -- Continue with the range
           (rng', here_effect, rng_evars) <-
             make_range_type param_effects' =<< evalHead rng
           return_type <- etypeToReturnType rng'

           let fun_type = ERepType representation $
                          FunT param here_effect return_type
           return (fun_type, emptyEffect, dom_evars ++ rng_evars)
         
         _ | getLevel (Gluon.fromWhnf expr) /= TypeLevel ->
               internalError "funTypeToPassType: Expecting a type"
           | otherwise -> do
               -- The function produces a side effect and returns its result
               (rng', rng_evars) <- makeEffectType no_effects expr

               -- If side effect variables are allowed here,
               -- create a variable to stand for this expression's free effect
               (param_effects', extra_evar) <-
                 if no_effects
                 then return (emptyEffect, [])
                 else do
                   effect_var <- newEffectVar
                   return (param_effects `effectUnion` varEffect effect_var,
                           [effect_var])

               return (rng', param_effects', extra_evar ++ rng_evars)

    -- Convert the parameter on the left side of an (->)
    make_domain_type param_effects (Binder' mv dom ()) = do
      (dom', dom_evars) <- makeEffectType no_effects =<< evalHead dom
      param <- etypeToParamType dom' mv
           
      -- Include this parameter in the function's side effect
      let param_effects' =
            param_effects `effectUnion` maybeVarEffect (paramTypeRegion param)
      return (param, param_effects', dom_evars)

-------------------------------------------------------------------------------
-- Conversion from core to effect types

-- | A mapping from a core variable to a unifiable region or effect variable
type CoreEnv = Map.Map Var EffectVar

-- | During translation from Core type to effect inference type, new unifiable
-- region and effect variables are created for each type.
type CoreTrans a = ReaderT CoreEnv RegionM a

-- Translated variables are unifiable.  To avoid unexpected
-- unification-related side effects, a translated type should either be
-- used immediately at a monomorphic type, or turned into a type scheme that's
-- instantiated each time its used.
withCoreRegionVar :: Var -> (RVar -> CoreTrans a) -> CoreTrans a
withCoreRegionVar v k = do
  v' <- lift (newRegionVar True)
  local (Map.insert v v') (k v')

withCoreEffectVar :: Var -> (EVar -> CoreTrans a) -> CoreTrans a
withCoreEffectVar v k = do
  v' <- lift newEffectVar
  local (Map.insert v v') (k v')

lookupCoreVar :: Var -> CoreTrans EffectVar
lookupCoreVar v = asks $ \env ->
  case Map.lookup v env
  of Just v' -> v'
     Nothing -> internalError "lookupCoreVar"

isCoreEffectVar :: Var -> CoreTrans Bool
isCoreEffectVar v = asks $ \env ->
  case Map.lookup v env
  of Just v' | isEVar v' -> True
     _ -> False

-- | Convert a Core type to the corresponding effect inference type.
-- This is used to get the effect types of predefined functions and
-- data types.
--
-- The returned type represents a polymorphic effect type.  If there are
-- effect parameters, they are converted to fresh effect variables
-- that are returned as a list.
--
-- FIXME: Don't know how to determine whether a core type is an effect 
-- or something else.
coreToEffectType :: Core.RCType -> RegionM ([EVar], ERepType)
coreToEffectType ty = runReaderT (cTypeToPolyEffectType ty) Map.empty

-- | Convert a core type to a polymorphic effect type.

-- Extract all effect parameters, then pass the remaining expression
-- to 'cTypeToEffectType'.
cTypeToPolyEffectType :: Core.RCType -> CoreTrans ([EVar], ERepType)
cTypeToPolyEffectType ty = 
  case ty
  of Core.FunCT ft -> from_poly_type ft
     _ -> do t <- cTypeToEffectType ty
             return ([], t)
  where
    from_poly_type ft@(Core.ArrCT (Core.ValPT mv Core.::: param_ty) eff rng) 
      | is_effect_type param_ty =
          maybe (lift newEffectVar >>=) withCoreEffectVar mv $ \evar -> do
            (qvars, ty) <- cTypeToPolyEffectType (Core.FunCT rng)
            return (evar : qvars, ty)
    
      | otherwise = do t <- cTypeToEffectType (Core.FunCT ft)
                       return ([], t)

    -- Functions must have a non-effect parameter
    from_poly_type (Core.RetCT _) = internalError "cTypeToPolyEffectType"

    is_effect_type (Core.ExpCT (Gluon.LitE {Gluon.expLit = Gluon.KindL Gluon.EffectKind})) = True
    is_effect_type _ = False

cTypeToEffectType :: Core.RCType -> CoreTrans ERepType
cTypeToEffectType ty =
  case ty
  of Core.ExpCT e -> gluonTypeToEffectType e
     Core.AppCT op args -> do
       cop <- cTypeToEffectType op
       (eff_args, other_args) <- cTypeArgumentsToEffectTypes args
       
       -- If there are effect arguments, create an instance expression
       let varcon = case discardTypeRepr cop
                    of VarT v -> Left v
                       ConT c -> Right c
                       _ -> internalError "cTypeToEffectType"
           inst_op =
             if null eff_args then cop else instT varcon eff_args

       return $ appT inst_op other_args
     Core.FunCT ft -> cFunTypeToEffectType ft
     
-- | Convert a list of Core type arguments to effect-annotated types.
-- A prefix of the arguments consists of effects; the rest are types.
cTypeArgumentsToEffectTypes :: [Core.RCType]
                            -> CoreTrans ([Effect], [ERepType])
cTypeArgumentsToEffectTypes types = cvt_eff id types
  where
    -- Convert effect types, then convert other types
    cvt_eff hd (t:ts) = do is_eff <- isCoreEffectType t 
                           if is_eff
                             then do eff <- cTypeToEffect t
                                     cvt_eff (hd . (eff:)) ts
                             else do types <- mapM cTypeToEffectType (t:ts)
                                     return (hd [], types)
    cvt_eff hd []     = return (hd [], [])

-- | Decide whether a core expression is an effect type.  This function only
-- works for the subset of core expressions that can be translated to effect
-- inference.
--
-- Effect-typed core arguments are inspected by inspecting their head.  The
-- constructors @SconjE@, @EmpE@, and @AtE@ indicate that it's effect typed.
-- Also, effect variables indicate that it's effect typed.
isCoreEffectType :: Core.RCType -> CoreTrans Bool
isCoreEffectType ty =
  case ty
  of Core.ExpCT e ->
       case e
       of Gluon.VarE {Gluon.expVar = v} -> isCoreEffectVar v
          Gluon.ConE {Gluon.expCon = c} -> return $ check_con c
          Gluon.AppE {Gluon.expOper = Gluon.ConE {Gluon.expCon = c}} ->
            return $ check_con c
          _ -> return False
     Core.AppCT op _ ->
       case op
       of Core.ExpCT (Gluon.ConE {Gluon.expCon = c}) -> return $ check_con c
          _ -> return False
     Core.FunCT {} -> return False
  where
    check_con c = c `elem` [ Gluon.builtin Gluon.the_EmpE
                           , Gluon.builtin Gluon.the_SconjE
                           , Gluon.builtin Gluon.the_AtE
                           ]

-- | Convert a Core function type to an effect-annotated type.

-- The conversion process is recursive on the function range.  Initially, the
-- entire type is treated like a function range, then it is converted from a
-- return type to a regular type.
cFunTypeToEffectType :: Core.RCFunType -> CoreTrans ERepType
cFunTypeToEffectType ft = do
  rt <- to_return_type ft
  case rt of OwnRT t -> return (etypeWithStandardRepr t)
             _ -> internalError "cFunTypeToEffectType"
  where
    to_return_type (Core.ArrCT param_binder eff rng) =
      assume_parameter param_binder $ \param' -> do
        eff' <- cTypeToEffect eff
        rng' <- to_return_type rng
        lift $ etypeToReturnType $ funT param' eff' rng'

    to_return_type (Core.RetCT (binder Core.::: rng)) = do
      rng' <- cTypeToEffectType rng
      case binder of 
        Core.ValRT -> return $ ValRT $ discardTypeRepr rng'
        Core.OwnRT -> return $ OwnRT $ discardTypeRepr rng'
        
        -- Only support reading from a variable address.  Addresses derived
        -- by pointer manipulation cannot be expressed.
        Core.ReadRT (Gluon.VarE {Gluon.expVar = v}) -> do
          rgn <- lookupCoreVar v
          return $ ReadRT rgn $ discardTypeRepr rng'
        Core.ReadRT _ -> internalError "cFunTypeToEffectType"

        Core.WriteRT -> do rgn <- lift (newRegionVar False)
                           return $ WriteRT rgn $ discardTypeRepr rng'

    assume_parameter (param Core.::: dom) k = do
      dom' <- cTypeToEffectType dom
      let dom_t = discardTypeRepr dom'
      case param of
        Core.ValPT mv -> k $ ValPT mv dom_t
        Core.OwnPT    -> k $ OwnPT dom_t
        Core.ReadPT v -> withCoreRegionVar v $ \v' -> k $ ReadPT v' dom_t

-- | Convert a Gluon type to an effect type.
-- The type may only consist of variables, constructors, and applications.
--
-- /FIXME/: Convert effect types using cTypeToEffect.  Use Core type inference
-- to identify effect types.
gluonTypeToEffectType :: Gluon.RExp -> CoreTrans ERepType
gluonTypeToEffectType expr =
  case expr
  of Gluon.VarE {Gluon.expVar = v} -> return $ varT v
     Gluon.ConE {Gluon.expCon = c} -> return $ conT c
     Gluon.LitE {Gluon.expLit = l} -> return $ litT l
     Gluon.AppE {Gluon.expOper = op, Gluon.expArgs = args} -> do
       op' <- gluonTypeToEffectType op
       args' <- mapM gluonTypeToEffectType args
       return $ appT op' args'
     _ -> internalError "gluonTypeToEffectType: Unexpected type"

-- | Convert a core type to the corresponding effect.
-- The type must consist of only the empty type @EmpE@, conjunctions
-- @SconjE@, effect variables, and atomic @AtE@ effects where the address 
-- is a region.
cTypeToEffect :: Core.RCType -> CoreTrans Effect
cTypeToEffect expr =
  case Core.unpackConAppCT expr
  of Just (c, args)
       | c `Gluon.isBuiltin` Gluon.the_EmpE -> return emptyEffect

       | c `Gluon.isBuiltin` Gluon.the_SconjE ->
           case args
           of [arg1, arg2] -> do eff1 <- cTypeToEffect arg1
                                 eff2 <- cTypeToEffect arg2
                                 return $ effectUnion eff1 eff2
              _ -> internalError "cTypeToEffect"

       | c `Gluon.isBuiltin` Gluon.the_AtE ->
           case args
           of [ty, Core.ExpCT (Gluon.VarE {Gluon.expVar = rgn})] -> do
                liftM varEffect $ lookupCoreVar rgn
              _ -> internalError "cTypeToEffect"

     Nothing ->
       case expr
       of Core.ExpCT (Gluon.VarE {Gluon.expVar = evar}) ->
            liftM varEffect $ lookupCoreVar evar

          _ -> internalError "cTypeToEffect: Unexpected effect expression"

