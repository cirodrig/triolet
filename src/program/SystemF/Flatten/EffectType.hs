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
        unpackFunctionType,
        
        -- * Renaming
        Renaming(..),
        idRenaming,
        evalAndApplyRenaming,
        Parametric(..),
        FreeEffectVars(..),
        
        -- * Converting to effect types
        toEffectType,
        toRestrictedEffectType,
        toPureEffectType,
        etypeToParamType,
        etypeToReturnType,
        coreToEffectType,
        
        -- * Pretty-printing
        pprEType, pprERepType, pprEReturnType, pprEParamType
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

    -- | Return a borrowed reference to data that already exists.
    --   Variable references are the only thing that uses this convention.
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
conAppT c args =
  let con_type = ERepType (conRepr c (map discardTypeRepr args)) (ConT c)
  in appT con_type args

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

instT (Left v) [] ty_args = appT (varT v) ty_args
instT (Right c) [] ty_args = conAppT c ty_args
instT op eff_args ty_args = appT (ERepType repr $ InstT op eff_args) ty_args
  where
    repr = case op
           of Left _  -> Referenced
              Right c -> conRepr c (map discardTypeRepr ty_args)

funT param eff ret = 
  let repr = case getLevel ret
             of TypeLevel -> Boxed
                KindLevel -> Value
  in ERepType repr (FunT param eff ret)

conRepr :: Con -> [EType] -> Representation
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
dataTypePassConv :: Con -> [EType] -> Representation
dataTypePassConv c ty_args =
  case lookupDataTypeTable c
  of (pc, _, _, _) -> pc ty_args

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
    --  2. Representation, as a function of the type parameters
    --  3. Variances of effect parameters
    --  4. Variances of type parameters
    assocs =
      [ (SF.pyonBuiltin SF.the_PassConv, ref, [], [Invariant])
      , (SF.pyonBuiltin SF.the_EqDict, ref, [], [Invariant])
      , (SF.pyonBuiltin SF.the_OrdDict, ref, [], [Invariant])
      , (SF.pyonBuiltin SF.the_AdditiveDict, ref, [], [Invariant])
      , (SF.pyonBuiltin SF.the_MultiplicativeDict, ref, [], [Invariant])
      , (SF.pyonBuiltin SF.the_TraversableDict, ref, [], [Invariant])
      , (SF.pyonBuiltin SF.the_int, val, [], [])
      , (SF.pyonBuiltin SF.the_float, val, [], [])
      , (SF.pyonBuiltin SF.the_complex, complex_repr, [], [Invariant])        
      , (SF.pyonBuiltin SF.the_bool, val, [], [])
      , (SF.pyonBuiltin SF.the_NoneType, val, [], [])
      , (SF.pyonBuiltin SF.the_Any, val, [], [])
      , (SF.pyonBuiltin SF.the_list, ref, [], [Invariant])
      , (SF.pyonBuiltin SF.the_LazyStream, box, [Covariant], [Covariant])
      , (SF.getPyonTupleType' 2, ref, [], [Invariant, Invariant])
      ]
   
    ref = const Referenced
    val = const Value
    box = const Boxed
    
    -- Complex float is passed by value.  Otherwise, by reference.
    complex_repr [arg] =
      case arg
      of ConT {etypeCon = c}
           | c `SF.isPyonBuiltin` SF.the_float -> Value
           | otherwise -> Referenced

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
-- is usually chosen based on some the type's head.  In some cases, the
-- head and some arguments are used to choose the representation.
-- The type must have kind @*@ (this condition is not checked).
etypeStandardRepr :: EType -> Representation
etypeStandardRepr ty = head_repr ty []
  where
    -- Inspect the head to choose the parameter-passing convention
    head_repr ty ty_args =
      case ty
      of AppT op args -> head_repr op (args ++ ty_args)
         InstT (Left v) _ -> Referenced
         InstT (Right c) _ -> conRepr c ty_args
         FunT _ _ _
           | getLevel ty == TypeLevel -> Boxed -- Functions are passed 'owned'
           | getLevel ty == KindLevel -> Value -- Types are passed by value
           | otherwise -> internalError "etypeStandardRepr"
         VarT _ -> Referenced
         ConT c -> conRepr c ty_args
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

mapParametricTriple :: (Parametric a, Parametric b, Parametric c) =>
                       (forall d. Parametric d => d -> d)
                    -> (a, b, c) -> (a, b, c)
mapParametricTriple f (x, y, z) = (f x, f y, f z)

instance (Parametric a, Parametric b, Parametric c) =>
         Parametric (a, b, c) where
  freeEffectVars (x, y, z) = do
    xfv <- freeEffectVars x
    yfv <- freeEffectVars y
    zfv <- freeEffectVars z
    return (xfv `unionFV` yfv `unionFV` zfv)
  evaluate (x, y, z) = liftM3 (,,) (evaluate x) (evaluate y) (evaluate z)
  renameT old_v new_v = mapParametricTriple (renameT old_v new_v)
  renameE old_v new_v = mapParametricTriple (renameE old_v new_v)
  assignT old_v new_e = mapParametricTriple (assignT old_v new_e)
  assignE old_v new_e = mapParametricTriple (assignE old_v new_e)
  (x, y, z) `mentionsE` v = x `mentionsE` v >||>
                            y `mentionsE` v >||>
                            z `mentionsE` v
  (x, y, z) `mentionsAnyE` vs = x `mentionsAnyE` vs >||>
                                y `mentionsAnyE` vs >||>
                                z `mentionsAnyE` vs
  (x, y, z) `mentionsT` v = x `mentionsT` v ||
                            y `mentionsT` v ||
                            z `mentionsT` v

instance Parametric a => Parametric [a] where
  freeEffectVars xs = liftM unionsFV $ mapM freeEffectVars xs
  evaluate xs = mapM evaluate xs
  renameT old_v new_v xs = map (renameT old_v new_v) xs
  renameE old_v new_v xs = map (renameE old_v new_v) xs
  assignT old_v new_e xs = map (assignT old_v new_e) xs
  assignE old_v new_e xs = map (assignE old_v new_e) xs
  xs `mentionsE` v = anyM (`mentionsE` v) xs
  xs `mentionsAnyE` vs = anyM (`mentionsAnyE` vs) xs
  xs `mentionsT` v = any (`mentionsT` v) xs

-- | Not a complete instance.  Only variables that are not unified with an 
--   effect behave like a 'Parametric' instance. 
instance Parametric EffectVar where
  freeEffectVars v = do mb <- evalEffectVar v
                        return (FreeEffectVars (fromEffectSet mb) Set.empty)
  evaluate v = do mb <- evalEffectVar v
                  case fromEffect mb of
                    [v'] -> return v'
                    _ -> internalError "EffectVar.evaluate: Cannot evaluate"
  renameT _ _ v = v
  renameE old_v new_v v
    | v == old_v = new_v
    | otherwise  = v
  assignT _ _ v = v
  assignE old_v new_e v
    | v == old_v = internalError "EffectVar.assign: Cannot assign"
    | otherwise = v
  v `mentionsE` test_v = fmap (test_v ==) $ evaluate v
  v `mentionsAnyE` test_vs = fmap (`Set.member` test_vs) $ evaluate v
  v `mentionsT` _ = False

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
    of AppT op args -> do
         op_e <- freeEffectVars op
         args_e <- mapM freeEffectVars args
         return $ unionsFV (covariant op_e : map invariant args_e)

       InstT op args -> do
         -- Get free effect variables from parameters
         free_vars <- mapM freeEffectVars args

         -- Figure out the variance of each effect parameter
         let tovar Invariant = invariant
             tovar Covariant = covariant
             tovar Contravariant = contravariant
         let variances =
               case op
               of Left _  -> replicate (length args) invariant
                  Right c -> map tovar $ conEffectParamVariance c
         
         -- Apply variances and combine results
         return $ unionsFV $ zipWith ($) variances free_vars
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

-- | The degree to which effects are allowed in effect types.
data Effectfulness = NoEffects         -- ^ Functions have no effects
                   | RestrictedEffects -- ^ Functions read their parameters
                                       --   but have no other effects
                   | ArbitraryEffects  -- ^ Functions are permitted an
                                       --   arbitrary effect.  A flexible 
                                       --   effect variable is inserted when
                                       --   creating the function type.
                   deriving(Eq)
  
-- | True for dictionary type constructors
isDictionaryTypeCon c =
  c `elem` [ SF.pyonBuiltin SF.the_PassConv
           , SF.pyonBuiltin SF.the_AdditiveDict
           ]

-- | Instantiate a type constructor by inserting new type parameters.  The
--   parameters will acquire values by unification.
--
--   The newly created, unifiable effect variables are returned in a list.
instantiateTypeCon :: Effectfulness -> Con -> [ERepType]
                   -> RegionM (ERepType, [EVar])
instantiateTypeCon effectfulness c ty_args =
  case effectfulness
  of NoEffects         -> pure
     RestrictedEffects -> pure
     ArbitraryEffects  -> mkInstT (Right c) arity ty_args
  where
    pure = return (mkPureInstT (Right c) arity ty_args, [])
    arity = dataTypeEffectArity c

-- | Create an instance expression where all effect parameters are empty.
mkPureInstT :: Either Var Con -> Int -> [ERepType] -> ERepType
mkPureInstT op arity ty_args = instT op (replicate arity emptyEffect) ty_args

-- | Create an instance expression from a variable or constructor.
mkInstT :: Either Var Con       -- ^ Variable or constructor to instantiate
        -> Int                  -- ^ Arity (number of effect parameters)
        -> [ERepType]           -- ^ Type argumetns
        -> RegionM (ERepType, [EVar])
mkInstT op arity ty_args = do
  args <- replicateM arity newEffectVar
  return (instT op (map varEffect args) ty_args, args)


-- | Convert a System F type to the corresponding effect type.  New effect
-- variables are created to stand for each side effect.  Function types are
-- conservatively assumed to access all their parameters.
toEffectType :: Gluon.WSRExp -> RegionM (ERepType, [EVar])
toEffectType = makeEffectType ArbitraryEffects

-- | Convert a System F type to the corresponding effect type.  Function types
--   are conservatively assumed to access all their parameters, but have no
--   other side effects.
toRestrictedEffectType :: Gluon.WSRExp -> RegionM ERepType
toRestrictedEffectType t = fmap fst $ makeEffectType RestrictedEffects t

-- | Convert a System F type to the corresponding effect type, with no side
--   effects at all.  This conversion is used in type parameters of type 
--   classes.
toPureEffectType :: Gluon.WSRExp -> RegionM ERepType
toPureEffectType t = fmap fst $ makeEffectType NoEffects t

-- | This function does the real work of 'toEffectType' and
-- 'toPureEffectType'.
makeEffectType :: Effectfulness -> Gluon.WSRExp -> RegionM (ERepType, [EVar])
makeEffectType effectfulness expr =
  case getLevel $ Gluon.fromWhnf $ Gluon.substFullyUnderWhnf expr
  of KindLevel -> do k <- makeEffectKind expr
                     return (k, [])
     TypeLevel ->
       case Gluon.unpackRenamedWhnfAppE expr
       of Just (con, args) -> makeConstructorApplication effectfulness con args
          Nothing ->
            case Gluon.fromWhnf expr
            of Gluon.FunE {} -> makeFunctionType effectfulness expr
               Gluon.AppE {Gluon.expOper = op, Gluon.expArgs = args} -> do 
                 (op', op_evars) <- makeEffectType' effectfulness op
                 (unzip -> (args', concat -> args_evars)) <-
                   mapM (makeEffectType' effectfulness) args
                 return (appT op' args', op_evars ++ args_evars)
               Gluon.VarE {Gluon.expVar = v} -> return (varT v, [])
               Gluon.LitE {Gluon.expLit = l} -> return (litT l, [])
               _ -> internalError "makeEffectType"
     _ -> internalError "makeEffectType"

makeEffectType' :: Effectfulness -> Gluon.SRExp -> RegionM (ERepType, [EVar])
makeEffectType' effectfulness expr =
  makeEffectType effectfulness =<< evalHead expr

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
makeConstructorApplication effectfulness sf_con args = do
  (unzip -> (args', concat -> arg_evars)) <-
    mapM (makeEffectType' local_effectfulness) args
  (con_inst, con_evars) <-
    instantiateTypeCon local_effectfulness core_con args'
  return (con_inst, con_evars ++ arg_evars)
  where
    -- Don't let side effects appear in parameters to dictionary types 
    local_effectfulness =
      if isDictionaryTypeCon sf_con
      then NoEffects
      else effectfulness
    
    core_con
      | sf_con `SF.isPyonBuiltin` SF.the_Stream = SF.pyonBuiltin SF.the_LazyStream
      | otherwise = sf_con

-- | Create a function type from the expression.  In the type, assume that 
-- all parameters are read.  Side effects from parameters will be placed on 
-- the last arrow.  In other words, the function only produces side effects
-- after all parameters are applied.
makeFunctionType :: Effectfulness -> Gluon.WSRExp -> RegionM (ERepType, [EVar])
makeFunctionType effectfulness expr =
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
               (rng', rng_evars) <- makeEffectType effectfulness expr

               -- If side effect variables are allowed here,
               -- create a variable to stand for this expression's free effect
               (param_effects', extra_evar) <-
                 case effectfulness
                 of NoEffects -> return (emptyEffect, [])
                    RestrictedEffects -> return (param_effects, [])
                    ArbitraryEffects -> do
                      effect_var <- newEffectVar
                      return (param_effects `effectUnion` varEffect effect_var,
                              [effect_var])

               return (rng', param_effects', extra_evar ++ rng_evars)

    -- Convert the parameter on the left side of an (->)
    make_domain_type param_effects (Binder' mv dom ()) = do
      (dom', dom_evars) <- makeEffectType' effectfulness dom
      param <- etypeToParamType dom' mv
           
      -- Include this parameter in the function's side effect
      let param_effects' =
            param_effects `effectUnion` maybeVarEffect (paramTypeRegion param)
      return (param, param_effects', dom_evars)

-- | Given a function type, unpack it into parameters and arguments.
--   Unpacking stops at the first effect type that is not literally the empty
--   effect.
unpackFunctionType :: EReturnType -> ([EParamType], Effect, EReturnType)
unpackFunctionType rtype = unpack id rtype
  where
    unpack params_head (OwnRT (FunT param eff ret))
      | isEmptyEffect eff = unpack (params_head . (param:)) ret
      | otherwise = (params_head [param], eff, ret)
    unpack params_head rt = (params_head [], emptyEffect, rt)

-------------------------------------------------------------------------------
-- Conversion from core to effect types

-- | A mapping from a core variable to a unifiable region or effect variable
type CoreEnv = Map.Map Var EffectVar

-- | During translation from Core type to effect inference type, new unifiable
-- region and effect variables are created for each type.
type CoreTrans a = ReaderT CoreEnv RegionM a

-- | Type arguments to an operator that hasn't been converted tye
data Args = NoArgs
          | EffArgs [Effect]
          | Args [Effect] [ERepType]

nonemptyArgs NoArgs = False
nonemptyArgs _ = True

mkArgs :: [Effect] -> [ERepType] -> Args
mkArgs [] [] = NoArgs
mkArgs es [] = EffArgs es
mkArgs es ts = Args es ts

fromArgs :: Args -> ([Effect], [ERepType])
fromArgs NoArgs       = ([], [])
fromArgs (EffArgs es) = (es, [])
fromArgs (Args es ts) = (es, ts)

applyArgsVar :: Var -> Args -> ERepType
applyArgsVar v args =
  case fromArgs args
  of ([], types) -> appT (varT v) types
     (es, types) -> instT (Left v) es types

applyArgsCon :: Con -> Args -> ERepType
applyArgsCon c args =
  case fromArgs args
  of ([], types) -> conAppT c types
     (es, types) -> instT (Right c) es types  

-- | Apply a literal to type arguments.  The arguments should be empty.
applyArgsLit :: Gluon.Lit -> Args -> ERepType
applyArgsLit l NoArgs = litT l
applyArgsLit _ _ = internalError "Unexpected type application of literal"

concatArgs x NoArgs = x
concatArgs NoArgs x = x
concatArgs (EffArgs e1) (EffArgs e2) = EffArgs (e1 ++ e2)
concatArgs (EffArgs e1) (Args e2 ts) = Args (e1 ++ e2) ts
concatArgs (Args _ _) (EffArgs _)    = internalError "Unexpected effect argument"
concatArgs (Args e1 t1) (Args [] t2) = Args e1 (t1 ++ t2)
concatArgs (Args _ _) (Args (_:_) _) = internalError "Unexpected effect argument"

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
     _ -> do t <- cTypeToEffectType ty NoArgs
             return ([], t)
  where
    from_poly_type ft@(Core.ArrCT (Core.ValPT mv Core.::: param_ty) eff rng) 
      | is_effect_type param_ty =
          maybe (lift newEffectVar >>=) withCoreEffectVar mv $ \evar -> do
            (qvars, ty) <- cTypeToPolyEffectType (Core.FunCT rng)
            return (evar : qvars, ty)
    
      | otherwise = do t <- cTypeToEffectType (Core.FunCT ft) NoArgs
                       return ([], t)

    -- Functions must have a non-effect parameter
    from_poly_type (Core.RetCT _) = internalError "cTypeToPolyEffectType"

    is_effect_type (Core.ExpCT (Gluon.LitE {Gluon.expLit = Gluon.KindL Gluon.EffectKind})) = True
    is_effect_type _ = False

-- | Convert the given Core type to an effect type and apply it to the given
--   type arguments.
--
--   This is done as one step because the given arguments may influence how
--   the type is converted.
cTypeToEffectType :: Core.RCType -> Args -> CoreTrans ERepType
cTypeToEffectType ty ty_args =
  case ty
  of Core.ExpCT e -> gluonTypeToEffectType e ty_args
     Core.AppCT op args -> do
       args' <- cTypeArgumentsToEffectTypes args
       cTypeToEffectType op (concatArgs args' ty_args)
     Core.FunCT ft 
       | nonemptyArgs ty_args -> internalError "cTypeToEffectType: Function type applied to arguments"
       | otherwise -> cFunTypeToEffectType ft
     
-- | Convert a list of Core type arguments to effect-annotated types.
-- A prefix of the arguments consists of effects; the rest are types.
cTypeArgumentsToEffectTypes :: [Core.RCType] -> CoreTrans Args
cTypeArgumentsToEffectTypes types = cvt_eff id types
  where
    -- Convert effect types, then convert other types
    cvt_eff hd (t:ts) = isCoreEffectType t >>= convert
      where 
        -- Convert an effect parameter
        convert True = do
          eff <- cTypeToEffect t
          cvt_eff (hd . (eff:)) ts
        -- Convert remaining parameters (which are all type parameters)
        convert False = do
          types <- forM (t:ts) $ \t -> cTypeToEffectType t NoArgs
          return $ mkArgs (hd []) types
    cvt_eff hd []     = return $ mkArgs (hd []) []

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
      rng' <- cTypeToEffectType rng NoArgs
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
      -- Cannot convert parameters whose type is "Effect" because it requires
      -- support for higher-rank types
      when (is_effect_kind dom) $
        internalError "cFunTypeToEffectType: Unsupported higher-rank effect type"

      dom' <- cTypeToEffectType dom NoArgs
      let dom_t = discardTypeRepr dom'
      case param of
        Core.ValPT mv -> k $ ValPT mv dom_t
        Core.OwnPT    -> k $ OwnPT dom_t
        Core.ReadPT v -> withCoreRegionVar v $ \v' -> k $ ReadPT v' dom_t
    
    is_effect_kind (Core.ExpCT (Gluon.LitE {Gluon.expLit = Gluon.KindL Gluon.EffectKind})) = True
    is_effect_kind _ = False

-- | Convert a Gluon type to an effect type.  If the Gluon type was applied to
--   arguments, then those arguments should be passed to this function.  They 
--   will be used to determine the type's representation.
--
-- Type-level types may only consist of variables, constructors, and 
-- applications.  Kind-level types may have arrows.
--
-- /FIXME/: Convert effect types using cTypeToEffect.  Use Core type inference
-- to identify effect types.
gluonTypeToEffectType :: Gluon.RExp -> Args -> CoreTrans ERepType
gluonTypeToEffectType expr ty_args =
  case expr
  of Gluon.VarE {Gluon.expVar = v} -> return $ applyArgsVar v ty_args
     Gluon.ConE {Gluon.expCon = c} -> return $ applyArgsCon c ty_args
     Gluon.LitE {Gluon.expLit = l} -> return $ applyArgsLit l ty_args
     Gluon.AppE {Gluon.expOper = op, Gluon.expArgs = args} -> do
       args' <- forM args $ \arg -> gluonTypeToEffectType arg NoArgs
       gluonTypeToEffectType op (concatArgs (mkArgs [] args') ty_args)
     Gluon.FunE { Gluon.expMParam = Gluon.Binder' Nothing dom ()
                , Gluon.expRange = rng}
       | getLevel expr /= KindLevel -> 
           internalError "gluonTypeToEffectType: Unexpected function type"
       | nonemptyArgs ty_args ->
           internalError "gluonTypeToEffectType: Function type was applied to parameters"
       | otherwise -> do
           dom' <- gluonTypeToEffectType dom NoArgs
           param <- lift $ etypeToParamType dom' Nothing
           rng' <- gluonTypeToEffectType rng NoArgs
           ret <- lift $ etypeToReturnType rng'
           return $ funT param emptyEffect ret
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

