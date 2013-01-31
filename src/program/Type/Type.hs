
{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
{-# OPTIONS_GHC -no-auto #-}
module Type.Type(module Type.Var,
                 module Type.Level,
                 Type(..),
                 KindedType(..),
                 Binder(..),

                 -- * Construction and deconstruction helper routines
                 typeApp, varApp,
                 fromTypeApp, fromVarApp,
                 funType, fromFunType,
                 forallType, fromForallType,
                 fromForallFunType,
                 getBaseKind, discardBaseKind,

                 -- * Predefined types
                 kindT, intindexT, valT, boxT, bareT, outT, initT,
                 initConT,
                 outPtrT, storeT, posInftyT, negInftyT, arrT, intT, uintT, floatT,
                 kindV, intindexV, valV, boxV, bareV, outV, initV,
                 initConV,
                 outPtrV, storeV, posInftyV, negInftyV, arrV, intV, uintV, floatV,
                 arrTypeParameter1, arrTypeParameter2,
                 firstAvailableVarID,

                 -- * Kinds
                 Kind,
                 BaseKind(..),
                 toBaseKind, fromBaseKind,

                 -- * Pretty-printing
                 pprType, pprTypePrec)
where

import Text.PrettyPrint.HughesPJ

import Common.PrecDoc
import Common.Error
import Common.Identifier
import Common.Label
import Type.Var
import Type.Level

data Type =
    -- | A variable or constructor
    VarT Var
    -- | A type application
  | AppT Type Type
    -- | A type function
  | LamT {-#UNPACK#-}!Binder Type
    -- | A function type
  | FunT Type Type
    -- | A universal quantifier
  | AllT {-#UNPACK#-}!Binder Type
    -- | An arbitrary, opaque type inhabiting the given kind.  The kind has
    --   no free type variables.
  | AnyT Type
    -- | An integer type index.  These inhabit kind 'intIndexT'.
  | IntT !Integer
    
    -- | A coercion type constructor.
    --
    --   A coercion (s ~ t) carries the ability to coerce a value of type s
    --   to a value of type t.
  | CoT Kind

    -- | An unboxed tuple constructor.
    --   The type parameters have the specified kinds, which must be either
    --   'ValK' or 'BoxK'.
    --
    --   Unboxed tuples are introduced after representation inference.
  | UTupleT ![BaseKind]

infixr 4 `FunT`
infixl 7 `AppT`

-- | Create a type application
typeApp :: Type -> [Type] -> Type
typeApp op args = foldl AppT op args

varApp :: Var -> [Type] -> Type
varApp v ts = typeApp (VarT v) ts

fromTypeApp :: Type -> (Type, [Type])
fromTypeApp t = fta t []
  where
    fta (AppT op arg) args = fta op (arg:args)
    fta t args = (t, args)

fromVarApp :: Type -> Maybe (Var, [Type])
fromVarApp t = case fromTypeApp t
               of (VarT v, args) -> Just (v, args)
                  _ -> Nothing

funType :: [Type] -> Type -> Type
funType [] t = t
funType (p:ps) t = FunT p (funType ps t)

fromFunType :: Type -> ([Type], Type)
fromFunType t = go id t
  where
    go hd (FunT dom rng) = go (hd . (dom:)) rng
    go hd rng = (hd [], rng)

forallType :: [Binder] -> Type -> Type
forallType args ret = foldr AllT ret args

fromForallType :: Type -> ([Binder], Type)
fromForallType t = go id t
  where
    go hd (AllT param rng) = go (hd . (param:)) rng
    go hd t = (hd [], t)

fromForallFunType :: Type -> ([Binder], [Type], Type)
fromForallFunType t =
  let (qvars, monotype) = fromForallType t
      (dom, rng) = fromFunType monotype
  in (qvars, dom, rng)

-- | A type annotated with its base kind
data KindedType = KindedType !BaseKind Type

getBaseKind :: KindedType -> BaseKind
getBaseKind (KindedType k _) = k

discardBaseKind :: KindedType -> Type
discardBaseKind (KindedType _ t) = t

data Binder = (:::) { binderVar :: Var, binderType :: Type}

instance HasLevel Var => HasLevel Type where
  getLevel (VarT v) = getLevel v
  getLevel (AppT op _) = getLevel op
  getLevel (LamT _ body) = getLevel body
  getLevel (FunT _ rng) = getLevel rng
  getLevel (AllT _ rng) = getLevel rng
  getLevel (AnyT _) = TypeLevel
  getLevel (IntT _) = TypeLevel
  getLevel (CoT _)  = TypeLevel
  getLevel (UTupleT _) = TypeLevel

kindT, intindexT, valT, boxT, bareT, outT, initT,
  initConT, outPtrT, storeT, posInftyT, negInftyT, arrT,
  intT, uintT, floatT :: Type

kindT = VarT kindV
intindexT = VarT intindexV
valT = VarT valV
boxT = VarT boxV
bareT = VarT bareV
outT = VarT outV
initT = VarT initV
initConT = VarT initConV
outPtrT = VarT outPtrV
storeT = VarT storeV
posInftyT = VarT posInftyV      -- Positive infinity
negInftyT = VarT negInftyV
arrT = VarT arrV
intT = VarT intV
uintT = VarT uintV
floatT = VarT floatV

kindV, intindexV, valV, boxV, bareV, outV, initV,
  initConV, outPtrV, storeV, posInftyV, negInftyV, arrV, intV, uintV, floatV,
  arrTypeParameter1, arrTypeParameter2 :: Var

kindV = mkVar kindVarID (Just $ plainLabel builtinModuleName "kind") SortLevel
intindexV = mkVar intindexVarID (Just $ plainLabel builtinModuleName "intindex") KindLevel
valV = mkVar valVarID (Just $ plainLabel builtinModuleName "val") KindLevel
boxV = mkVar boxVarID (Just $ plainLabel builtinModuleName "box") KindLevel
bareV = mkVar bareVarID (Just $ plainLabel builtinModuleName "bare") KindLevel
outV = mkVar outVarID (Just $ plainLabel builtinModuleName "out") KindLevel
initV = mkVar writeVarID (Just $ plainLabel builtinModuleName "init") KindLevel
initConV = mkVar initConVarID (Just $ plainLabel builtinModuleName "Init") TypeLevel
outPtrV = mkVar outPtrVarID (Just $ plainLabel builtinModuleName "OutPtr") TypeLevel
storeV = mkVar storeVarID (Just $ plainLabel builtinModuleName "Store") TypeLevel
posInftyV = mkVar posInftyVarID (Just $ plainLabel builtinModuleName "pos_infty") TypeLevel
negInftyV = mkVar negInftyVarID (Just $ plainLabel builtinModuleName "neg_infty") TypeLevel
arrV = mkVar arrVarID (Just $ plainLabel builtinModuleName "arr") TypeLevel
intV = mkVar intVarID (Just $ plainLabel builtinModuleName "int") TypeLevel
uintV = mkVar uintVarID (Just $ plainLabel builtinModuleName "uint") TypeLevel
floatV = mkVar floatVarID (Just $ plainLabel builtinModuleName "float") TypeLevel

-- Used to construct the built-in data type definition for arrays
arrTypeParameter1 = mkVar arrTypeParameter1ID (Just $ plainLabel builtinModuleName "n") TypeLevel
arrTypeParameter2 = mkVar arrTypeParameter2ID (Just $ plainLabel builtinModuleName "a") TypeLevel

kindVarID = toIdent 1
intindexVarID = toIdent 2
valVarID = toIdent 3
boxVarID = toIdent 4
bareVarID = toIdent 5
outVarID = toIdent 6
writeVarID = toIdent 7
initConVarID = toIdent 8
outPtrVarID = toIdent 9
storeVarID = toIdent 10
posInftyVarID = toIdent 11
negInftyVarID = toIdent 12
arrVarID = toIdent 13
intVarID = toIdent 14
uintVarID = toIdent 15
floatVarID = toIdent 16
arrTypeParameter1ID = toIdent 17
arrTypeParameter2ID = toIdent 18

-- | The first variable ID that's not reserved for predefined variables
firstAvailableVarID :: VarID
firstAvailableVarID = toIdent 19

-------------------------------------------------------------------------------
-- Convenience functions for kinds

-- | Kinds and types are represented using the same data structures
type Kind = Type

-- | Base kinds as an enumerative data structure.  Each base kind corresponds
--   to a variable.
data BaseKind =
    ValK
  | BoxK
  | BareK
  | OutK
  | WriteK
  | IntIndexK
    deriving(Eq, Ord, Show)

-- | Convert a kind to a base kind.  Raises an error if the argument is not a
--   base kind.
toBaseKind :: Kind -> BaseKind
toBaseKind (VarT kind_var) =
  case lookup kind_var table
  of Just k -> k
     Nothing -> internalError "toBaseKind: Unrecognized type"
  where
    table = [(valV, ValK), (boxV, BoxK), (bareV, BareK), (outV, OutK),
             (initV, WriteK),
             (intindexV, IntIndexK)]

toBaseKind _ = internalError "toBaseKind: Unrecognized type"

fromBaseKind :: BaseKind -> Kind
fromBaseKind k =
  case k
  of ValK -> valT
     BoxK -> boxT
     BareK -> bareT
     OutK -> outT
     WriteK -> initT
     IntIndexK -> intindexT

-------------------------------------------------------------------------------
-- Pretty-printing

{-
pprTypeParen :: Type -> Doc
pprTypeParen t = parens $ pprType t

pprAppArgType t =
  case t
  of VarT {} -> pprType t
     _ -> pprTypeParen t

pprFunArgType repr t =
  case t
  of FunT {} -> parens (pprTypeRepr (Just repr) t)
     _ -> pprTypeRepr (Just repr) t-}

pprType :: Type -> Doc
pprType t = unparenthesized $ pprTypePrec t

pprTypePrec :: Type -> PrecDoc
pprTypePrec ty = {-# SCC pprTypePrec #-}
  case ty
  of VarT v -> hasAtomicPrec $ pprVar v
     -- Special syntax for coercions
     AppT (AppT (CoT _) arg1) arg2 ->
       (pprTypePrec arg1 ?+ cmpPrec <+> text "~" <+> pprTypePrec arg2 ?+ cmpPrec) `hasPrec` cmpPrec
     AppT op arg -> ppr_app op [arg] `hasPrec` appPrec
     LamT param body -> ppr_lam [param] body `hasPrec` lamPrec
     FunT arg ret -> pprFunType ty
     AllT binder rng -> ppr_all [binder] rng `hasPrec` lamPrec
     AnyT k -> text "Any :" <+> pprTypePrec k ?+ typeAnnPrec `hasPrec` typeAnnPrec
     IntT n -> hasAtomicPrec $ text (show n)
     CoT k -> text "Coercion :" <+> pprTypePrec k ?+ typeAnnPrec `hasPrec` typeAnnPrec 
     UTupleT ks -> text "UTuple" <+> utuple_tags ks `hasPrec` appPrec
  where
    utuple_tags ks =
      text "<" <> hcat (punctuate (text ",") $ map ppr_k ks) <> text ">"
      where
        ppr_k ValK = text "val"
        ppr_k BoxK = text "box"
        ppr_k _    = text "ERROR"

    -- Uncurry the application
    ppr_app (AppT op' arg') args = ppr_app op' (arg':args)
    ppr_app op' args = sep [pprTypePrec t ?+ appPrec | t <- op' : args]
    
    -- Uncurry the lambda abstraction.  Uncurrying builds the parameter list
    -- in reverse order, so we reverse it again.
    ppr_lam params (LamT param body) = ppr_lam (param : params) body
    ppr_lam params e =
      hang (text "lambda" <+> sep (map ppr_binder $ reverse params) <> text ".") 4
      (pprTypePrec e ? lamPrec)

    ppr_binder (v ::: t) =
      parens $ pprVar v <+> text ":" <+> pprTypePrec t ?+ typeAnnPrec

    -- Uncurry the type abstraction.
    ppr_all params (AllT param rng) = ppr_all (param : params) rng
    ppr_all params e =
      hang (text "forall" <+> sep (map ppr_binder $ reverse params) <> text ".") 4
      (pprTypePrec e ? lamPrec)

-- | Pretty-print a function type.
pprFunType :: Type -> PrecDoc
pprFunType t =
  let (params, return) = fromFunType t
      param_docs = [pprTypePrec param ?+ appPrec <+> text "->" | param <- params]
      return_doc = pprTypePrec return ?+ appPrec
  in sep (param_docs ++ [return_doc]) `hasPrec` funPrec

