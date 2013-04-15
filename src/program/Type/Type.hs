{-| Most type-related definitions are here.
Some definitions that use Template Haskell have been moved
into "Type.BuiltinVar".
-}
{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
{-# OPTIONS_GHC -no-auto #-}
module Type.Type(module Type.Var,
                 module Type.Level,
                 module Type.BuiltinVar,
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

                 firstAvailableVarID,
                 builtinVarTable,

                 -- * Kinds
                 Kind,
                 BaseKind(..),
                 toBaseKind, fromBaseKind,

                 -- * Pretty-printing
                 pprType, pprTypePrec)
where

import Control.DeepSeq
import Text.PrettyPrint.HughesPJ

import Common.PrecDoc
import Common.Error
import Common.Identifier
import Common.Label
import Type.Var
import Type.Level
import Type.BuiltinVar

instance NFData Type where
  rnf (VarT v)     = rnf v
  rnf (AppT s t)   = rnf s `seq` rnf t
  rnf (LamT b t)   = rnf b `seq` rnf t
  rnf (FunT s t)   = rnf s `seq` rnf t
  rnf (AllT b t)   = rnf b `seq` rnf t
  rnf (AnyT k)     = rnf k
  rnf (IntT n)     = rnf n
  rnf (CoT k)      = rnf k
  rnf (UTupleT ks) = rnf ks

instance NFData Binder where rnf (v ::: k) = rnf v `seq` rnf k

instance NFData BaseKind where rnf k = k `seq` ()

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

instance NFData KindedType where rnf (KindedType _ t) = rnf t

getBaseKind :: KindedType -> BaseKind
getBaseKind (KindedType k _) = k

discardBaseKind :: KindedType -> Type
discardBaseKind (KindedType _ t) = t

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

-------------------------------------------------------------------------------
-- Convenience functions for kinds

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

