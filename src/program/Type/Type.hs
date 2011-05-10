
{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
module Type.Type(module Type.Var,
                 module Type.Level,
                 Type(..),
                 ParamType,
                 ReturnType,
                 (:::)(..),
                 Repr(..),
                 ParamRepr(..),
                 ReturnRepr(..),
                 sameParamRepr,
                 sameReturnRepr,
                 paramReprToRepr,
                 returnReprToRepr,
                 paramReprToReturnRepr,
                 returnReprToParamRepr,

                 -- * Construction and deconstruction helper routines
                 typeApp, varApp,
                 fromTypeApp, fromVarApp,
                 pureFunType, funType,
                 forallFunType,
                 fromFunType, fromPureFunType,

                 -- * Predefined types
                 kindT, pureT, intindexT, valT, boxT, bareT, outT, posInftyT,
                 kindV, pureV, intindexV, valV, boxV, bareV, outV, posInftyV,
                 firstAvailableVarID,

                 -- * Pretty-printing
                 pprType, pprTypePrec, pprReprType,
                 pprParam, pprReturn,
                 pprParamReprWord, pprReturnRepr)
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
  | LamT Var Type ReturnType
    -- | A function type.
    --
    --   Eventually this constructor will be simplified to @FunT Type Type@.
  | FunT !ParamType !ReturnType
    -- | A universal quantifier
  | AllT Var Type !ReturnType
    -- | An arbitrary, opaque type inhabiting the given kind.  The kind has
    --   no free type variables.
  | AnyT Type
    -- | An integer type index.  These inhabit kind 'intIndexT'.
  | IntT !Integer

infixr 4 `FunT`
infixl 7 `AppT`

type ParamType = ParamRepr ::: Type
type ReturnType = ReturnRepr ::: Type

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

pureFunType, funType :: [ParamType] -> ReturnType -> Type
pureFunType = constructFunctionType ValRT
funType = constructFunctionType BoxRT

constructFunctionType repr [] ret = internalError "funType: No parameters"
constructFunctionType repr ps ret = go ps
  where
    go [p]    = FunT p ret
    go (p:ps) = FunT p (repr ::: go ps)

forallFunType :: [(Var, Type)] -> Type -> Type
forallFunType args ret = foldr fa ret args
  where
    fa (v, t) ret = AllT v t (ValRT ::: ret)

fromPureFunType, fromFunType :: Type -> ([ParamType], ReturnType)
fromPureFunType = deconstructFunctionType ValRT
fromFunType = deconstructFunctionType BoxRT

deconstructFunctionType repr ty = go id (repr ::: ty)
  where
    go hd (value_repr ::: FunT dom rng)
      | sameReturnRepr repr value_repr = go (hd . (dom:)) rng

    go hd return_type = (hd [], return_type)

data x ::: y = x ::: y

-- | A representation.
data Repr = Value               -- ^ Represented as a value.  Variables hold
                                --   the actual data
          | Boxed               -- ^ Boxed.  Variables hold a pointer to
                                --   memory-managed data.
          | Referenced          -- ^ Referenced.  Variables hold a pointer to
                                --   non-memory-managed data.
            deriving (Eq, Ord, Show)

-- | A function parameter representation.
--
-- A value parameter means that the data is actually passed to the function.
-- A boxed or read reference means that a pointer is passed to the function.
-- A write reference means that the /function/ passes a pointer to its
-- /argument/, which writes its data at the given address.
data ParamRepr =
    ValPT !(Maybe Var)       -- ^ Pass as a (possibly dependent) value
  | BoxPT                    -- ^ Pass a boxed reference
  | ReadPT                   -- ^ Pass a readable reference
  | WritePT                  -- ^ Pass a written reference
  | OutPT                    -- ^ Pass an output reference
  | SideEffectPT             -- ^ A dummy parameter representing a dependence

-- | A return parameter representation.
--
-- A value return means that the data is returned.  A boxed, or read return
-- means that a pointer to the data is returned.  A write return means that
-- the return address is taken as a parameter, and will be written in the
-- function.
--
-- The three representations 'ReadRT', 'WriteRT', and 'OutRT' all pertain to
-- referenced objects.
-- 'ReadRT' is used for reading an object that was already created.  We can't
-- decide where we want the data, but we take whatever address we find it at.
-- 'WriteRT' is used for creating an object.  We decide where we want
-- the data to go before it's even created, and we tell the creator where to
-- put its output.
-- 'OutRT' is a write-only pointer.  Whereas a 'WriteRT' value is passed in
-- the direction that data flows, an 'OutRT' value
-- is passed in the opposite direction.  It's the consumer of a value telling
-- the producer where to put it.
--
-- 'SideEffectRT' is for dummy values that are passed around to keep track of
-- dependences.  Functions that store into memory return this.  Without it,
-- the functions would look like dead code because they don't return anything.
data ReturnRepr =
    ValRT                       -- ^ A value
  | BoxRT                       -- ^ A boxed object reference
  | ReadRT                      -- ^ A reference chosen by the producer
  | WriteRT                     -- ^ A reference chosen by the consumer
  | OutRT                       -- ^ A pointer to write-only data
  | SideEffectRT                -- ^ A dummy value to track dependences

returnReprToRepr :: ReturnRepr -> Repr
returnReprToRepr ValRT   = Value
returnReprToRepr BoxRT   = Boxed
returnReprToRepr ReadRT  = Referenced
returnReprToRepr WriteRT = Referenced

paramReprToRepr :: ParamRepr -> Repr
paramReprToRepr (ValPT _) = Value
paramReprToRepr BoxPT     = Boxed
paramReprToRepr ReadPT    = Referenced
paramReprToRepr WritePT   = Referenced

paramReprToReturnRepr :: ParamRepr -> ReturnRepr
paramReprToReturnRepr (ValPT _) = ValRT
paramReprToReturnRepr BoxPT = BoxRT
paramReprToReturnRepr ReadPT = ReadRT
paramReprToReturnRepr WritePT = WriteRT
paramReprToReturnRepr OutPT = OutRT
paramReprToReturnRepr SideEffectPT = SideEffectRT

returnReprToParamRepr :: ReturnRepr -> ParamRepr
returnReprToParamRepr ValRT = ValPT Nothing
returnReprToParamRepr BoxRT = BoxPT
returnReprToParamRepr ReadRT = ReadPT
returnReprToParamRepr WriteRT = WritePT
returnReprToParamRepr OutRT = OutPT
returnReprToParamRepr SideEffectRT = SideEffectPT

-- | True if the given representations are the same, False otherwise.
--   Parameter variables are ignored.
sameParamRepr :: ParamRepr -> ParamRepr -> Bool
sameParamRepr (ValPT _) (ValPT _) = True
sameParamRepr BoxPT     BoxPT     = True
sameParamRepr ReadPT    ReadPT    = True
sameParamRepr WritePT   WritePT   = True
sameParamRepr OutPT     OutPT     = True
sameParamRepr SideEffectPT SideEffectPT = True
sameParamRepr _         _         = False

-- | True if the given representations are the same, False otherwise.
sameReturnRepr :: ReturnRepr -> ReturnRepr -> Bool
sameReturnRepr ValRT     ValRT     = True
sameReturnRepr BoxRT     BoxRT     = True
sameReturnRepr ReadRT    ReadRT    = True
sameReturnRepr WriteRT   WriteRT   = True
sameReturnRepr OutRT     OutRT     = True
sameReturnRepr SideEffectRT SideEffectRT = True
sameReturnRepr _         _         = False

instance HasLevel Var => HasLevel Type where
  getLevel (VarT v) = getLevel v
  getLevel (AppT op _) = getLevel op
  getLevel (FunT _ (_ ::: rng)) = getLevel rng
  getLevel (LamT _ _ (_ ::: body)) = getLevel body
  getLevel (AnyT _) = TypeLevel
  getLevel (IntT _) = TypeLevel

kindT, pureT, intindexT, valT, boxT, bareT, posInftyT :: Type
kindT = VarT kindV
pureT = VarT pureV
intindexT = VarT intindexV
valT = VarT valV
boxT = VarT boxV
bareT = VarT bareV
outT = VarT outV
posInftyT = VarT posInftyV      -- Positive infinity

kindV, pureV, intindexV, valV, boxV, bareV, posInftyV :: Var

kindV = mkVar kindVarID (Just $ pyonLabel builtinModuleName "kind") SortLevel
pureV = mkVar pureVarID (Just $ pyonLabel builtinModuleName "pure") KindLevel
intindexV = mkVar intindexVarID (Just $ pyonLabel builtinModuleName "intindex") KindLevel
valV = mkVar valVarID (Just $ pyonLabel builtinModuleName "val") KindLevel
boxV = mkVar boxVarID (Just $ pyonLabel builtinModuleName "box") KindLevel
bareV = mkVar bareVarID (Just $ pyonLabel builtinModuleName "bare") KindLevel
outV = mkVar outVarID (Just $ pyonLabel builtinModuleName "out") KindLevel
posInftyV = mkVar posInftyVarID (Just $ pyonLabel builtinModuleName "pos_infty") TypeLevel

kindVarID = toIdent 1
pureVarID = toIdent 2
intindexVarID = toIdent 3
valVarID = toIdent 4
boxVarID = toIdent 5
bareVarID = toIdent 6
outVarID = toIdent 8
posInftyVarID = toIdent 9

-- | The first variable ID that's not reserved for predefined variables
firstAvailableVarID :: VarID
firstAvailableVarID = toIdent 10

-------------------------------------------------------------------------------
-- Pretty-printing

-- | Pretty-print the name of a 'ParamRepr'.  The parameter variable (if any)
--   is ignored.
pprParamReprWord :: ParamRepr -> Doc
pprParamReprWord prepr =
  text $ case prepr
         of ValPT _      -> "val"
            BoxPT        -> "box"
            ReadPT       -> "read"
            WritePT      -> "write"
            OutPT        -> "out"
            SideEffectPT -> "sideeffect"

-- | Pretty-print a 'ReturnRepr'.
pprReturnRepr :: ReturnRepr -> Doc
pprReturnRepr rrepr =
  text $ case rrepr
         of ValRT        -> "val"
            BoxRT        -> "box"
            ReadRT       -> "read"
            WriteRT      -> "write"
            OutRT        -> "out"
            SideEffectRT -> "sideeffect"

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
pprTypePrec ty =
  case ty
  of VarT v -> hasAtomicPrec $ pprVar v
     AppT op arg -> ppr_app op [arg] `hasPrec` appPrec
     LamT v dom (_ ::: body) -> ppr_lam [(v, dom)] body `hasPrec` lamPrec
     FunT arg ret -> pprFunType Nothing ty
     AllT v dom (_ ::: rng) -> ppr_all [(v, dom)] rng `hasPrec` lamPrec
     AnyT k -> text "Any :" <+> pprTypePrec k ?+ typeAnnPrec `hasPrec` typeAnnPrec
     IntT n -> hasAtomicPrec $ text (show n)
  where
    -- Uncurry the application
    ppr_app (AppT op' arg') args = ppr_app op' (arg':args)
    ppr_app op' args = sep [pprTypePrec t ?+ appPrec | t <- op' : args]
    
    -- Uncurry the lambda abstraction.  Uncurrying builds the parameter list
    -- in reverse order, so we reverse it again.
    ppr_lam params (LamT v dom (_ ::: body)) = ppr_lam ((v, dom) : params) body
    ppr_lam params e =
      hang (text "lambda" <+> sep (map ppr_binder $ reverse params) <> text ".") 4
      (pprTypePrec e ? lamPrec)

    ppr_binder (v, t) =
      parens $ pprVar v <+> text ":" <+> pprTypePrec t ?+ typeAnnPrec

    -- Uncurry the type abstraction.
    ppr_all params (AllT v dom (_ ::: rng)) = ppr_all ((v, dom) : params) rng
    ppr_all params e =
      hang (text "forall" <+> sep (map ppr_binder $ reverse params) <> text ".") 4
      (pprTypePrec e ? lamPrec)

-- | Pretty-print a type with an implicit representation.  The implicit
--   representation is used when printing function types.
pprReprType :: ReturnRepr -> Type -> PrecDoc
pprReprType rrepr ty =
  case ty
  of FunT arg ret -> pprFunType (Just rrepr) ty
     _ -> pprTypePrec ty

-- | Pretty-print a function type.
pprFunType :: Maybe ReturnRepr -> Type -> PrecDoc
pprFunType erepr (FunT arg ret) =
  let (params, return) = decompose_function (pprParam arg :) ret
      param_docs = [param ?+ appPrec <+> text "->" | param <- params]
      return_doc = return ?+ appPrec
  in sep (param_docs ++ [return_doc]) `hasPrec` funPrec
  where
    -- Decompose the function into a parameter list and a return type
    decompose_function hd (ret_repr ::: FunT arg ret)
      | return_repr_match ret_repr =
          decompose_function (hd . (pprParam arg :)) ret
    
    decompose_function hd ty = (hd [], pprReturn ty)

    -- Is this the same as the expected representation?
    return_repr_match repr = maybe False (sameReturnRepr repr) erepr

pprFunType _ _ = internalError "pprFunType"

pprReturn :: ReturnType -> PrecDoc
pprReturn (ret ::: rng) =
  let repr_doc = pprReturnRepr ret
  in repr_doc <+> pprReprType ret rng ? appPrec `hasPrec` appPrec
      
pprParam :: ParamType -> PrecDoc
pprParam (arg ::: dom) =
  case arg
  of ValPT (Just v) ->
       arg_word <+> pprVar v <+> text ":" <+> pprTypePrec dom ?+ typeAnnPrec
       `hasPrec` typeAnnPrec
     _ -> ordinary_lhs
  where
    arg_word = pprParamReprWord arg
    ordinary_lhs =
      arg_word <+> pprReprType (paramReprToReturnRepr arg) dom ? appPrec
      `hasPrec` appPrec
