
{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
module Type.Type(Type(..),
                 ParamType,
                 ReturnType,
                 (:::)(..),
                 Repr(..),
                 ParamRepr(..),
                 ReturnRepr(..),
                 paramReprToRepr,
                 returnReprToRepr,
                 typeApp, varApp,
                 fromTypeApp, fromVarApp,
                 pureFunType, funType,
                 kindT, pureT,
                 kindV, pureV,
                 firstAvailableVarID,
                 pprType, pprParam, pprReturn)
where

import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Core.Level
import LowLevel.Label
import Type.Var

data Type =
    -- | A variable or constructor
    VarT Var
    -- | A type application
  | AppT Type Type
    -- | A function type
  | FunT !ParamType !ReturnType

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

pureFunType, funType :: [(ParamRepr ::: Type)] -> ReturnRepr ::: Type -> Type
pureFunType = constructFunctionType ValRT
funType = constructFunctionType BoxRT

constructFunctionType repr [] ret = internalError "funType: No parameters" 
constructFunctionType repr ps ret = go ps
  where
    go [p]    = FunT p ret 
    go (p:ps) = FunT p (repr ::: go ps)

data x ::: y = x ::: y

-- | A representation.
data Repr = Value               -- ^ Represented as a value.  Variables hold
                                --   the actual data
          | Boxed               -- ^ Boxed.  Variables hold a pointer to
                                --   memory-managed data.
          | Referenced          -- ^ Referenced.  Variables hold a pointer to
                                --   non-memory-managed data.
            deriving (Eq, Ord)

-- | A function parameter representation.
--
-- A value parameter means that the data is actually passed to the function.
-- A boxed or read reference means that a pointer is passed to the function.
-- A write reference means that the /function/ passes a pointer to its
-- /argument/, which writes its data at the given address.
data ParamRepr =
    ValPT !(Maybe Var)       -- ^ Pass as a (possibly dependent) value
  | BoxPT                       -- ^ Pass a boxed reference
  | ReadPT                      -- ^ Pass a readable reference
  | WritePT                     -- ^ Pass a written reference

-- | A return parameter representation.
--
-- A value return means that the data is returned.  A boxed, or read return
-- means that a pointer to the data is returned.  A write return means that
-- the return address is taken as a parameter, and will be written in the
-- function.
data ReturnRepr =
    ValRT
  | BoxRT
  | ReadRT
  | WriteRT

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

instance HasLevel Var => HasLevel Type where
  getLevel (VarT v) = getLevel v
  getLevel (AppT op _) = getLevel op
  getLevel (FunT _ (_ ::: rng)) = getLevel rng

kindT, pureT :: Type
kindT = VarT kindV
pureT = VarT pureV

kindV, pureV :: Var

kindV = mkVar kindVarID (Just $ pyonLabel builtinModuleName "kind") SortLevel
pureV = mkVar kindVarID (Just $ pyonLabel builtinModuleName "pure") KindLevel

kindVarID = toIdent 1
pureVarID = toIdent 2

-- | The first variable ID that's not reserved for predefined variables
firstAvailableVarID :: VarID
firstAvailableVarID = toIdent 10

-------------------------------------------------------------------------------
-- Pretty-printing

pprTypeParen :: Type -> Doc
pprTypeParen t = parens $ pprType t

pprAppArgType t = 
  case t
  of VarT {} -> pprType t
     _ -> pprTypeParen t

pprFunArgType repr t =
  case t
  of FunT {} -> parens (pprTypeRepr (Just repr) t)
     _ -> pprTypeRepr (Just repr) t

pprType :: Type -> Doc
pprType (VarT v) = pprVar v
pprType (AppT op arg) = ppr_app op [arg]
  where
    ppr_app (AppT op' arg') args = ppr_app op' (arg':args)
    ppr_app op' args = pprAppArgType op' <+> sep (map pprAppArgType args)

pprType (FunT arg ret) =
  let repr = case ret
             of BoxRT ::: FunT {} -> Just Boxed
                ValRT ::: FunT {} -> Just Value
                _ -> Nothing
      fun_doc = pprTypeRepr repr (FunT arg ret)
  in case repr
     of Just Boxed -> text "box" <+> parens fun_doc
        Just Value -> text "val" <+> parens fun_doc
        _ -> fun_doc

pprTypeRepr repr ty =
  case ty
  of FunT arg ret -> pprFunType repr [pprParam arg] ret
     _ -> pprType ty

pprFunType erepr params (ret_repr ::: FunT arg ret)
  | return_repr_match = pprFunType erepr (pprParam arg : params) ret
  where
    return_repr_match =
      case ret_repr
      of BoxRT -> erepr == Just Boxed
         ValRT -> erepr == Just Value
         _ -> False

pprFunType erepr params ret =
  let items = reverse (pprReturn ret : map (<+> text "->") params)
  in sep items

pprReturn (ret ::: rng) =  
  let repr_doc =
        case ret
        of ValRT -> text "val"
           BoxRT -> text "box"
           ReadRT -> text "read"
           WriteRT -> text "write"
  in repr_doc <+> pprFunArgType (returnReprToRepr ret) rng
      
pprParam (arg ::: dom) =
  case arg
  of ValPT Nothing -> ordinary_lhs $ text "val"
     ValPT (Just v) -> parens $
                       text "val" <+> pprVar v <+> text ":" <+> pprType dom
     BoxPT -> ordinary_lhs $ text "box"
     ReadPT -> ordinary_lhs $ text "read"
     WritePT -> ordinary_lhs $ text "write"
  where
    ordinary_lhs repr_doc =
      repr_doc <+> pprFunArgType (paramReprToRepr arg) dom
