
{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
module Type.Type(Type(..), (:::)(..), ParamRepr(..), ReturnRepr(..),
                 kindV, pureV,
                 firstAvailableVarID,
                 pprType, pprParam, pprReturn)
where

import Text.PrettyPrint.HughesPJ

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
  | FunT !(ParamRepr ::: Type) !(ReturnRepr ::: Type)

data x ::: y = x ::: y

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

instance HasLevel Var => HasLevel Type where
  getLevel (VarT v) = getLevel v
  getLevel (AppT op _) = getLevel op
  getLevel (FunT _ (_ ::: rng)) = getLevel rng

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

pprFunArgType t =
  case t
  of FunT {} -> pprTypeParen t
     _ -> pprType t

pprType :: Type -> Doc
pprType (VarT v) = pprVar v
pprType (AppT op arg) = ppr_app op [arg]
  where
    ppr_app (AppT op' arg') args = ppr_app op' (arg':args)
    ppr_app op' args = pprAppArgType op <+> sep (map pprAppArgType args)

pprType (FunT arg ret) = ppr_fun_type [pprParam arg] ret 
  where 
    ppr_fun_type rparams (BoxRT ::: FunT arg ret) =
      ppr_fun_type (pprParam arg : rparams) ret

    ppr_fun_type rparams ret =
      let items = reverse (pprReturn ret : map (<+> text "->") rparams)
      in sep items
    
pprReturn (ret ::: rng) =  
  let repr_doc =
        case ret
        of ValRT -> text "val"
           BoxRT -> text "box"
           ReadRT -> text "read"
           WriteRT -> text "write"
  in repr_doc <+> pprFunArgType rng
      
pprParam (arg ::: dom) =
  case arg
  of ValPT Nothing -> ordinary_lhs $ text "val"
     ValPT (Just v) -> parens $
                       text "val" <+> pprVar v <+> text ":" <+> pprType dom
     BoxPT -> ordinary_lhs $ text "box"
     ReadPT -> ordinary_lhs $ text "read"
     WritePT -> ordinary_lhs $ text "write"
  where
    ordinary_lhs repr_doc = repr_doc <+> pprFunArgType dom
