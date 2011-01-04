
{-# LANGUAGE ViewPatterns #-}
module CParser.GenCore (ConTable, createCoreTable) where

import qualified Data.IntMap as IntMap

import Gluon.Common.SourcePos
import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Core(Var, Con(conID), Rec)
import Gluon.Core.Level
import qualified Gluon.Core.Builtins as Gluon
import qualified Gluon.Core as Gluon
import CParser.AST
import CParser.LevelInference()
import qualified SystemF.Builtins as SF
import qualified Core.Syntax as Core

type ConTable = IntMap.IntMap (Core.CBind Core.CReturnT Rec)

addressType = Core.ValRT Core.::: addr_type
  where
    addr_type = Core.ExpCT $ Gluon.mkInternalConE (Gluon.builtin Gluon.the_Addr)

pointerType = Core.ValRT Core.::: ptr_type
  where
    ptr_type = Core.ExpCT $ Gluon.mkInternalConE (SF.pyonBuiltin SF.the_Ptr)

emptyEffect = Core.ExpCT $ Gluon.mkInternalConE (Gluon.builtin Gluon.the_EmpE)

fromLICon (LICon c) = c
fromLICon _ = internalError "fromLICon"

fromLIVar (LIVar v) = v
fromLIVar _ = internalError "fromLIVar"

translateType :: LvLType -> Core.RCType
translateType lty =
  case unLoc lty
  of VarT (LIVar v) -> Core.varCT v
     VarT (LICon c) -> Core.conCT c
     VarT (LIKind k) -> Core.ExpCT $ Gluon.mkLitE noSourcePos (Gluon.KindL k)
     LitT l -> internalError "translateType: Not implemented for literals"
     AppT op args -> Core.appCT (translateType op) (map translateType args)
     FunT {} 
       | getLevel lty == Gluon.KindLevel -> translateFunKind lty
       | otherwise -> Core.FunCT $ translateFunType lty

translateFunType :: LvLType -> Core.RCFunType
translateFunType (unLoc -> FunT param meff rng) =
  Core.arrCT (translateParamType param)
  (maybe emptyEffect translateType meff)
  (translateReturnType rng)

translateFunKind (unLoc -> FunT param _ rng)
  | ValuePT Nothing pt <- param,
    Value == rtRepr rng =
      case translateType pt
      of Core.ExpCT param_kind ->
           case translateType $ rtType rng
           of Core.ExpCT ret_kind ->
                Core.ExpCT $ Gluon.mkInternalArrowE False param_kind ret_kind
              _ -> not_kind
         _ -> not_kind
  | otherwise = not_kind
  where
    not_kind = internalError "Expression is not a valid kind"

translateParamType (ValuePT v t) =
  let param =
        case v
        of Nothing -> Nothing
           Just (LIVar p_var) -> Just p_var
           _ -> internalError "translateParamType"
  in Core.ValPT param Core.::: translateType t
translateParamType (BoxedPT t) = Core.OwnPT Core.::: translateType t
translateParamType (ReferencedPT a t) = 
  case a
  of LIVar a_var -> Core.ReadPT a_var Core.::: translateType t
     _ -> internalError "translateParamType"

translateReturnType :: ReturnType LevelInferred -> Core.RCFunType
translateReturnType rt
  | rtRepr rt == Boxed,
    range <- rtType rt, 
    FunT {} <- unLoc range = translateFunType range
  | otherwise =
    Core.RetCT $ translate_repr (rtRepr rt) Core.::: translateType (rtType rt)
  where
    translate_repr Value = Core.ValRT
    translate_repr Boxed = Core.OwnRT
    translate_repr Reference = Core.WriteRT

translateDecl :: LvDecl -> [(Con, Core.CBind Core.CReturnT Rec)]
translateDecl (BoxedDecl v ty) =
  [(fromLICon v, Core.OwnRT Core.::: translateType ty)]

translateDecl (DataDecl a p ty) =
  [(fromLICon p, Core.ReadRT addr Core.::: translateType ty)]
  where
    addr = Gluon.mkInternalVarE (fromLIVar a)

createCoreTable :: LvModule -> ConTable
createCoreTable (Module decls) =
  IntMap.fromList [(fromIdent $ conID c, ty)
                  | (c, ty) <- concatMap (translateDecl . unLoc) decls]