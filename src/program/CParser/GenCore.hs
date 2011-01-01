
{-# LANGUAGE ViewPatterns #-}
module CParser.GenCore (ConTable, createCoreTable) where

import qualified Data.IntMap as IntMap

import Gluon.Common.SourcePos
import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Core(Var, Con(conID), Rec)
import qualified Gluon.Core.Builtins as Gluon
import qualified Gluon.Core as Gluon
import CParser.AST
import qualified SystemF.Builtins as SF
import qualified Core.Syntax as Core

type ConTable = IntMap.IntMap Core.RCType

addressType = Core.ExpCT $ Gluon.mkInternalConE (Gluon.builtin Gluon.the_Addr)
pointerType = Core.ExpCT $ Gluon.mkInternalConE (SF.pyonBuiltin SF.the_Ptr)
emptyEffect = Core.ExpCT $ Gluon.mkInternalConE (Gluon.builtin Gluon.the_EmpE)

fromLICon (LICon c) = c
fromLICon _ = internalError "fromLICon"

translateType :: LvLType -> Core.RCType
translateType lty =
  case unLoc lty
  of VarT (LIVar v) -> Core.varCT v
     VarT (LICon c) -> Core.conCT c
     VarT (LIKind k) -> Core.ExpCT $ Gluon.mkLitE noSourcePos (Gluon.KindL k)
     LitT l -> internalError "translateType: Not implemented for literals"
     AppT op args -> Core.appCT (translateType op) (map translateType args)
     FunT {} -> Core.FunCT $ translateFunType lty

translateFunType :: LvLType -> Core.RCFunType
translateFunType (unLoc -> FunT param meff rng) =
  Core.arrCT (translateParamType param)
             (maybe emptyEffect translateType meff)
             (translateReturnType rng)

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

translateDecl :: LvDecl -> [(Con, Core.RCType)]
translateDecl (BoxedDecl v ty) =
  [(fromLICon v, translateType ty)]

translateDecl (DataDecl a p ty) =
  [(fromLICon a, addressType), (fromLICon p, pointerType)]

createCoreTable :: LvModule -> ConTable
createCoreTable (Module decls) =
  IntMap.fromList [(fromIdent $ conID c, ty)
                  | (c, ty) <- concatMap (translateDecl . unLoc) decls]