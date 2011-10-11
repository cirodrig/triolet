{-|
This module is responsible for inserting explicit memory management code
that decides when to deallocate memory.  There's no implementation at
present; memory just leaks.
-}
module LowLevel.ReferenceCounting(insertReferenceCounting)
where

import Common.Error
import LowLevel.Syntax
import LowLevel.CodeTypes
import Export
  
-------------------------------------------------------------------------------
-- * Type annotation conversion 
-- $type_annotation
-- These routines change memory-managed pointer types to unmanaged pointer
-- types.

toPointerPrimType :: PrimType -> PrimType
toPointerPrimType OwnedType = PointerType
toPointerPrimType t = t

toPointerType :: ValueType -> ValueType
toPointerType (PrimType pt) = PrimType $ toPointerPrimType pt
toPointerType t = t

-- | Convert all owned pointers to non-owned pointers in the record type
toPointerRecordType :: StaticRecord -> StaticRecord
toPointerRecordType rec = mapRecordFieldTypes change_field rec
  where
    change_field (PrimField t) = PrimField $ toPointerPrimType t
    change_field _ = internalError "toPointerRecordType"

isOwnedVar :: Var -> Bool
isOwnedVar v =
  case varType v
  of PrimType OwnedType -> True
     _ -> False

-------------------------------------------------------------------------------
-- * Conversion on expressions

-- | Convert owned variables to pointer variables.  Leave other variables
-- unchanged.
toPointerVar :: Var -> Var
toPointerVar v =
  case varType v
  of PrimType t -> v {varType = PrimType $ toPointerPrimType t}
     RecordType r -> v {varType = RecordType $ toPointerRecordType r}

toPointerVal :: Val -> Val
toPointerVal value =
  case value
  of VarV v -> VarV (toPointerVar v)
     LitV l -> value
     _ -> internalError "toPointerVal"
       

-- | Convert a primitive operating on owned pointer variables to the equivalent
-- one operating on pointer variables.  If the primitive doesn't operate on 
-- owned pointers, leave it unchanged.
toPointerPrim :: Prim -> Prim
toPointerPrim prim =
  case prim
  of PrimLoad m (PrimType OwnedType) -> PrimLoad m (PrimType PointerType)
     PrimStore m (PrimType OwnedType) -> PrimStore m (PrimType PointerType)
     PrimCastToOwned -> internalError "toPointerPrim"
     PrimCastFromOwned -> internalError "toPointerPrim"
     _ -> prim

-- | Convert global data from owned to non-owned pointers.
-- Because global data can't contain lambda expressions and can't
-- release their references, only types have to change.
toPointerData :: Val -> Val
toPointerData value =
  case value
  of VarV v -> VarV (toPointerVar v)
     RecV rt vs -> RecV (toPointerRecordType rt) (map toPointerData vs)
     LitV _ -> value
     _ -> internalError "toPointerData"

toPointerDataList :: [Val] -> [Val]
toPointerDataList values = map toPointerData values

toPointerAtom :: Atom -> Atom
toPointerAtom atom =
  case atom
  of ValA vs -> ValA $ toPointerDataList vs
     CallA conv v vs -> CallA conv (toPointerData v) (toPointerDataList vs)
     
     -- Since owned types are being ignored, just convert these casts to moves
     PrimA PrimCastToOwned [v] -> ValA [toPointerData v]
     PrimA PrimCastFromOwned [v] -> ValA [toPointerData v]
     PrimA prim vs -> PrimA (toPointerPrim prim) (toPointerDataList vs)
     UnpackA rec v -> UnpackA (toPointerRecordType rec) (toPointerData v)
     -- Pack atoms should have been eliminated
     _ -> internalError "toPointerAtom"

toPointerStm :: Stm -> Stm
toPointerStm statement = 
  case statement
  of LetE vs atom stm' ->
       LetE (map toPointerVar vs) (toPointerAtom atom) (toPointerStm stm')
     LetrecE defs stm' ->
       LetrecE (fmap toPointerDef defs) (toPointerStm stm')
     SwitchE val alts ->
       SwitchE (toPointerVal val) [(x, toPointerStm s) | (x, s) <- alts]
     ReturnE atom ->
       ReturnE (toPointerAtom atom)
     ThrowE val ->
       ThrowE (toPointerVal val)

toPointerFun :: Fun -> Fun
toPointerFun f =
  f { funParams      = map toPointerVar $ funParams f
    , funReturnTypes = map toPointerType $ funReturnTypes f
    , funBody        = toPointerStm $ funBody f
    }

toPointerFunctionType ftype =
  let domain = map toPointerType $ ftParamTypes ftype
      range = map toPointerType $ ftReturnTypes ftype
  in  mkFunctionType (ftConvention ftype) domain range

toPointerDef (Def v f) =
  Def (toPointerVar v) (toPointerFun f)

toPointerDataDef (Def v (StaticData x)) =
  let dat = StaticData (toPointerData x)
  in Def (toPointerVar v) dat

toPointerImport :: Import -> Import
toPointerImport (ImportClosureFun ep mvalue) =
  let ep' =
        EntryPoints
        (toPointerFunctionType $ entryPointsType ep)
        (functionArity ep)
        (toPointerVar $ directEntry ep)
        (fmap toPointerVar $ vectorEntry ep)
        (toPointerVar $ exactEntry ep)
        (toPointerVar $ inexactEntry ep)
        (toPointerVar $ infoTableEntry ep)
        (toPointerVar $ globalClosure ep)
      mvalue' = fmap toPointerFun mvalue
  in ImportClosureFun ep' mvalue'

toPointerImport (ImportPrimFun v ft mvalue) =
  ImportPrimFun (toPointerVar v) (toPointerFunctionType ft) (fmap toPointerFun mvalue)

toPointerImport (ImportData v msdata) =
  let msdata' = 
        case msdata
        of Just (StaticData v) ->
             Just (StaticData (toPointerData v))
           Nothing -> Nothing
  in ImportData (toPointerVar v) msdata'

toPointerExport :: (Var, ExportSig) -> (Var, ExportSig)
toPointerExport (v, sig) = (toPointerVar v, sig)

toPointerGlobalDef (GlobalFunDef d) = GlobalFunDef $ toPointerDef d
toPointerGlobalDef (GlobalDataDef d) = GlobalDataDef $ toPointerDataDef d

-------------------------------------------------------------------------------

-- | Insert explicit memory management into a module.  All memory-managed
-- pointers become unmanaged pointers.
insertReferenceCounting :: Module -> IO Module
insertReferenceCounting mod =
  let defs' = map (fmap toPointerGlobalDef) $ moduleGlobals mod
      imports' = map toPointerImport $ moduleImports mod
      exports' = map toPointerExport $ moduleExports mod
  in return $ mod { moduleImports = imports'
                  , moduleGlobals = defs'
                  , moduleExports = exports'}
