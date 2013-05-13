{-|
This module gets rid of the distinctions between managed and unmanaged
pointers.  We rely on garbage collection to manage pointers properly.

Cursors are expanded into records, so record flattening should be
performed in a following step.
-}
module LowLevel.ReferenceTracking(insertReferenceTracking)
where

import Prelude hiding(mapM)

import Control.Applicative
import Data.Traversable

import Common.Error
import LowLevel.Build
import LowLevel.FreshVar
import LowLevel.Syntax
import LowLevel.CodeTypes
import Export
import Globals

-- | The reference tracking monad may create new variables
type RT a = FreshVarM a

-- | A cursor record after reference tracking has been eliminated.
--   Both fields of the cursor are pointers.
pointerCursorRecord :: StaticRecord
pointerCursorRecord =
  constStaticRecord [ PrimField PointerType
                    , PrimField PointerType
                    ]

data Cursor = Cursor { ownedRef :: !Val, interiorPtr :: !Val}

-- | Generate code to unpack a cursor.
--   Cursors should be converted to records before they're passed to this
--   function.
unpackCursor :: Val -> (Cursor -> RT Stm) -> RT Stm
unpackCursor cursor_val k = do
  owned <- newAnonymousVar (PrimType PointerType)
  interior <- newAnonymousVar (PrimType PointerType)
  let atom = UnpackA pointerCursorRecord cursor_val

  -- Pass the unpacked cursor to the continuation
  stm <- k (Cursor (VarV owned) (VarV interior))

  -- Insert an 'unpack' atom to unpack the cursor
  return $ LetE [owned, interior] atom stm

-- | Generate code to repack a cursor
packCursor :: Cursor -> (Val -> RT Stm) -> RT Stm
packCursor (Cursor owned interior) k = do
  c <- newAnonymousVar (RecordType pointerCursorRecord)
  let atom = PackA pointerCursorRecord [owned, interior]

  -- Pass the packed cursor to the continuation
  stm <- k (VarV c)

  -- Insert a 'pack' atom to pack the cursor
  return $ LetE [c] atom stm

-- | Generate code to convert any kind of pointer to a 'PointerType'.
--   Pointers and owned references are left alone.  The interior pointer
--   is extracted from a cursor.
unpackPointer :: PointerKind -> Val -> (Val -> RT Stm) -> RT Stm
unpackPointer CursorPtr  c   k = unpackCursor c $ \(Cursor _ ptr) -> k ptr
unpackPointer PointerPtr ptr k = k ptr
unpackPointer OwnedPtr   ptr k = k ptr

-------------------------------------------------------------------------------
-- * Type annotation conversion 
-- $type_annotation
-- These routines change memory-managed pointer types to unmanaged pointer
-- types.

toPointerPrimType :: PrimType -> PrimType
toPointerPrimType OwnedType = PointerType
toPointerPrimType CursorType = internalError "toPointerPrimType"
toPointerPrimType t = t

toPointerType :: ValueType -> ValueType
toPointerType (PrimType CursorType) = RecordType pointerCursorRecord
toPointerType (PrimType OwnedType) = PrimType PointerType
toPointerType (PrimType t) = PrimType t
toPointerType (RecordType rt) = RecordType $ toPointerRecordType rt

-- | Convert all owned pointers to non-owned pointers in the record type
toPointerRecordType :: StaticRecord -> StaticRecord
toPointerRecordType rec = mapRecordFieldTypes change_field rec
  where
    change_field (PrimField pt) = case toPointerType (PrimType pt)
                                  of PrimType pt' -> PrimField pt'
                                     RecordType rt' -> RecordField rt'
    change_field _ = internalError "toPointerRecordType"

-------------------------------------------------------------------------------
-- * Conversion on expressions

toPointerLit NullRefL = NullL
toPointerLit l = l

-- | Convert owned variables to pointer variables.  Leave other variables
-- unchanged.
toPointerVar :: Var -> Var
toPointerVar v = v {varType = toPointerType $ varType v}

toPointerVal :: Val -> Val
toPointerVal value =
  case value
  of VarV v -> VarV (toPointerVar v)
     LitV l -> LitV (toPointerLit l)
     _ -> internalError "toPointerVal"
       
-- | Convert global data from owned to non-owned pointers.
-- Because global data can't contain lambda expressions and can't
-- release their references, only types have to change.
toPointerData :: Val -> Val
toPointerData value =
  case value
  of VarV v -> VarV (toPointerVar v)
     RecV rt vs -> RecV (toPointerRecordType rt) (map toPointerData vs)
     LitV l -> LitV (toPointerLit l)
     _ -> internalError "toPointerData"

toPointerDataList :: [Val] -> [Val]
toPointerDataList values = map toPointerData values

-- | Convert a primitive operating on owned pointer variables to the equivalent
--   one operating on pointer variables.  If the primitive doesn't operate on 
--   owned pointers, leave it unchanged.
--   If the primitive operates on cursors, change it to operate on the
--   cursor's interior pointer.
toPointerPrim :: Prim -> [Val] -> (Atom -> RT Stm) -> RT Stm
toPointerPrim prim vs k =
  case prim
  of PrimLoad m ptr_kind ty ->
       -- Load from a simple pointer 
       let ![ptr', off'] = map toPointerData vs
       in unpackPointer ptr_kind ptr' $ \p -> 
          k $ PrimA (PrimLoad m PointerPtr (toPointerType ty)) [p, off']

     PrimStore m ptr_kind ty ->
       -- Store to a simple pointer 
       let ![ptr', off', val'] = map toPointerData vs
       in unpackPointer ptr_kind ptr' $ \p ->
          k $ PrimA (PrimStore m PointerPtr (toPointerType ty)) [p, off', val']

     PrimSelect ty -> with_new_prim $ PrimSelect (toPointerType ty)

     -- Expand pointer arithmetic involving cursors
     PrimAddP ptr_kind ->
       let ![ptr', off'] = map toPointerData vs
       in case ptr_kind
          of PointerPtr ->
               k $ PrimA (PrimAddP PointerPtr) [ptr', off']

             OwnedPtr -> do
               -- Do pointer arithmetic on the argument pointer and return a cursor
               interior' <- newAnonymousVar (PrimType PointerType)
               LetE [interior'] (PrimA (PrimAddP PointerPtr) [ptr', off']) <$> do
                 packCursor (Cursor ptr' (VarV interior')) $ \x ->
                   k $ ValA [x]
       
             CursorPtr -> do
               -- Do pointer arithmetic on the cursor's interior pointer
               interior' <- newAnonymousVar (PrimType PointerType)
               unpackCursor ptr' $ \(Cursor owned interior) ->
                 LetE [interior'] (PrimA (PrimAddP PointerPtr) [interior, off']) <$> do
                   packCursor (Cursor owned (VarV interior')) $ \x ->
                     k $ ValA [x]

     PrimSubP ptr_kind ->
       let ![ptr1, ptr2] = map toPointerData vs
       in case ptr_kind
          of PointerPtr ->
               k $ PrimA (PrimSubP PointerPtr) [ptr1, ptr2]

             CursorPtr ->
               unpackCursor ptr1 $ \(Cursor _ interior1) ->
               unpackCursor ptr2 $ \(Cursor _ interior2) ->
               k $ PrimA (PrimSubP PointerPtr) [interior1, interior2]

     -- Since owned types are being ignored, just convert these casts to moves
     PrimCastToOwned -> k $ ValA (map toPointerData vs)
     PrimCastFromOwned -> k $ ValA (map toPointerData vs)
     PrimCastFromCursor ->
       let [v] = vs
       in unpackCursor (toPointerData v) $ \(Cursor _ interior) -> 
          k $ ValA [interior]

     PrimCursorBase ->
       let [v] = vs
       in unpackCursor (toPointerData v) $ \(Cursor owned _) ->
          k $ ValA [owned]

     -- Other primops are unchanged
     _ -> with_new_prim prim
  where
    -- After choosing the new primitive operation, convert all values
    with_new_prim p = k $ PrimA p (map toPointerData vs)

toPointerAtom :: Atom -> (Atom -> RT Stm) -> RT Stm
toPointerAtom atom k =
  case atom
  of ValA vs -> k $ ValA $ toPointerDataList vs
     CallA conv v vs -> k $ CallA conv (toPointerData v) (toPointerDataList vs)
     PrimA prim vs -> toPointerPrim prim vs k
     UnpackA rec v -> k $ UnpackA (toPointerRecordType rec) (toPointerData v)

     -- Pack atoms should have been eliminated
     _ -> internalError "toPointerAtom"

toPointerStm :: Stm -> RT Stm
toPointerStm statement = 
  case statement
  of LetE vs atom stm' ->
       toPointerAtom atom $ \atom' ->
       LetE (map toPointerVar vs) atom' <$> toPointerStm stm'
     LetrecE defs stm' ->
       LetrecE <$> traverse toPointerDef defs <*> toPointerStm stm'
     SwitchE val alts ->
       SwitchE (toPointerVal val) <$> traverse toPointerBranch alts
     ReturnE atom ->
       toPointerAtom atom $ \atom' -> pure $ ReturnE atom'
     ThrowE val ->
       pure $ ThrowE (toPointerVal val)
  where
    toPointerBranch (x, s) = do
      s' <- toPointerStm s
      return (x, s')

toPointerFun :: Fun -> RT Fun
toPointerFun f = do
  body' <- toPointerStm $ funBody f
  return $ f { funParams      = map toPointerVar $ funParams f
             , funReturnTypes = map toPointerType $ funReturnTypes f
             , funBody        = body'
             }

toPointerFunctionType ftype =
  let domain = map toPointerType $ ftParamTypes ftype
      range = map toPointerType $ ftReturnTypes ftype
  in  mkFunctionType (ftConvention ftype) domain range

toPointerDef (Def v f) =
  Def (toPointerVar v) <$> toPointerFun f

toPointerDataDef (Def v (StaticData x)) =
  let dat = StaticData (toPointerData x)
  in Def (toPointerVar v) dat

toPointerImport :: Import -> RT Import
toPointerImport (ImportClosureFun ep mvalue) = do
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
  mvalue' <- traverse toPointerFun mvalue
  return $ ImportClosureFun ep' mvalue'

toPointerImport (ImportPrimFun v ft mvalue) = do
  mvalue' <- mapM toPointerFun mvalue
  return $ ImportPrimFun (toPointerVar v) (toPointerFunctionType ft) mvalue'

toPointerImport (ImportData v msdata) =
  let msdata' = 
        case msdata
        of Just (StaticData v) ->
             Just (StaticData (toPointerData v))
           Nothing -> Nothing
  in return $ ImportData (toPointerVar v) msdata'

toPointerExport :: (Var, ExportSig) -> (Var, ExportSig)
toPointerExport (v, sig) = (toPointerVar v, sig)

toPointerGlobalDef (GlobalFunDef d) = GlobalFunDef <$> toPointerDef d
toPointerGlobalDef (GlobalDataDef d) = GlobalDataDef <$> pure (toPointerDataDef d)

-------------------------------------------------------------------------------

-- | Insert explicit memory management into a module.  All memory-managed
-- pointers become unmanaged pointers.
insertReferenceTracking :: Module -> IO Module
insertReferenceTracking mod =
  withTheLLVarIdentSupply $ \var_ids -> do
    defs' <- runFreshVarM var_ids $
             mapM (traverse toPointerGlobalDef) $ moduleGlobals mod
    imports' <- runFreshVarM var_ids $
                mapM toPointerImport $ moduleImports mod
    let exports' = map toPointerExport $ moduleExports mod
    return $ mod { moduleImports = imports'
                 , moduleGlobals = defs'
                 , moduleExports = exports'}
