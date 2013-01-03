{-| Tracking of run-time type information used during lowering.

Size paramters are used when generating low-level code of data structure
accesses.   During lowering, a 'DynTypeInfo' is used to keep track of the 
in-scope size parameters.
-}

module SystemF.Datatypes.DynamicTypeInfo where

import Control.Monad

import Common.Error
import Common.MonadLogic
import SystemF.Datatypes.Util
import Type.Type
import Type.Environment
import Type.Compare
import qualified LowLevel.Build as L
import qualified LowLevel.Syntax as L

-- | For testing, supply fake size information for unknown types
testing = True

-------------------------------------------------------------------------------
-- Dynamic type information

-- | A lookup table, indexed by type.
--
--   All types in a given table have a single kind, known to the user of
--   the table.
type TypeAssocList a = [(Type, a)]

emptyTypeAssocList :: TypeAssocList a
emptyTypeAssocList = []

-- | Insert an entry into an association list
insertTypeAssocList :: Type -> a -> TypeAssocList a -> TypeAssocList a
insertTypeAssocList t x l = (t, x) : l

lookupTypeAssocList :: EvalMonad m => Type -> TypeAssocList a -> m (Maybe a)
lookupTypeAssocList t l = search l
  where
    search ((key, value) : l) =
      ifM (compareTypes t key) (return $ Just value) (search l)

    search [] =
      return Nothing

-- | Run-time type information associated with various types.
data DynTypeInfo =
  DynTypeInfo
  { -- | Size and alignment of value types
    valTypeInfo  :: TypeAssocList SizeAlign
    -- | Size and alignment of bare types
  , bareTypeInfo :: TypeAssocList SizeAlign
    -- | Integer values of type-level integers
  , intTypeInfo  :: TypeAssocList L.Val
  }

emptyTypeInfo =
  DynTypeInfo emptyTypeAssocList emptyTypeAssocList emptyTypeAssocList

insertValTypeInfo t s i =
  i {valTypeInfo = insertTypeAssocList t s $ valTypeInfo i}

insertBareTypeInfo t s i =
  i {bareTypeInfo = insertTypeAssocList t s $ bareTypeInfo i}

insertIntTypeInfo t s i =
  i {intTypeInfo = insertTypeAssocList t s $ intTypeInfo i}

-- | Lookup dynamic size and alignment information for a value type
lookupValTypeInfo :: EvalMonad m => DynTypeInfo -> Type -> m SizeAlign
lookupValTypeInfo layouts ty = do
  ml <- lookupTypeAssocList ty $ valTypeInfo layouts
  case ml of
    Just l -> return l
    Nothing -> if testing
               then return emptySizeAlign
               else internalError "lookupValTypeInfo: Not found"

-- | Lookup dynamic size and alignment information for a bare type
lookupBareTypeInfo :: EvalMonad m => DynTypeInfo -> Type -> m SizeAlign
lookupBareTypeInfo layouts ty = do
  ml <- lookupTypeAssocList ty $ bareTypeInfo layouts
  case ml of
    Just l -> return l
    Nothing -> if testing
               then return emptySizeAlign
               else internalError "lookupBareTypeInfo: Not found"

-- | Lookup dynamic value information for an integer type
lookupIntTypeInfo :: EvalMonad m => DynTypeInfo -> Type -> m L.Val
lookupIntTypeInfo layouts ty = do
  ml <- lookupTypeAssocList ty $ intTypeInfo layouts
  case ml of
    Just l -> return l
    Nothing -> if testing
               then return $ L.nativeIntV 0
               else internalError "lookupIntTypeInfo: Not found"

