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
--
--   Parameterized over the type 'size' of size information and 'int' of
--   integer values.  These are either core expressions or low-level values.
data DynTypeInfo val bare int =
  DynTypeInfo
  { -- | Size and alignment of value types
    valTypeInfo  :: TypeAssocList val
    -- | Size and alignment of bare types
  , bareTypeInfo :: TypeAssocList bare
    -- | Integer values of type-level integers
  , intTypeInfo  :: TypeAssocList int
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
lookupValTypeInfo :: (EvalMonad m) =>
                     DynTypeInfo val bare int -> Type -> m (Maybe val)
lookupValTypeInfo layouts ty = lookupTypeAssocList ty $ valTypeInfo layouts

lookupValTypeInfo' :: (EvalMonad m) =>
                     DynTypeInfo val bare int -> Type -> m val
lookupValTypeInfo' layouts ty = lookupValTypeInfo layouts ty >>= check
  where
    check (Just l) = return l
    check Nothing  = internalError "lookupValTypeInfo: Not found"

-- | Lookup dynamic size and alignment information for a bare type
lookupBareTypeInfo :: (EvalMonad m) =>
                      DynTypeInfo val bare int -> Type -> m (Maybe bare)
lookupBareTypeInfo layouts ty = lookupTypeAssocList ty $ bareTypeInfo layouts

lookupBareTypeInfo' :: (EvalMonad m) =>
                       DynTypeInfo val bare int -> Type -> m bare
lookupBareTypeInfo' layouts ty = lookupBareTypeInfo layouts ty >>= check
  where
    check (Just l) = return l
    check Nothing  = internalError "lookupBareTypeInfo': Not found"

-- | Lookup dynamic value information for an integer type
lookupIntTypeInfo :: (EvalMonad m) =>
                     DynTypeInfo val bare int -> Type -> m (Maybe int)
lookupIntTypeInfo layouts ty = lookupTypeAssocList ty $ intTypeInfo layouts

lookupIntTypeInfo' :: (EvalMonad m) =>
                      DynTypeInfo val bare int -> Type -> m int
lookupIntTypeInfo' layouts ty = lookupIntTypeInfo layouts ty >>= check
  where
    check (Just l) = return l
    check Nothing  = internalError $ "lookupIntTypeInfo: Not found: " ++ show (pprType ty)
