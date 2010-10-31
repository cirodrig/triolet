
{-# LANGUAGE FlexibleContexts, DeriveDataTypeable #-}
module LowLevel.Syntax where

import Control.Monad
import Data.Function
import Data.Maybe
import Data.Typeable

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Supply
import Gluon.Common.Label
import Export
import LowLevel.Types
import LowLevel.Record

-- | A type that may be put into a variable
data ValueType = PrimType !PrimType
               | RecordType !StaticRecord
                 deriving(Eq)

instance HasSize ValueType where
  sizeOf (PrimType pt) = sizeOf pt
  sizeOf (RecordType rt) = sizeOf rt
  alignOf (PrimType pt) = alignOf pt
  alignOf (RecordType rt) = alignOf rt

valueToPrimType :: ValueType -> PrimType
valueToPrimType (PrimType pt) = pt
valueToPrimType _ =
  internalError "Expecting a primitive type, got a record type"

-- | A comparison operation
data CmpOp = CmpEQ | CmpNE | CmpLT | CmpLE | CmpGT | CmpGE

data Prim =
    -- | @PrimCastZ from-sign to-sign size@
    -- 
    -- Change the sign of an integral value without changing its content
    PrimCastZ !Signedness !Signedness !Size
  | PrimAddZ !Signedness !Size  -- ^ Add two integers
  | PrimSubZ !Signedness !Size  -- ^ Subtract Y from X
  | PrimMulZ !Signedness !Size  -- ^ Multiply X by Y
  | PrimModZ !Signedness !Size  -- ^ Remainder (floor) of X modulo Y
  | PrimMaxZ !Signedness !Size  -- ^ Compute maximum
  | PrimCmpZ !Signedness !Size !CmpOp -- ^ Boolean compare integers
  | PrimCmpP !CmpOp                   -- ^ Boolean compare pointers
  | PrimAnd                           -- ^ Boolean and
  | PrimOr                            -- ^ Boolean or
  | PrimNot                           -- ^ Boolean negation
  | PrimAddP                    -- ^ Add a native unsigned integer to a
                                --   (owned or non-owned) pointer.  The result
                                --   is a non-owned pointer.
  | PrimLoad !ValueType         -- ^ Load a value from an (owned or non-owned) 
                                --   pointer.
  | PrimStore !ValueType        -- ^ Store a value to an (owned or non-owned) 
                                --   pointer.
  | PrimAAddZ !Signedness !Size -- ^ Atomically add the target of a pointer to
                                --   an integer.  Return the original value at
                                --   that address.
  | PrimCastToOwned             -- ^ Cast a non-owned pointer to an owned
                                --   pointer.  A new reference is returned.
  | PrimCastFromOwned           -- ^ Cast an owned pointer to a non-owned
                                --   pointer.  Consumes a reference.
  | PrimAddF !Size              -- ^ Floating-point addition
  | PrimSubF !Size              -- ^ Floating-point subtraction
  | PrimMulF !Size              -- ^ Floating-point multiplication
  | PrimModF !Size              -- ^ Floating-point modulus

data Lit =
    UnitL                       -- ^ The unit value
  | NullL                       -- ^ The NULL non-owned pointer
  | BoolL !Bool                 -- ^ A boolean
  | IntL !Signedness !Size !Integer -- ^ An integer
  | FloatL !Size !Double        -- ^ A floating-point number
    deriving(Eq)

data Var =
  Var
  { -- | An ID uniquely identifying this variable.  If two variables have
    -- the same ID, all their other fields should be equal also.
    varID :: {-# UNPACK #-} !(Ident Var)
    -- | True if this variable is visible outside the module where it is
    --   defined.  Exported variables always have a label and are global.
  , varIsExternal :: {-# UNPACK #-} !Bool
  , varName :: !(Maybe Label)
    -- | The variable's externally visible name, as it appears in object code.
    -- This is used to override the default name mangling, for example, when
    -- referencing a function that was defined in C.  If the value is Nothing,
    -- then the variable's name is used to generate an externally visible name.
    --
    -- In variables that are not externally visible, this field must be
    -- Nothing.
  , varExternalName :: !(Maybe String)
  , varType :: ValueType
  }

instance Show Var where
  show v =
    let name = maybe "_" showLabel $ varName v
    in name ++ "'" ++ show (fromIdent $ varID v)

instance Eq Var where
  (==) = (==) `on` varID

instance Ord Var where
  compare = compare `on` varID

type ParamVar = Var
type ImportVar = Var

-- | A value
data Val =
    VarV Var
  | RecV !StaticRecord [Val]
  | LitV !Lit
  | LamV Fun

valType :: Val -> ValueType
valType (VarV v) = varType v
valType (RecV r _) = RecordType r
valType (LitV l) = PrimType $ litType l
valType (LamV f) = PrimType OwnedType

-- | An atomic operation.  Some non-atomic operations are included here.
-- This is modeled after ANF, but isn't truly ANF since expressions can be 
-- recursive.
data Atom =
    -- | Return some values
    ValA [Val]
    -- | Call a closure-based function 
    -- (possibly with the wrong number of arguments).
    -- The function must be an owned pointer.
  | CallA Val [Val]
    -- | Call a primitive function, using the C calling convention extended
    -- with support for multiple return values.
    -- Unlike closure-based calls, this call must have exactly the right
    -- number of arguments.
    -- The function must be a non-owned pointer.
  | PrimCallA Val [Val]
    -- | Perform a primitive operation (such as 'add' or 'load').
    --   Must have exactly the right number of arguments.
  | PrimA !Prim [Val]
    -- | Pack a statically typed record value.
  | PackA !StaticRecord [Val]
    -- | Unpack a statically typed record value.
  | UnpackA !StaticRecord Val

-- | A statement.  Statements may have side effects.
data Stm =
    -- | Bind an atom's result to temporary variables
    LetE [ParamVar] Atom Stm
    -- | Define local functions
  | LetrecE [FunDef] Stm
    -- | Conditional branch.  Inspect the value, then execute an alternative.
  | SwitchE Val [Alt]
    -- | Produce a value
  | ReturnE Atom

data Fun =
  Fun 
  { funIsPrim :: !Bool 
  , funParams :: [ParamVar] 
  , funReturnTypes :: [ValueType] 
  , funBody :: Stm
  }

isPrimFun, isClosureFun :: Fun -> Bool
isPrimFun = funIsPrim
isClosureFun f = not (isPrimFun f)

closureFun :: [ParamVar] -> [ValueType] -> Stm -> Fun
closureFun = Fun False

primFun :: [ParamVar] -> [ValueType] -> Stm -> Fun
primFun = Fun True

type Alt = (Lit, Stm)

-- | A function definition
data FunDef = FunDef !ParamVar Fun

funDefiniendum :: FunDef -> Var
funDefiniendum (FunDef v _) = v

funDefiniens :: FunDef -> Fun
funDefiniens (FunDef _ f) = f

-- | A static data definition
data DataDef = DataDef !ParamVar !StaticRecord ![Val]

dataDefiniendum :: DataDef -> Var
dataDefiniendum (DataDef v _ _) = v

data Module =
  Module 
  { moduleImports :: [ImportVar] -- ^ Imported, externally defined variables
  , moduleFunctions :: [FunDef]  -- ^ Function definitions
  , moduleData :: [DataDef]      -- ^ Global data definitions
  , moduleExports :: [(Var, ExportSig)] -- ^ Exported functions and their
                                        --   externally visible types
  }
  deriving(Typeable)

-- | True if the module exports something out of the Pyon language
moduleHasExports :: Module -> Bool
moduleHasExports m = not $ null $ moduleExports m

-------------------------------------------------------------------------------

-- | A primitive or closure function type.
data FunctionType =
  FunctionType {-# UNPACK #-}!Bool ![ValueType] ![ValueType]

primFunctionType :: [ValueType] -> [ValueType] -> FunctionType
primFunctionType params returns = FunctionType True params returns

closureFunctionType :: [ValueType] -> [ValueType] -> FunctionType
closureFunctionType params returns = FunctionType False params returns

ftIsPrim, ftIsClosure :: FunctionType -> Bool
ftIsPrim (FunctionType b _ _) = b
ftIsClosure t = not (ftIsPrim t)

ftParamTypes :: FunctionType -> [ValueType]
ftParamTypes (FunctionType _ ps _) = ps

ftReturnTypes :: FunctionType -> [ValueType]
ftReturnTypes (FunctionType _ _ rs) = rs

-- | The global objects that make up a Pyon function.  Objects that can be
--   dynamically allocated (specifically, closure and captured variable
--   records) are not included here.
data EntryPoints =
  EntryPoints
  { _epType         :: {-# UNPACK #-} !FunctionType
  , _epArity        :: {-# UNPACK #-} !Int
  , _epDirectEntry  :: !Var
  , _epExactEntry   :: !Var
  , _epInexactEntry :: !Var
  , _epDeallocEntry :: !(Maybe Var)      -- Nothing if never deallocated
  , _epInfoTable    :: !Var
  }

-- | Get the type of a function
entryPointsType :: EntryPoints -> FunctionType
entryPointsType = _epType

-- | Get the arity of a function.  This is the number of parameters that 
--   direct and exact calls must pass.
functionArity :: EntryPoints -> Int
functionArity = _epArity

-- | Get the direct entry point of a function
directEntry :: EntryPoints -> Var
directEntry = _epDirectEntry

-- | Get the exact entry point of a function
exactEntry :: EntryPoints -> Var
exactEntry = _epExactEntry

-- | Get the inexact entry point of a function
inexactEntry :: EntryPoints -> Var
inexactEntry = _epInexactEntry

-- | Get the deallocation entry point of a function.
--
-- The deallocation entry point is Nothing if the function cannot be
-- deallocated, which is true for global functions.
deallocEntry :: EntryPoints -> Maybe Var
deallocEntry = _epDeallocEntry

-- | Get  the info table of a function
infoTableEntry :: EntryPoints -> Var
infoTableEntry = _epInfoTable

-- | Create a new internal variable
newVar :: Supplies m (Ident Var) =>
          Maybe Label -> Maybe String -> ValueType -> m Var
newVar name ext_name ty = do
  ident <- fresh
  return $ Var { varID = ident
               , varIsExternal = False
               , varName = name
               , varExternalName = ext_name
               , varType = ty
               }

-- | Create a new variable with no name
newAnonymousVar :: Supplies m (Ident Var) => ValueType -> m Var
newAnonymousVar ty = newVar Nothing Nothing ty

-- | Create a new externally defined variable
newExternalVar :: Supplies m (Ident Var) =>
                  Label -> Maybe String -> ValueType -> m Var
newExternalVar name ext_name ty = do
  ident <- fresh
  return $ Var { varID = ident
               , varIsExternal = True
               , varName = Just name
               , varExternalName = ext_name
               , varType = ty
               }

-- | Get the type of a literal
litType :: Lit -> PrimType
litType UnitL = UnitType
litType NullL = PointerType
litType (BoolL _) = BoolType
litType (IntL sgn sz _) = IntType sgn sz
litType (FloatL sz _) = FloatType sz

funType :: Fun -> FunctionType
funType f =
  FunctionType (funIsPrim f) (map varType $ funParams f) (funReturnTypes f)
  