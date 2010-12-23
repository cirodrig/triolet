
{-# LANGUAGE FlexibleContexts, DeriveDataTypeable #-}
module LowLevel.Syntax where

import Control.Monad
import Data.Function
import Data.Maybe
import Data.Monoid
import Data.Typeable

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Supply
import Export
import LowLevel.CodeTypes
import LowLevel.Label

-- | Attached to function definitions to indicate how many places in the 
--   code contain a reference to the function.
--
--   'ManyUses' represents more than one use, or an unknown number of uses.
data Uses = ZeroUses | OneUse | ManyUses
          deriving(Eq, Enum, Bounded)

instance Monoid Uses where
  mempty = ZeroUses
  mappend ZeroUses x = x
  mappend x ZeroUses = x
  mappend _ _ = ManyUses

-- | A measure of how much code a function contains.  Used to control 
--   inlining.  An unknown code size is represented by -1.
newtype CodeSize = CodeSize Int

unknownCodeSize :: CodeSize
unknownCodeSize = CodeSize (-1)

codeSize :: Int -> CodeSize
codeSize n | n < 0     = internalError "codeSize: Invalid size"
           | otherwise = CodeSize n

fromCodeSize :: CodeSize -> Maybe Int
fromCodeSize (CodeSize n) | n < 0     = Nothing
                          | otherwise = Just n

-- | A comparison operation
data CmpOp = CmpEQ | CmpNE | CmpLT | CmpLE | CmpGT | CmpGE
           deriving(Eq, Ord, Bounded, Enum)

data Prim =
    -- | @PrimCastZ from-sign to-sign size@
    -- 
    -- Change the sign of an integral value without changing its content
    PrimCastZ !Signedness !Signedness !Size
    -- | @PrimExtendZ sign from-size to-size@
    --
    -- Sign-extend, zero-extend, or truncate an integral value
  | PrimExtendZ !Signedness !Size !Size
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
    -- | @PrimLoad mutability type base offset@ 
    -- 
    -- Load a value from a (managed or unmanaged) pointer at some byte offset.
    -- Before the record flattening pass, the loaded value may have record
    -- type; afterward, it may only have primitive type.
    --
    -- The mutability flag may be 'Constant' if the loaded memory is known to
    -- be constant (possibly initialized by a single store operation).
    -- Otherwise, it should be 'Mutable'.  Incorrect use of 'Constant' may
    -- cause incorrect optimizations.
  | PrimLoad !Mutability !ValueType
    -- | @PrimStore mutability type base offset value@
    --
    -- Store a value to a (managed or unmanaged) pointer at some byte offset.
    -- Before the record flattening pass, the stored value may have record
    -- type; afterward, it may only have primitive type.
    --
    -- The mutability flag may be 'Constant' if the stored memory is known to
    -- be constant.  In that case, the memory must not be written by any other
    -- instruction.  Otherwise, it should be 'Mutable'.
    -- Incorrect use of 'Constant' may cause incorrect optimizations.
  | PrimStore !Mutability !ValueType
  | PrimAAddZ !Signedness !Size -- ^ Atomically add the target of a pointer to
                                --   an integer.  Return the original value at
                                --   that address.
  | PrimCastToOwned             -- ^ Cast a non-owned pointer to an owned
                                --   pointer.  A new reference is returned.
  | PrimCastFromOwned           -- ^ Cast an owned pointer to a non-owned
                                --   pointer.  Consumes a reference.
  | PrimGetFrameP               -- ^ Get the current function's frame pointer,
                                --   pointing to the function's local data.
                                --   Returns a pointer.  If there's no frame,
                                --   NULL is returned.
    -- | @PrimCastZToF from-size to-size@
    -- Cast a signed integral value to a floating-point value
  | PrimCastZToF !Size !Size
    -- | @PrimCastFToZ from-size to-size@
    -- Cast a floating-point value to a signed integral value
  | PrimCastFToZ !Size !Size
  -- - | PrimCastToFloat             -- ^ Cast to a floating-point value
  | PrimAddF !Size              -- ^ Floating-point addition
  | PrimSubF !Size              -- ^ Floating-point subtraction
  | PrimMulF !Size              -- ^ Floating-point multiplication
  | PrimModF !Size              -- ^ Floating-point modulus

primReturnType :: Prim -> [ValueType]
primReturnType prim =
  case prim
  of PrimCastZ _ to_sgn to_sz -> int to_sgn to_sz
     PrimAddZ sgn sz          -> int sgn sz
     PrimSubZ sgn sz          -> int sgn sz
     PrimMulZ sgn sz          -> int sgn sz
     PrimModZ sgn sz          -> int sgn sz
     PrimMaxZ sgn sz          -> int sgn sz
     PrimCmpZ _ _ _           -> bool
     PrimCmpP _               -> bool
     PrimAnd                  -> bool
     PrimOr                   -> bool
     PrimNot                  -> bool
     PrimAddP                 -> pointer
     PrimLoad _ t             -> [t]
     PrimStore _ _            -> []
     PrimAAddZ sgn sz         -> int sgn sz
     PrimCastToOwned          -> [PrimType OwnedType]
     PrimCastFromOwned        -> pointer
     PrimCastZToF _ sz        -> float sz
     PrimCastFToZ _ sz        -> int Signed sz
     PrimAddF sz              -> float sz
     PrimSubF sz              -> float sz
     PrimMulF sz              -> float sz
     PrimModF sz              -> float sz
  where
    int sgn sz = [PrimType $ IntType sgn sz]
    float sz = [PrimType $ FloatType sz]
    bool = [PrimType BoolType]
    pointer = [PrimType PointerType]

data Lit =
    UnitL                       -- ^ The unit value
  | NullL                       -- ^ The NULL non-owned pointer
  | BoolL !Bool                 -- ^ A boolean
  | IntL !Signedness !Size !Integer -- ^ An integer
  | FloatL !Size !Double        -- ^ A floating-point number
    deriving(Eq, Ord)

-- | Throw an error if the literal is invalid
checkLit :: Lit -> ()
checkLit (IntL sgn sz n)
  | isRepresentableInt sgn sz n =
      internalError "checkLit: Integer literal out of range"
  | otherwise = ()
checkLit _ = ()

-- | Create an integer literal holding the given value
intL :: Signedness -> Size -> Integer -> Lit
intL sgn sz n
  | not $ isRepresentableInt sgn sz n =
      internalError "intL: Integer literal out of range"
  | otherwise = IntL sgn sz n

-- | Create an integer literal holding the given value modulo the
--   integer's representable range.  In other words, truncate the bits
--   that don't fit in the literal. 
coercedIntL :: Signedness -> Size -> Integer -> Lit
coercedIntL sgn sz n = IntL sgn sz (coerceToRepresentableInt sgn sz n)

data Var =
  Var
  { -- | An ID uniquely identifying this variable.  If two variables have
    -- the same ID, all their other fields should be equal also.
    varID :: {-# UNPACK #-} !(Ident Var)
    -- | True if this variable is visible outside the module where it is
    --   defined.  Exported variables are global.
  , varIsExternal :: {-# UNPACK #-} !Bool
    -- | The variable's name.  If the variable is externally visible, it must
    --   have a name.
  , varName :: !(Maybe Label)
    -- | The variable's type.
  , varType :: ValueType
  }

-- | Get a variable's mangled name.
--
-- An externally visible variable's mangled name consists of just its label.
-- Its ID is not part of its name, since IDs are not preserved across
-- modules.
--
-- Internal variables' mangled names consist of the variable's label and ID.
-- If the variable doesn't have a label, it consists of a single letter and
-- the variable's ID.
mangledVarName :: Bool -> Var -> String
mangledVarName is_local v
  | varIsExternal v =
      case varName v
      of Just lab -> mangleLabel lab -- Mangle name, but don't add ID
         Nothing -> internalError $ "mangledVarName: External variables " ++
                                    "must have a label"
  | otherwise =
        case varName v
        of Just lab
             | is_local  -> mangleModuleScopeLabel lab ++ "_" ++ mangled_id
             | otherwise -> mangleLabel lab ++ "_" ++ mangled_id
           Nothing  -> type_leader (varType v) ++ mangled_id
  where
    mangled_id = show $ fromIdent $ varID v

    type_leader (PrimType t) =
      case t
      of PointerType -> "v_"
         OwnedType -> "v_"
         BoolType -> "b_"
         IntType Signed _ -> "i_"
         IntType Unsigned _ -> "u_"
         FloatType _ -> "f_"

    type_leader (RecordType _) = "r_"

instance Show Var where
  show v =
    let name = maybe "_" (either id showLocalID . labelLocalName) $ varName v
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
    -- | Call a function using the given calling convention. 
    --
    -- If 'ClosureCall', call a closure-based function.  The function must 
    -- be an owned pointer.  The call may have a different number of arguments
    -- than the callee actually takes.
    --
    -- If 'PrimCall', call a function directly.  The function must be a
    -- non-owned pointer.  The number of arguments must match what the function
    -- expects.
  | CallA !CallConvention Val [Val]
    -- | Perform a primitive operation (such as 'add' or 'load').
    --   Must have exactly the right number of arguments.
  | PrimA !Prim [Val]
    -- | Pack a statically typed record value.
    --
    -- This atom should only appear before record flattening.
  | PackA !StaticRecord [Val]
    -- | Unpack a statically typed record value.
    --
    -- After record flattening, this atom should only appear with a 'VarV'
    -- as its RHS.
  | UnpackA !StaticRecord Val

closureCallA = CallA ClosureCall
primCallA = CallA PrimCall

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
  { -- | The function's calling convention
    funConvention  :: !CallConvention
    -- | The function's code size, computed by DCE
  , funSize        :: {-# UNPACK #-}!CodeSize
    -- | How many times this function is referenced, computed by DCE
  , funUses        :: !Uses
    -- | Whether user requested to inline this function
  , funInlineRequest :: {-# UNPACK #-}!Bool
    -- | The number of bytes of stack data used for local data.
    --   If zero, no bytes are reserved and the local data are can't be
    --   accessed.  Only top-level functions may have a nonzero frame size.
  , funFrameSize   :: {-# UNPACK #-}!Int
  , funParams      :: [ParamVar] 
  , funReturnTypes :: [ValueType] 
  , funBody        :: Stm
  }

isPrimFun, isClosureFun :: Fun -> Bool
isPrimFun f = funConvention f == PrimCall
isClosureFun f = funConvention f == ClosureCall

setFunSize :: CodeSize -> Fun -> Fun
setFunSize sz f = f {funSize = sz}

setFunUses :: Uses -> Fun -> Fun
setFunUses u f = f {funUses = u}

mkFun :: CallConvention -> Bool -> Int -> [ParamVar] -> [ValueType] -> Stm
      -> Fun
mkFun cc inl_req frame_size params returns body =
  Fun { funConvention  = cc
      , funSize        = unknownCodeSize
      , funUses        = ManyUses
      , funInlineRequest = inl_req
      , funFrameSize   = frame_size
      , funParams      = params
      , funReturnTypes = returns
      , funBody        = body}

closureFun :: [ParamVar] -> [ValueType] -> Stm -> Fun
closureFun params returns body =
  mkFun ClosureCall False 0 params returns body

primFun :: [ParamVar] -> [ValueType] -> Stm -> Fun
primFun params returns body =
  mkFun PrimCall False 0 params returns body

type Alt = (Lit, Stm)

-- | A piece of static data
data StaticData = StaticData !StaticRecord ![Val]

data Def a = Def {definiendum :: !ParamVar, definiens :: a}

-- | A function definition
type FunDef = Def Fun

-- | A static data definition
type DataDef = Def StaticData

data GlobalDef = GlobalFunDef FunDef
               | GlobalDataDef DataDef

globalDefiniendum :: GlobalDef -> Var
globalDefiniendum (GlobalFunDef d) = definiendum d
globalDefiniendum (GlobalDataDef d) = definiendum d

partitionGlobalDefs :: [GlobalDef] -> ([FunDef], [DataDef])
partitionGlobalDefs ds = part id id ds
  where
    part fhead dhead (GlobalFunDef fd:ds)  = part (fhead . (fd:)) dhead ds 
    part fhead dhead (GlobalDataDef dd:ds) = part fhead (dhead . (dd:)) ds 
    part fhead dhead []                    = (fhead [], dhead [])

-- | An imported symbol
data Import =
    -- | A global function
    ImportClosureFun
    { importEntryPoints :: EntryPoints
      -- | The function's value.  The value is present if the function was
      -- deemed suitable for inlining.  The value is from before closure
      -- conversion.
    , importFunction :: !(Maybe Fun)
    }
    -- | A global procedure
  | ImportPrimFun
    { _importVar :: !ParamVar
    , importFunType :: !FunctionType
      -- | The function's value.  The value is present if the function was
      -- deemed suitable for inlining.  The value is from before closure
      -- conversion.
    , importFunction :: !(Maybe Fun)
    }
    -- | A global constant
  | ImportData
    { _importVar :: !ParamVar
      -- | The imported value's fields.  A field is present if it's deemed
      --   suitable for inlining.  The value is from before closure conversion.
    , importValue :: !(Maybe StaticData)
    }

clearImportDefinition :: Import -> Import
clearImportDefinition (ImportClosureFun ep _) = ImportClosureFun ep Nothing
clearImportDefinition (ImportPrimFun v ty _) = ImportPrimFun v ty Nothing
clearImportDefinition (ImportData v _) = ImportData v Nothing

-- | Get the variable defined by an import statement.
--   In the case of a closure function, which can define multiple variables,
--   this returns the global closure.  The global closure is the only variable
--   that can be referenced before closure conversion.
importVar :: Import -> Var
importVar impent =
  case impent
  of ImportClosureFun {importEntryPoints = entry_points} ->
       case globalClosure entry_points
       of Just v -> v
          Nothing -> internalError "importVar"
     ImportPrimFun {_importVar = v} -> v
     ImportData {_importVar = v} -> v

data Module =
  Module 
  { moduleModuleName :: !ModuleName
  , moduleNameSupply :: !(Supply LocalID)
  , moduleImports :: [Import]    -- ^ Imported, externally defined variables
  , moduleGlobals :: [GlobalDef] -- ^ Global definitions
  , moduleExports :: [(Var, ExportSig)] -- ^ Exported functions and their
                                        --   externally visible types
  }
  deriving(Typeable)

-- | True if the module exports something out of the Pyon language
moduleHasExports :: Module -> Bool
moduleHasExports m = not $ null $ moduleExports m

-- | Remove definitions of imported functions
clearImportedFunctionDefinitions :: Module -> Module
clearImportedFunctionDefinitions mod =
  mod {moduleImports = map clear_function_def $ moduleImports mod}
  where
    clear_function_def (ImportClosureFun ep _) = ImportClosureFun ep Nothing
    clear_function_def (ImportPrimFun v ty _) = ImportPrimFun v ty Nothing
    clear_function_def def@(ImportData _ _) = def

-- | Remove definitions of all imported things
clearImportedDefinitions :: Module -> Module
clearImportedDefinitions mod =
  mod {moduleImports = map clearImportDefinition $ moduleImports mod}

-------------------------------------------------------------------------------

-- | The global objects that make up a Pyon function.  Objects that can be
--   dynamically allocated (specifically, closure and captured variable
--   records) are not included here.
data EntryPoints =
  EntryPoints
  { _epType          :: {-# UNPACK #-} !FunctionType
  , _epArity         :: {-# UNPACK #-} !Int
  , _epDirectEntry   :: !Var
  , _epExactEntry    :: !Var
  , _epInexactEntry  :: !Var
  , _epDeallocEntry  :: !(Maybe Var)      -- Nothing if never deallocated
  , _epInfoTable     :: !Var
  , _epGlobalClosure :: !(Maybe Var) -- Only for global functions
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

-- | Get the info table of a function
infoTableEntry :: EntryPoints -> Var
infoTableEntry = _epInfoTable

-- | Get the global closure of a function.
-- Only global functions have a global closure.
globalClosure :: EntryPoints -> Maybe Var
globalClosure = _epGlobalClosure

-- | Assign the global closure of a function.  This function is to assist in  
--   renaming entry points.  There must already be a global closure.
setGlobalClosure :: Var -> EntryPoints -> EntryPoints
setGlobalClosure new_c ep
  | isNothing (globalClosure ep) =
      internalError "setGlobalClosure: No global closure"
  | otherwise = ep {_epGlobalClosure = Just new_c}

-- | All variables referenced by an 'EntryPoints'.
entryPointsVars :: EntryPoints -> [Var]
entryPointsVars ep =
  _epDirectEntry ep :
  _epExactEntry ep :
  _epInexactEntry ep :
  maybe id (:) (_epDeallocEntry ep) (
  _epInfoTable ep :
  maybeToList (_epGlobalClosure ep))

-- | Create a new internal variable
newVar :: Supplies m (Ident Var) => Maybe Label -> ValueType -> m Var
newVar name ty = do
  ident <- fresh
  return $ Var { varID = ident
               , varIsExternal = False
               , varName = name
               , varType = ty
               }

-- | Create a new variable with no name
newAnonymousVar :: Supplies m (Ident Var) => ValueType -> m Var
newAnonymousVar ty = newVar Nothing ty

-- | Create a new externally defined variable
newExternalVar :: Supplies m (Ident Var) =>
                  Label -> ValueType -> m Var
newExternalVar name ty = do
  ident <- fresh
  return $ Var { varID = ident
               , varIsExternal = True
               , varName = Just name
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
  mkFunctionType (funConvention f) (map varType $ funParams f) (funReturnTypes f)
  