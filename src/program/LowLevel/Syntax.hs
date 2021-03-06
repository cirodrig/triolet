
{-# LANGUAGE FlexibleContexts, DeriveDataTypeable #-}
module LowLevel.Syntax where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Monad hiding(mapM)
import Data.Function
import Data.Foldable(Foldable(..))
import Data.Traversable(Traversable(..))
import Data.Maybe
import Data.Monoid
import Data.Typeable

import Common.Error
import Common.Identifier
import Common.Supply
import Common.Label
import Export
import LowLevel.CodeTypes

-- | Create a dynamic field.
--
-- This function is here rather than in "LowLevel.Records" 
-- due to module dependences.
mkDynamicField :: Val -> Mutability -> DynamicFieldType -> DynamicField
mkDynamicField offset mutable field_type
  | valType offset /= PrimType nativeIntType =
      internalError "mkDynamicField: Offset has wrong type"
  | otherwise = mkField' offset mutable field_type

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

-- | Add two code sizes.  If either argument is an unknown size,
--   the result is an unknown size.
addCodeSize :: CodeSize -> CodeSize -> CodeSize
infixl 4 `addCodeSize`
addCodeSize (CodeSize s1) (CodeSize s2) =
  CodeSize $ if s1 < 0 || s2 < 0 then -1 else s1 + s2

fromCodeSize :: CodeSize -> Maybe Int
fromCodeSize (CodeSize n) | n < 0     = Nothing
                          | otherwise = Just n

-- | Code size forms a monoid under addition
instance Monoid CodeSize where
  mempty = codeSize 0
  mappend = addCodeSize

-- | A comparison operation
data CmpOp = CmpEQ | CmpNE | CmpLT | CmpLE | CmpGT | CmpGE
           deriving(Eq, Ord, Bounded, Enum)

-- | A floating-point rounding mode
data RoundMode = Floor | Ceiling | Truncate | Nearest
               deriving (Eq, Ord, Bounded, Enum)

-- | An intrinsic floating-point unary operation
data UnaryFPIntrinsic =
    ExpI | LogI | SqrtI | SinI | CosI | TanI
    deriving (Eq, Ord, Bounded, Enum)

-- | A pointer kind; subset of 'PrimType'.
data PointerKind = OwnedPtr | PointerPtr | CursorPtr
                 deriving(Eq, Ord, Bounded, Enum) 

pointerKind OwnedType = OwnedPtr
pointerKind PointerType = PointerPtr
pointerKind CursorType = CursorPtr

fromPointerKind OwnedPtr = OwnedType
fromPointerKind PointerPtr = PointerType
fromPointerKind CursorPtr = CursorType

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
  | PrimDivZ !Signedness !Size  -- ^ Divide (floor) X by Y
  | PrimMaxZ !Signedness !Size  -- ^ Compute maximum
  | PrimMinZ !Signedness !Size  -- ^ Compute minimum
  | PrimAndZ !Signedness !Size  -- ^ Bitwise and
  | PrimOrZ !Signedness !Size   -- ^ Bitwise or
  | PrimXorZ !Signedness !Size  -- ^ Bitwise xor
  | PrimComplZ !Signedness !Size -- ^ Bitwise complement
  | PrimShiftL !Signedness !Size      -- ^ Shift left by a signed int value
  | PrimShiftR !Signedness !Size      -- ^ Shift right by a signed int value
  | PrimCmpZ !Signedness !Size !CmpOp -- ^ Boolean compare integers
  | PrimCmpP !CmpOp                   -- ^ Boolean compare pointers or
                                      --   owned references
  | PrimSelect !ValueType             -- ^ Boolean value select
  | PrimAnd                           -- ^ Boolean and
  | PrimOr                            -- ^ Boolean or
  | PrimNot                           -- ^ Boolean negation
  | PrimAddP !PointerKind       -- ^ Add a native unsigned integer to a
                                --   pointer.  The argument gives the type of
                                --   the argument pointer.
                                --   The result is a cursor or pointer.
  | PrimSubP !PointerKind       -- ^ Find the difference of two pointers
                                --   or cursors.
                                --   The result is a native integer.
    -- | @PrimLoad mutability type base offset@ 
    -- 
    -- Load a value from a pointer at some byte offset.
    -- Before the record flattening pass, the loaded value may have record
    -- type; afterward, it may only have primitive type.
    --
    -- The mutability flag may be 'Constant' if the loaded memory is known to
    -- be constant (possibly initialized by a single store operation).
    -- Otherwise, it should be 'Mutable'.  Incorrect use of 'Constant' may
    -- cause incorrect optimizations.
  | PrimLoad !Mutability !PointerKind !ValueType
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
  | PrimStore !Mutability !PointerKind !ValueType
  | PrimAAddZ !Signedness !Size -- ^ Atomically add the target of a pointer to
                                --   an integer.  Return the original value at
                                --   that address.
  | PrimCastToOwned             -- ^ Cast a non-owned pointer to an owned
                                --   pointer.
  | PrimCastFromOwned           -- ^ Cast an owned pointer to a non-owned
                                --   pointer.
  | PrimCastFromCursor          -- ^ Extract the interior reference from a cursor.
  | PrimCursorBase              -- ^ Get the owned pointer from a cursor
  | PrimCastPtrToInt !Size      -- ^ Cast a pointer to an unsigned integer
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
  | PrimCmpF !Size !CmpOp       -- ^ Floating-point comparison
  | PrimAddF !Size              -- ^ Floating-point addition
  | PrimSubF !Size              -- ^ Floating-point subtraction
  | PrimMulF !Size              -- ^ Floating-point multiplication
  | PrimModF !Size              -- ^ Floating-point modulus
  | PrimDivF !Size              -- ^ Floating-point division
    -- | @PrimRoundF mode from-size to-sign to-size
    --
--   Floating-point to integer conversion.
  | PrimRoundF !RoundMode !Size !Signedness !Size
    
  | PrimPowF !Size              -- ^ Floating-point exponentiation
  | PrimUnaryF !UnaryFPIntrinsic !Size -- ^ Intrinsic FP function
  | PrimMemBar                         -- ^ Memory barrier

primReturnType :: Prim -> [ValueType]
primReturnType prim =
  case prim
  of PrimCastZ _ to_sgn to_sz -> int to_sgn to_sz
     PrimExtendZ sgn _ to_sz  -> int sgn to_sz
     PrimAddZ sgn sz          -> int sgn sz
     PrimSubZ sgn sz          -> int sgn sz
     PrimMulZ sgn sz          -> int sgn sz
     PrimModZ sgn sz          -> int sgn sz
     PrimDivZ sgn sz          -> int sgn sz
     PrimMaxZ sgn sz          -> int sgn sz
     PrimMinZ sgn sz          -> int sgn sz
     PrimAndZ sgn sz          -> int sgn sz
     PrimOrZ sgn sz           -> int sgn sz
     PrimXorZ sgn sz          -> int sgn sz
     PrimComplZ sgn sz        -> int sgn sz
     PrimShiftL sgn sz        -> int sgn sz
     PrimShiftR sgn sz        -> int sgn sz
     PrimCmpZ _ _ _           -> bool
     PrimCmpP _               -> bool
     PrimSelect t             -> [t]
     PrimAnd                  -> bool
     PrimOr                   -> bool
     PrimNot                  -> bool
     PrimAddP k               -> pointer_add k
     PrimLoad _ _ t           -> [t]
     PrimStore _ _ _          -> []
     PrimAAddZ sgn sz         -> int sgn sz
     PrimCastToOwned          -> [PrimType OwnedType]
     PrimCastFromOwned        -> pointer
     PrimCastFromCursor       -> pointer
     PrimCastPtrToInt sz      -> int Unsigned sz
     PrimGetFrameP            -> pointer
     PrimCastZToF _ sz        -> float sz
     PrimCastFToZ _ sz        -> int Signed sz
     PrimCmpF _ _             -> bool
     PrimAddF sz              -> float sz
     PrimSubF sz              -> float sz
     PrimMulF sz              -> float sz
     PrimModF sz              -> float sz
     PrimDivF sz              -> float sz
     PrimPowF sz              -> float sz
     PrimRoundF _ _ sgn sz    -> int sgn sz
     PrimUnaryF _ sz          -> float sz
     PrimMemBar               -> []
  where
    int sgn sz = [PrimType $ IntType sgn sz]
    float sz = [PrimType $ FloatType sz]
    bool = [PrimType BoolType]
    pointer = [PrimType PointerType]
    pointer_add k = [PrimType $ fromPointerKind $ addPResultType k]

-- | Determine the type of the result of 'PrimAddP'.
--   The type is either a cursor or a pointer.
addPResultType :: PointerKind -> PointerKind
addPResultType OwnedPtr = CursorPtr
addPResultType CursorPtr = CursorPtr
addPResultType PointerPtr = PointerPtr

data Lit =
    UnitL                       -- ^ The unit value
  | NullL                       -- ^ The NULL non-owned pointer
  | NullRefL                    -- ^ The NULL owned pointer
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

instance HasLabel Var where getLabel = varName

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
         UnitType -> "u_"
         IntType Signed _ -> "i_"
         IntType Unsigned _ -> "u_"
         FloatType _ -> "f_"

    type_leader (RecordType _) = "r_"

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

valType :: Val -> ValueType
valType (VarV v) = varType v
valType (RecV r _) = RecordType r
valType (LitV l) = PrimType $ litType l

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
    -- If 'PrimCall', call a global function directly.  The function must be a
    -- non-owned pointer.  The number of arguments must match what the function
    -- expects.
    --
    -- If 'JoinCall', branch to a local function.  The function must be a
    -- non-owned pointer.  The number of arguments must match what the function
    -- expects.  The call must be in tail position.
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
joinCallA = CallA JoinCall

-- | A statement.  Statements may have side effects.
data Stm =
    -- | Bind an atom's result to temporary variables
    LetE [ParamVar] Atom Stm
    -- | Define local functions
  | LetrecE !(Group FunDef) Stm
    -- | Conditional branch.  Inspect the value, then execute an alternative.
  | SwitchE Val [Alt]
    -- | Produce a value
  | ReturnE Atom
    -- | Raise an exception.
    --   The argument is a native integer value.
  | ThrowE Val

-- | A function.  The parameter is the data type used for the function body,
--   usually 'Stm'.
data FunBase a =
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
    -- | The function's entry points.  'ClosureCall' functions have
    --   entry points; other calling conventions don't.
    --
    --   FIXME: the entry points should be part of the function definition,
    --   not part of the function, because the variables in this 'EntryPoints' 
    --   count as variable definitions.
    --
    --   These names are used by closure conversion and in interface files. 
  , funEntryPoints :: !(Maybe EntryPoints)

  , funParams      :: [ParamVar] 
  , funReturnTypes :: [ValueType] 
  , funBody        :: a
  }

type Fun = FunBase Stm

isPrimFun, isJoinFun, isClosureFun :: FunBase a -> Bool
isPrimFun f = funConvention f == PrimCall
isJoinFun f = funConvention f == JoinCall
isClosureFun f = funConvention f == ClosureCall

setFunSize :: CodeSize -> FunBase a -> FunBase a
setFunSize sz f = f {funSize = sz}

setFunUses :: Uses -> Fun -> Fun
setFunUses u f = f {funUses = u}

-- | Remove size and uses information from a function
clearFunDCEInfo :: FunBase a -> FunBase a
clearFunDCEInfo f = f { funSize = unknownCodeSize
                      , funUses = ManyUses}

mkFun :: CallConvention -> Bool -> Int -> Maybe EntryPoints
      -> [ParamVar] -> [ValueType] -> a
      -> FunBase a
mkFun cc inl_req frame_size entry_points params returns body =
  Fun { funConvention  = cc
      , funSize        = unknownCodeSize
      , funUses        = ManyUses
      , funInlineRequest = inl_req
      , funFrameSize   = frame_size
      , funEntryPoints = entry_points
      , funParams      = params
      , funReturnTypes = returns
      , funBody        = body}

closureFun :: EntryPoints -> [ParamVar] -> [ValueType] -> Stm -> Fun
closureFun ep params returns body =
  mkFun ClosureCall False 0 (Just ep) params returns body

primFun :: [ParamVar] -> [ValueType] -> Stm -> Fun
primFun params returns body =
  mkFun PrimCall False 0 Nothing params returns body

joinFun :: [ParamVar] -> [ValueType] -> Stm -> Fun
joinFun params returns body =
  mkFun JoinCall False 0 Nothing params returns body

changeFunBody :: (a -> b) -> FunBase a -> FunBase b
changeFunBody f (Fun cc s u inl fs ep p r b) = Fun cc s u inl fs ep p r (f b)

changeFunBodyM :: Monad m => (a -> m b) -> FunBase a -> m (FunBase b)
changeFunBodyM f (Fun cc s u inl fs ep p r b) =
  do b' <- f b
     return $ Fun cc s u inl fs ep p r b'

type Alt = (Lit, Stm)

-- | A piece of static data.
--   The value must be a record or literal.
newtype StaticData = StaticData Val

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

data Group a = NonRec a | Rec [a]

instance Functor Group where
  fmap f (NonRec x) = NonRec (f x)
  fmap f (Rec xs) = Rec (fmap f xs)

instance Foldable Group where
  foldMap f (NonRec x) = f x
  foldMap f (Rec xs) = mconcat (map f xs)

instance Traversable Group where
  traverse f (NonRec x) = NonRec <$> f x
  traverse f (Rec xs) = Rec <$> traverse f xs
  mapM f (NonRec x) = NonRec `liftM` f x
  mapM f (Rec xs) = Rec `liftM` mapM f xs

mergeGroups :: [Group a] -> Group a
mergeGroups gs = Rec $ concatMap groupMembers gs

groupMembers :: Group a -> [a]
groupMembers (NonRec x) = [x]
groupMembers (Rec xs)   = xs

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
    { -- | The imported function's entry points.
      --   If the function is present, it has the same entry points.
      importEntryPoints :: EntryPoints

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
       globalClosure entry_points
     ImportPrimFun {_importVar = v} -> v
     ImportData {_importVar = v} -> v

data Module =
  Module 
  { moduleModuleName :: !ModuleName
  , moduleNameSupply :: !(Supply LocalID)
  , moduleImports :: [Import]    -- ^ Imported, externally defined variables
  , moduleGlobals :: [Group GlobalDef] -- ^ Global definitions
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

-- | Names of the global objects that make up a function.
--   These names are created when a closure-call function is created.  They're
--   used during closure conversion to generate function call code.
--
--   Call 'mkEntryPoints' or 'mkGlobalEntryPoints' to create an 'EntryPoints'.
--
--   The variables mentioned in 'EntryPoints'es behave like uses of the
--   variables, not as definitions.  Note that, prior to closure conversion, 
--   only the \"global closure\" field is defined.
--
--   Despite its name, the \"global closure\" is only global for global
--   functions.  For local functions, it's the name of a local variable
--   pointing to a dynamically allocated closure.
data EntryPoints =
  EntryPoints
  { _epType          :: {-# UNPACK #-} !FunctionType
  , _epArity         :: {-# UNPACK #-} !Int
  , _epDirectEntry   :: !Var
  , _epVectorEntry   :: !(Maybe Var) -- Only for vectorized functions
  , _epExactEntry    :: !Var
  , _epInexactEntry  :: !Var
  , _epInfoTable     :: !Var
  , _epGlobalClosure :: !Var
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

-- | Get the vector entry point of a function
vectorEntry :: EntryPoints -> Maybe Var
vectorEntry = _epVectorEntry

-- | Get the exact entry point of a function
exactEntry :: EntryPoints -> Var
exactEntry = _epExactEntry

-- | Get the inexact entry point of a function
inexactEntry :: EntryPoints -> Var
inexactEntry = _epInexactEntry

-- | Get the info table of a function
infoTableEntry :: EntryPoints -> Var
infoTableEntry = _epInfoTable

-- | Get the global closure of a function.
-- Only global functions have a global closure.
globalClosure :: EntryPoints -> Var
globalClosure = _epGlobalClosure

-- | Assign the global closure of a function.
--
--   Reassigning the global closure may occur during renaming.
setGlobalClosure :: Var -> EntryPoints -> EntryPoints
setGlobalClosure new_c ep = ep {_epGlobalClosure = new_c}

-- | All variables referenced by an 'EntryPoints'.
entryPointsVars :: EntryPoints -> [Var]
entryPointsVars ep =
  _epDirectEntry ep :
  _epExactEntry ep :
  _epInexactEntry ep :
  _epInfoTable ep :
  _epGlobalClosure ep :
  maybeToList (_epVectorEntry ep)

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

-- | Create a new variable that is identical to the given variable except that
--   it has a different ID.
--
--   The variable's name is not changed.  In the case of external variables,
--   the old and new variables cannot coexist because they have the same name.
newClonedVar :: Supplies m (Ident Var) => Var -> m Var
newClonedVar v = do
  ident <- fresh
  return $ v {varID = ident}

-- | Get the type of a literal
litType :: Lit -> PrimType
litType UnitL = UnitType
litType NullL = PointerType
litType NullRefL = OwnedType
litType (BoolL _) = BoolType
litType (IntL sgn sz _) = IntType sgn sz
litType (FloatL sz _) = FloatType sz

funType :: FunBase a -> FunctionType
funType f =
  mkFunctionType (funConvention f) (map varType $ funParams f) (funReturnTypes f)

