{-| Intermediate representation with explicit data representations. 

This representation extends the pure System F
with more detailed information about how data structures fit
into memory.  Each variable binding gets extra information.
-}

module SystemF.MemoryIR where

import Common.Error
import SystemF.Syntax
import Type.Type
import Type.Var

data Mem

newtype instance Typ Mem = TypM {fromTypM :: Type}

data instance Pat Mem =
    -- | A variable binding.  This binds a value or a pointer, depending on
    --   the representation being used.
    --
    --   * ValPT Nothing: bind a value
    --   * BoxPT, ReadPT, OutPT: bind a pointer
    --   * WritePT: not permitted
    MemVarP Var !ParamType

    -- | A local, dynamically allocated variable.  The dynamically allocated
    --   memory exists as long as the variable is in scope.  The pattern takes
    --   a representation dictionary for this type as a parameter.
    --
    --   This pattern may only appear as the binder of a let expression.
  | LocalVarP Var Type ExpM
    
    -- | A wildcard pattern.  No variable is bound to this value.
    --
    -- This pattern may only appear in a function parameter or case 
    -- alternative.  It may not appear in a let expression.
  | MemWildP !ParamType

patMVar :: PatM -> Maybe Var
patMVar (MemVarP v _) = Just v
patMVar (LocalVarP v _ _) = Just v
patMVar (MemWildP _) = Nothing

patMVar' :: PatM -> Var
patMVar' pat =
  case patMVar pat
  of Just v -> v
     Nothing -> internalError "patMVar': Unexpected wildcard pattern"

patMType :: PatM -> Type
patMType (MemVarP _ (_ ::: ty)) = ty
patMType (LocalVarP _ ty _) = ty
patMType (MemWildP (_ ::: ty)) = ty

-- | Get the representation of the value bound to this pattern.
--   It's an error to call this on a 'LocalVarP'.
patMRepr :: PatM -> ParamRepr
patMRepr (MemVarP _ (prepr ::: _)) = prepr
patMRepr (LocalVarP _ _ _) = internalError "patMRepr"
patMRepr (MemWildP (prepr ::: _)) = prepr

-- | Get the representation of the value bound by this pattern.
--   For let expressions, this is the representation seen in the body
--   of the expression, not the representation seen in the RHS.
patMReturnRepr :: PatM -> ReturnRepr
patMReturnRepr (MemVarP _ (prepr ::: _)) = paramReprToReturnRepr prepr
patMReturnRepr (LocalVarP _ _ _) = ReadRT
patMReturnRepr (MemWildP (prepr ::: _)) = paramReprToReturnRepr prepr

data instance TyPat Mem  = TyPatM Var Type
newtype instance Ret Mem = RetM {fromRetM :: ReturnType}
newtype instance Exp Mem = ExpM {fromExpM :: BaseExp Mem}
newtype instance Alt Mem = AltM {fromAltM :: BaseAlt Mem}
newtype instance Fun Mem = FunM {fromFunM :: BaseFun Mem}

type TypM = Typ Mem
type PatM = Pat Mem
type TyPatM = TyPat Mem
type RetM = Ret Mem
type ExpM = Exp Mem
type AltM = Alt Mem
type FunM = Fun Mem