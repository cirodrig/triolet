{-| Intermediate representation with explicit data representations. 

This representation extends the pure System F
with more detailed information about how data structures fit
into memory.  Each variable binding gets extra information.
-}

module SystemF.MemoryIR where

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
  | LocalVarP Var Type ExpM

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