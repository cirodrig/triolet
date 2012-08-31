{-| Convert a module from specification types to memory types.

The conversion is performed in a single pass over a module.

This conversion is performed before the builtin module is initialized,
consequently, we take care not to examine any builtin variables.
Instead, the needed variables are passed in as arguments.
-}

module SystemF.SpecToMem(convertSpecToMemTypes)
where

import Common.Error
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Type

-- | Hold some type constructors in variables so we can use them.
data Info = Info { var_Init   :: !Var
                 , var_OutPtr :: !Var
                 , var_Store  :: !Var
                 }

isInit :: Info -> Var -> Bool
isInit ctx v = var_Init ctx == v

convertKind :: Type -> Type
convertKind (k1 `FunT` k2) =
  convertKind k1 `FunT` convertKind k2

convertKind (VarT v)
  | v == initV = boxT          -- Initializers become functions
  | otherwise  = VarT v        -- Other kinds are unchanged

convertTypes ctx ts = map (convertType ctx) ts

convertType :: Info -> Type -> Type
convertType ctx ty
  | Just (op, [arg]) <- fromVarApp ty, isInit ctx op =
      let arg' = convertType ctx arg
      in varApp (var_OutPtr ctx) [arg'] `FunT` VarT (var_Store ctx)

  | otherwise =
      case ty
      of VarT v
           | isInit ctx v -> internalError "convertType: Unexpected 'Init'"
           | otherwise -> ty
         IntT _ -> ty
         AppT op arg -> AppT (continue op) (continue arg)
         FunT dom rng -> FunT (continue dom) (continue rng)
         LamT (a ::: k) rng -> LamT (a ::: convertKind k) (continue rng)
         AllT (a ::: k) rng -> AllT (a ::: convertKind k) (continue rng)
         AnyT k -> AnyT (convertKind k)
         CoT k -> CoT k
  where
    continue t = convertType ctx t

convertTyParam (TyPat (v ::: k)) = TyPat (v ::: convertKind k)

convertSpecToMemTypes :: Var -> Var -> Var -> Module Mem -> Module Mem
convertSpecToMemTypes v_Init v_OutPtr v_Store mod =
  let ctx = Info v_Init v_OutPtr v_Store
  in mapModuleTypes convertKind (convertType ctx) mod
