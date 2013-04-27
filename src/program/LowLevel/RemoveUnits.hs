{-| Remove unit types from a program.

Before closure conversion, we must keep unit values around in order to
account for curried application.  If the function @f@ takes two arguments 
and returns an int, then @f(1)@ returns a function while @f(1, nil)@ returns 
an int.  After closure conversion, unit values serve no purpose and we can
delete them.

The function 'removeUnits' removes unit values from local variables,
record types, and function parameters/returns in a program.
-}

{-# LANGUAGE FlexibleInstances #-}
module LowLevel.RemoveUnits(removeUnits) where

import Common.Error
import LowLevel.CodeTypes
import LowLevel.Syntax

-- | Expand a variable to a value.
--   If the variable has unit type, then delete it.
expandVar :: Var -> [Val]
expandVar v 
  | varType v == PrimType UnitType = [] 
  | otherwise                      = [VarV v]

flattenParamList :: [ParamVar] -> [ParamVar]
flattenParamList vs = filter not_unit_type vs 
  where
    not_unit_type v = case varType v
                      of PrimType UnitType -> False 
                         _ -> True

-- Remove unit values from types
flattenTypeList :: [ValueType] -> [ValueType]
flattenTypeList xs = concatMap flattenType xs

flattenFunctionType :: FunctionType -> FunctionType
flattenFunctionType ft =
  mkFunctionType (ftConvention ft)
  (flattenTypeList $ ftParamTypes ft)
  (flattenTypeList $ ftReturnTypes ft)

flattenType :: ValueType -> [ValueType]
flattenType (PrimType UnitType) = []
flattenType (PrimType pt) = [PrimType pt]
flattenType (RecordType rt) = [RecordType $ removeUnitFields rt]

class Flatten a where
  flatten :: a -> a

instance Flatten a => Flatten [a] where
  flatten x = fmap flatten x

instance Flatten a => Flatten (Maybe a) where
  flatten x = fmap flatten x

flattenValList :: [Val] -> [Val]
flattenValList vs = concatMap flattenVal vs

flattenVal :: Val -> [Val]
flattenVal value =
  case value
  of VarV v       -> expandVar v
     RecV sr vals -> [RecV sr $ flattenValList vals]
     LitV UnitL   -> []
     LitV _       -> [value]

flattenSingleVal :: Val -> Val
flattenSingleVal v =
  case flattenVal v
  of [v'] -> v'
     _ -> internalError "flattenSingleVal"

instance Flatten Atom where
  flatten atom =
    case atom
    of ValA vs -> ValA $ flattenValList vs 
       CallA conv op vs -> CallA conv (flattenSingleVal op) (flattenValList vs)

       -- Load or store of unit value is deleted
       PrimA (PrimLoad _ _ (PrimType UnitType)) _ -> ValA []
       PrimA (PrimStore _ _ (PrimType UnitType)) _ -> ValA []
       PrimA prim vs -> PrimA prim (flattenValList vs)

instance Flatten Stm where
  flatten stm =
    case stm
    of LetE params atom body ->
         LetE (flattenParamList params) (flatten atom) (flatten body)
       LetrecE grp stm ->
         LetrecE (fmap flatten grp) (flatten stm)
       SwitchE scr alts ->
         SwitchE (flattenSingleVal scr) [(p, flatten s) | (p, s) <- alts]
       ReturnE atom -> ReturnE (flatten atom)
       ThrowE v -> ThrowE (flattenSingleVal v)

instance Flatten (FunBase Stm) where
  flatten f = f { funParams = flattenParamList $ funParams f
                , funReturnTypes = flattenTypeList $ funReturnTypes f
                , funBody = flatten $ funBody f
                }

instance Flatten a => Flatten (Def a) where
  flatten (Def v x) = Def v (flatten x)

instance Flatten StaticData where
  flatten (StaticData x) = StaticData $ flattenSingleVal x

instance Flatten GlobalDef where
  flatten (GlobalFunDef fd) = GlobalFunDef $ flatten fd
  flatten (GlobalDataDef dd) = GlobalDataDef $ flatten dd

flattenGlobals groups = map (fmap flatten) groups

flattenEntryPoints ep =
  let ty = flattenFunctionType $ entryPointsType ep
      arity = length $ ftParamTypes ty
  in ep {_epType = ty, _epArity = arity}

instance Flatten Import where
  flatten (ImportClosureFun ep mf) =
    importMustBeNothing mf $
    ImportClosureFun (flattenEntryPoints ep) Nothing
  
  flatten (ImportPrimFun v ft mf) =
    importMustBeNothing mf $
    ImportPrimFun v (flattenFunctionType ft) Nothing

  flatten (ImportData v mv) =
    ImportData v (flatten mv)

importMustBeNothing Nothing  x = x
importMustBeNothing (Just _) _ =
  internalError "flattenImport: Imported data should be discarded"

removeUnits :: Module -> IO Module
removeUnits mod =
  return $
  mod { moduleImports = map flatten $ moduleImports mod
      , moduleGlobals = flattenGlobals $ moduleGlobals mod
      }