{-| Definitions of built-in variables and some type-related data structures.

Some of these variables are assigned in "Type.Environment", while others
get their values from source code.
-}

{-# LANGUAGE TemplateHaskell #-}
module Type.BuiltinVar where

import Control.Monad
import qualified Language.Haskell.TH as TH

import Common.Identifier
import Common.Label
import Type.Var
import Type.Level

data Binder = (:::) { binderVar :: Var, binderType :: Type}

data Type =
    -- | A variable or constructor
    VarT Var
    -- | A type application
  | AppT Type Type
    -- | A type function
  | LamT {-#UNPACK#-}!Binder Type
    -- | A function type
  | FunT Type Type
    -- | A universal quantifier
  | AllT {-#UNPACK#-}!Binder Type
    -- | An arbitrary, opaque type inhabiting the given kind.  The kind has
    --   no free type variables.
  | AnyT Type
    -- | An integer type index.  These inhabit kind 'intIndexT'.
  | IntT !Integer

    -- | A coercion type constructor.
    --
    --   A coercion (s ~ t) carries the ability to coerce a value of type s
    --   to a value of type t.
  | CoT Kind

    -- | An unboxed tuple constructor.
    --   The type parameters have the specified kinds, which must be either
    --   'ValK' or 'BoxK'.
    --
    --   Unboxed tuples are introduced after representation inference.
  | UTupleT ![BaseKind]

infixr 4 `FunT`
infixl 7 `AppT`

-- | Kinds and types are represented using the same data structures
type Kind = Type

-- | Base kinds as an enumerative data structure.  Each base kind corresponds
--   to a variable.
data BaseKind =
    ValK
  | BoxK
  | BareK
  | OutK
  | WriteK
  | IntIndexK
    deriving(Eq, Ord, Show)

-- -- | The first variable ID that's not reserved for predefined variables
-- firstAvailableVarID :: VarID

-- Define 'firstAvailableVarID', 'builtinVarTable',
-- and 'kindV', 'kindT', 'intindexV', 'intindexT', ...

$(let concat_decs d1 d2 = liftM2 (++) d1 d2

      define_variable :: String -> Int -> String -> Level -> TH.DecsQ
      define_variable source_name id meta_name level =
        let val_name = TH.mkName (source_name ++ "V")
            ty_name = TH.mkName (source_name ++ "T")
            label = [| Just $ plainLabel builtinModuleName meta_name [] |]
        in sequence
           [ TH.valD (TH.varP val_name)
             (TH.normalB [| mkVar (toIdent id) $label level |]) []

           , TH.valD (TH.varP ty_name)
             (TH.normalB [| VarT $(TH.varE val_name) |]) []
           ]

      -- List of (source name, triolet name, level, externally declared)
      variables =
        [ -- The sort of all kinds
          ("kind", "kind", SortLevel, False)

          -- Kinds
        , ("intindex", "intindex", KindLevel, False)
        , ("val", "val", KindLevel, False)
        , ("box", "box", KindLevel, False)
        , ("bare", "bare", KindLevel, False)
        , ("out", "out", KindLevel, False)
        , ("init", "init", KindLevel, False)

          -- Types
        , ("initCon", "Init", TypeLevel, False)
        , ("outPtr", "OutPtr", TypeLevel, False)
        , ("cursor", "cursor", TypeLevel, False)
        , ("store", "Store", TypeLevel, False)
        , ("posInfty", "pos_infty", TypeLevel, False)
        , ("negInfty", "neg_infty", TypeLevel, False)
        , ("arr", "arr", TypeLevel, False)
        , ("int", "int", TypeLevel, False)
        , ("uint", "uint", TypeLevel, False)
        , ("float", "float", TypeLevel, False)
        , ("byte", "byte", TypeLevel, False)

        , ("asBox", "AsBox", TypeLevel, True)
        , ("asBare", "AsBare", TypeLevel, True)
        , ("bool", "bool", TypeLevel, True)
        , ("noneType", "NoneType", TypeLevel, True)
        , ("valInfo", "ReprVal", TypeLevel, True)
        , ("bareInfo", "Repr", TypeLevel, True)
        , ("boxInfo", "TypeObject", TypeLevel, True)
        , ("sizeAlign", "SizeAlign", TypeLevel, True)
        , ("sizeAlignVal", "SizeAlignVal", TypeLevel, True)
        , ("fiInt", "FIInt", TypeLevel, True)
        , ("isRef", "IsRef", TypeLevel, True)
        , ("ref", "Ref", TypeLevel, False) -- Has special boxing rules
        , ("stored", "Stored", TypeLevel, False) -- Has special layout rules
        , ("boxed", "Boxed", TypeLevel, True)
        , ("opaqueRef", "OpaqueRef", TypeLevel, True)

          -- Type variables
        , ("cursorTypeParameter", "a", TypeLevel, False)
        , ("storedTypeParameter", "a", TypeLevel, False)
        , ("arrTypeParameter1", "n", TypeLevel, False)
        , ("arrTypeParameter2", "a", TypeLevel, False)
        , ("refTypeParameter", "a", TypeLevel, False)

          -- Data constructors
        , ("valInfo_con", "reprVal", ObjectLevel, True)
        , ("bareInfo_con", "repr", ObjectLevel, True)
        , ("boxInfo_con", "typeObject", ObjectLevel, True)
        , ("sizeAlign_con", "sizeAlign", ObjectLevel, True)
        , ("sizeAlignVal_con", "sizeAlignVal", ObjectLevel, True)
        , ("store_con", "store", ObjectLevel, False)
        , ("fiInt_con", "fiInt", ObjectLevel, True)
        , ("true_con", "True", ObjectLevel, True)
        , ("false_con", "False", ObjectLevel, True)
        , ("isAReference", "isAReference", ObjectLevel, True)
        , ("notAReference", "notAReference", ObjectLevel, True)
        , ("ref_con", "ref", ObjectLevel, False) -- Has special boxing rules
        , ("stored_con", "stored", ObjectLevel, False)

          -- Global size information variables
        , ("boxInfo_valInfo", "typeObject_reprVal", ObjectLevel, True)
        , ("boxInfo_bareInfo", "typeObject_repr", ObjectLevel, True)
        , ("boxInfo_boxInfo", "typeObject_typeObject", ObjectLevel, True)
        , ("valInfo_cursor", "reprVal_cursor", ObjectLevel, True)
        , ("valInfo_store", "reprVal_store", ObjectLevel, True)
        , ("valInfo_int", "reprVal_int", ObjectLevel, True)
        , ("valInfo_uint", "reprVal_uint", ObjectLevel, True)
        , ("valInfo_float", "reprVal_float", ObjectLevel, True)
        , ("valInfo_byte", "reprVal_byte", ObjectLevel, True)
        , ("bareInfo_stored", "repr_Stored", ObjectLevel, True)
        , ("bareInfo_arr", "repr_arr", ObjectLevel, True)
        , ("bareInfo_ref", "repr_Ref", ObjectLevel, True)
        , ("fieldInfo_ref", "fieldSize_ref", ObjectLevel, True)

          -- Global variables for serialization
        , ("putInt", "putInt", ObjectLevel, True)
        , ("putUint", "putUint", ObjectLevel, True)
        , ("putUintAsUint8", "putUintAsUint8", ObjectLevel, True)
        , ("putUintAsUint16", "putUintAsUint16", ObjectLevel, True)
        , ("putFloat", "putFloat", ObjectLevel, True)
        , ("putByte", "putByte", ObjectLevel, True)
        , ("putCursor", "putCursor", ObjectLevel, True)
        , ("putStore", "putStore", ObjectLevel, True)
        , ("putBareCoercion", "putBareCoercion", ObjectLevel, True)
        , ("putBoxCoercion", "putBoxCoercion", ObjectLevel, True)
        , ("putStoredInt", "putStoredInt", ObjectLevel, True)
        , ("putStoredUint", "putStoredUint", ObjectLevel, True)
        , ("putStoredFloat", "putStoredFloat", ObjectLevel, True)
        , ("putArr", "putArr", ObjectLevel, True)
        , ("putRef", "putRef", ObjectLevel, True)
        , ("putPointerlessObject", "putPointerlessObject", ObjectLevel, True)
        , ("putBoxedObject", "putBoxedObject", ObjectLevel, True)
        , ("getInt", "getInt", ObjectLevel, True)
        , ("getUint", "getUint", ObjectLevel, True)
        , ("getUint8AsUint", "getUint8AsUint", ObjectLevel, True)
        , ("getUint16AsUint", "getUint16AsUint", ObjectLevel, True)
        , ("getFloat", "getFloat", ObjectLevel, True)
        , ("getByte", "getByte", ObjectLevel, True)
        , ("getCursor", "getCursor", ObjectLevel, True)
        , ("getStore", "getStore", ObjectLevel, True)
        , ("getBareCoercion", "getBareCoercion", ObjectLevel, True)
        , ("getBoxCoercion", "getBoxCoercion", ObjectLevel, True)
        , ("getStoredInt", "getStoredInt", ObjectLevel, True)
        , ("getStoredUint", "getStoredUint", ObjectLevel, True)
        , ("getStoredFloat", "getStoredFloat", ObjectLevel, True)
        , ("getArr", "getArr", ObjectLevel, True)
        , ("getRef", "getRef", ObjectLevel, True)
        , ("getPointerlessObject", "getPointerlessObject", ObjectLevel, True)
        , ("getBoxedObject", "getBoxedObject", ObjectLevel, True)

          -- Global variables used for generating address arithmetic and
          -- size computation
        , ("and", "and", ObjectLevel, True)
        , ("or", "or", ObjectLevel, True)
        , ("not", "not", ObjectLevel, True)

        , ("addI", "addI", ObjectLevel, True)
        , ("subI", "subI", ObjectLevel, True)
        , ("negateI", "negI", ObjectLevel, True)
        , ("mulI", "mulI", ObjectLevel, True)
        , ("modI", "modI", ObjectLevel, True)
        , ("maxI", "maxI", ObjectLevel, True)

        , ("eqU", "eqU", ObjectLevel, True)
        , ("addU", "addU", ObjectLevel, True)
        , ("subU", "subU", ObjectLevel, True)
        , ("modU", "modU", ObjectLevel, True)
        , ("maxU", "maxU", ObjectLevel, True)
        , ("intToUint", "intToUint", ObjectLevel, True)
        , ("uintToInt", "uintToInt", ObjectLevel, True)

        , ("defaultAsBox", "defaultAsBox", ObjectLevel, True)
        , ("defaultAsBare", "defaultAsBare", ObjectLevel, True)
        , ("blockcopy", "blockcopy", ObjectLevel, True)
        , ("idCoercion", "idCoercion", ObjectLevel, True)
        ]

      num_variables = length variables

      -- List of quoted @(String, Var)@ pairs
      builtin_var_table :: [TH.ExpQ]
      builtin_var_table =
        [ [| (mname, $(TH.varE $ TH.mkName (sname ++ "V"))) |]
        | (sname, mname, _, True) <- variables]

      fixed_declarations =
        [d| firstAvailableVarID = toIdent (1 + num_variables)
            builtinVarTable = $(TH.listE builtin_var_table) |]

      var_declarations =
        foldr concat_decs (return [])
        [ define_variable sname id mname level
        | ((sname, mname, level, _), id) <- zip variables [1..]]
  in fixed_declarations `concat_decs` var_declarations

 )
