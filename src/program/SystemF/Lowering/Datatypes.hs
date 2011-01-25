{-| Lowering of data type operations.

Each System F data type translates to either a 'LL.ValueType' or to a
'LL.DynamicRecordType'.  Additionally, each data constructor translates to
some operations for building and taking apart that data type.  This module
handles all that.

Given a data type, 'typeLayout' decides how the data type's contents
are arranged in memory.  Layouts are used when compiling case statements to 
access the contents of a data structure.
-}
module SystemF.Lowering.Datatypes
       (PolyRepr(..),
        ValueLayout(..),
        PointerLayout(..),
        pprValueLayout,
        pprPointerLayout,
        valueLayoutType,
        typeLayout,
        paramTypeLayout,
        lowerValueType,
        lowerReturnType,
        lowerParamType,
        lowerFunctionReturn,
        lowerFunctionType)
where

import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Builtins.Builtins
import LowLevel.Build
import qualified LowLevel.Syntax as LL
import qualified LowLevel.CodeTypes as LL
import qualified LowLevel.Print as LL
import SystemF.Syntax
import Type.Environment
import Type.Eval
import Type.Type

-- | A 'PolyRepr' value is a placeholder for the representation dictionary of
--   the given type.  It is only used for polymorphic types (type variables,
--   or type variables applied to arguments).  The type is used as a key to
--   look up the correct dictionary value.
newtype PolyRepr = PolyRepr Type

-- | The layout of a value.
--   Any value can be converted to a 'LL.Val'.  A 'ValueLayout' object gives 
--   us the value's type.  Each disjunct is labeled with the data constructor.
data ValueLayout =
    OpaqueBoxedValue            -- ^ A pointer to a boxed object
  | OpaquePointerValue          -- ^ A pointer to a referenced object
  | SpecialValue !LL.ValueType  -- ^ Not an algebraic data type
  | ScalarValue !Var !LL.PrimType
  | RecordValue !Var [ValueLayout]
  | EnumValue !LL.PrimType [(Var, LL.Lit)]

-- | The layout of a non-value.  Non-values are accessed through pointers.
--   A 'PointerLayout' object gives us the object's layout in memory.
--   Each disjunct is labeled with the data constructor.
data PointerLayout =
    -- | A scalar value that is accessed by value (load/store it)
    ValueReference !ValueLayout
    -- | A scalar value that is accessed by reference (get a pointer to it)
  | ScalarReference !ValueLayout
    -- | A polymorphic value, accessed by reference
  | PolyReference !PolyRepr
    -- | A product type
  | ProductReference !Var [PointerLayout]
    -- | A sum-of-products type
  | SOPReference [(Var, [PointerLayout])]

-- | Pretty-print a @constructor => layout@ term.
pprConstructorClause :: Var -> Doc -> Doc
pprConstructorClause v doc = hang (pprVar v <+> text "=>") 8 doc

-- | Pretty-print a product layout using the syntax @[a, b, c]@.
pprProduct :: (a -> Doc) -> [a] -> Doc
pprProduct ppr xs = brackets $ sep $ punctuate (text ",") $ map ppr xs

-- | Pretty-print a sum layout using the syntax @{ c => a; d => b }@.
pprSum :: (a -> Doc) -> [(Var, a)] -> Doc
pprSum ppr xs =
  braces $ sep $
  punctuate (text ";") [pprConstructorClause v (ppr d) | (v, d) <- xs]

pprValueLayout :: ValueLayout -> Doc
pprValueLayout vl =
  case vl
  of OpaqueBoxedValue -> text "box"
     OpaquePointerValue -> text "ptr"
     SpecialValue ty -> text "special" <> parens (LL.pprValueType ty)
     ScalarValue con ty -> pprConstructorClause con $ LL.pprPrimType ty
     RecordValue con vl ->
       pprConstructorClause con $ pprProduct pprValueLayout vl
     EnumValue ty cases ->
       text "enum" <+> LL.pprPrimType ty $$ nest 4 (pprSum LL.pprLit cases)

pprPointerLayout :: PointerLayout -> Doc
pprPointerLayout pl =
  case pl
  of ValueReference vl -> hang (text "value") 4 $ pprValueLayout vl
     ScalarReference vl -> hang (text "scalar") 4 $ pprValueLayout vl
     PolyReference (PolyRepr t) -> text "poly" <+> pprType t
     ProductReference v fs ->
       pprConstructorClause v $ pprProduct pprPointerLayout fs
     SOPReference cases ->
       pprSum (pprProduct pprPointerLayout) cases

-- | Get the low-level type corresponding to this 'ValueLayout'.
valueLayoutType :: ValueLayout -> LL.ValueType
valueLayoutType layout =
  case layout
  of OpaqueBoxedValue -> LL.PrimType LL.OwnedType
     OpaquePointerValue -> LL.PrimType LL.PointerType
     SpecialValue ty -> ty
     ScalarValue _ primtype -> LL.PrimType primtype
     RecordValue _ layouts ->
       LL.RecordType $
       LL.constStaticRecord $
       map (LL.valueToFieldType . valueLayoutType) layouts
     EnumValue enum_type _ -> LL.PrimType enum_type

-------------------------------------------------------------------------------
-- Lowering for types

-- | Determine the lowered type corresponding to the given data type when
--   it is passed by value.  The data must be representable as a value.
lowerValueType :: TypeEnv -> Type -> LL.ValueType
lowerValueType tenv ty =
  case typeLayout tenv (ValRT ::: ty)
  of Left vlayout -> valueLayoutType vlayout
     Right _ -> internalError "lowerValueType"

-- | Determine the lowered type corresponding to the given data type and
--   representation, if there is one.  Side effect types don't have a
--   lowered equivalent.
lowerReturnType :: TypeEnv -> ReturnType -> Maybe LL.ValueType
lowerReturnType tenv (rrepr ::: rtype) =
  case rrepr
  of ValRT -> Just $ lowerValueType tenv rtype
     BoxRT -> Just (LL.PrimType LL.OwnedType)
     ReadRT -> Just (LL.PrimType LL.PointerType)
     OutRT -> Just (LL.PrimType LL.PointerType)
     WriteRT -> internalError "lowerReturnType: Invalid representation"
     SideEffectRT -> Nothing

lowerParamType :: TypeEnv -> ParamType -> Maybe LL.ValueType
lowerParamType tenv (prepr ::: ptype) =
  lowerReturnType tenv (paramReprToReturnRepr prepr ::: ptype)

lowerFunctionReturn :: TypeEnv -> ReturnType -> [LL.ValueType]
lowerFunctionReturn tenv rt = maybeToList $ lowerReturnType tenv rt

lowerFunctionType :: TypeEnv -> Type -> LL.FunctionType
lowerFunctionType tenv ty =
  let (params, ret) = fromFunType ty
      param_types = catMaybes $ map (lowerParamType tenv) params
      ret_type = lowerFunctionReturn tenv ret
  in LL.closureFunctionType param_types ret_type

-------------------------------------------------------------------------------

-- | Get the layout of a value, given its parameter type.
paramTypeLayout :: TypeEnv -> ParamType -> Either ValueLayout PointerLayout
paramTypeLayout tenv (repr ::: ty) =
  typeLayout tenv (paramReprToReturnRepr repr ::: ty)

-- | Get the layout of a value, given its return type.
typeLayout :: TypeEnv -> ReturnType -> Either ValueLayout PointerLayout
typeLayout tenv (repr ::: scrutinee_type) =
  case repr
  of ValRT  -> Left $ valTypeLayout tenv scrutinee_type
     BoxRT  -> Left OpaqueBoxedValue
     ReadRT -> Right $ readTypeLayout tenv scrutinee_type
     OutRT  -> Right $ readTypeLayout tenv scrutinee_type
     _ -> internalError "typeLayout: Unexpected representation"

lookupDataTypeForLayout tenv ty 
  | Just (tycon, ty_args) <- fromVarApp ty,
    Just data_type <- lookupDataType tycon tenv,
    Just cons <- sequence [lookupDataCon c tenv
                          | c <- dataTypeDataConstructors data_type] =
      (tycon, data_type, cons, ty_args)
  | otherwise = internalError $ "typeLayout: Unknown type: " ++ show (pprType ty)

valTypeLayout tenv ty =
  case getLevel ty
  of TypeLevel ->
       valDataTypeLayout tenv $ lookupDataTypeForLayout tenv ty
     KindLevel ->
       -- Types are erased
       SpecialValue (LL.PrimType LL.UnitType)
     _ -> internalError "valTypeLayout"
      

readTypeLayout tenv ty =
  readDataTypeLayout tenv $ lookupDataTypeForLayout tenv ty

valDataTypeLayout :: TypeEnv -> (Var, DataType, [DataConType], [Type])
                  -> ValueLayout
valDataTypeLayout tenv (tycon, data_type, con_types, ty_args)
  | tycon `isPyonBuiltin` the_bool = bool_layout
  | tycon `isPyonBuiltin` the_int = int_layout
  | tycon `isPyonBuiltin` the_float = float_layout

  | all_nullary_constructors, [con] <- cons = unit_layout con

  | all_nullary_constructors =
      let disjuncts = zip (dataTypeDataConstructors data_type) $
                      map nativeWordL [0..]
      in EnumValue LL.nativeWordType disjuncts

  | [con] <- cons, [con_type] <- con_types =
      -- This is a product type
      let (field_reprs, _) = instantiateDataConType con_type ty_args
          field_layouts = [valTypeLayout tenv ty
                          | repr ::: ty <- field_reprs,
                            check_val_repr repr]
      in RecordValue con field_layouts

  | otherwise =
      internalError "valDataTypeLayout: Cannot construct value of this type"
  where
    cons = dataTypeDataConstructors data_type

    -- True if no constructors have fields
    all_nullary_constructors = all (null . dataConPatternArgs) con_types
    
    -- Fields of a value must be values
    check_val_repr ValRT = True
    check_val_repr ValRT = internalError "valDataTypeLayout"    

    bool_layout = EnumValue LL.BoolType
                  [(pyonBuiltin the_False, LL.BoolL False),
                   (pyonBuiltin the_True, LL.BoolL True)]

    int_layout = SpecialValue (LL.PrimType LL.pyonIntType)
    float_layout = SpecialValue (LL.PrimType LL.pyonFloatType)

    unit_layout con = ScalarValue con LL.UnitType

readDataTypeLayout :: TypeEnv -> (Var, DataType, [DataConType], [Type])
                   -> PointerLayout
readDataTypeLayout tenv typedescr@(tycon, data_type, con_types, ty_args)
  -- bool, int, and float have special representations
  | tycon `isPyonBuiltin` the_bool ||
    tycon `isPyonBuiltin` the_int ||
    tycon `isPyonBuiltin` the_float =
      ScalarReference $ valDataTypeLayout tenv typedescr

  | all_nullary_constructors, [con] <- cons =
      ProductReference con []

  | all_nullary_constructors =
      let disjuncts = [(con, []) | con <- cons] 
      in SOPReference disjuncts

  | [con] <- cons, [con_type] <- con_types =
      -- This is a product type
      let (field_reprs, _) = instantiateDataConType con_type ty_args
      in ProductReference con $ map field_layout field_reprs
      
  where
    cons = dataTypeDataConstructors data_type

    -- True if no constructors have fields
    all_nullary_constructors = all (null . dataConPatternArgs) con_types
    
    field_layout (ValRT ::: ty) =
      ValueReference $ valTypeLayout tenv ty

    field_layout (BoxRT ::: _) =
      ValueReference OpaqueBoxedValue

    field_layout (ReadRT ::: ty) =
      case fromVarApp ty
      of Just (op, args) ->
           case lookupDataType op tenv
           of Just _ ->
                -- This field is a data type; compute its layout
                readTypeLayout tenv ty
              Nothing ->
                -- This field is an application of a type variable.
                -- It has an unknown layout; use runtime layout information.
                PolyReference (PolyRepr ty)
         Nothing ->
           case ty
           of FunT {} -> ScalarReference OpaqueBoxedValue
              _ -> internalError "readDataTypeLayout"

