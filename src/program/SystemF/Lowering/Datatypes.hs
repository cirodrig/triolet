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
        OwnedLayout(..),
        PointerLayout(..),
        Layout(..),
        pprValueLayout,
        pprOwnedLayout,
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

-- | Add a list of variables to the type environment. 
--   This is called on existential variables from a data structure.
insertExistentialVars :: [ParamType] -> TypeEnv -> TypeEnv
insertExistentialVars params env = foldr ins env params
  where
    ins (ValPT (Just v) ::: ty) env = insertType v (ValRT ::: ty) env

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

-- | The layout of a referenced object.
--   Non-values are accessed through pointers.
--   A 'PointerLayout' object gives us the object's layout in memory.
--   Each disjunct is labeled with the data constructor.
data PointerLayout =
    -- | A scalar value that is accessed by value (load/store it)
    ValueReference !ValueLayout
    -- | A scalar value that is accessed by reference (get a pointer to it)
  | ScalarReference !ValueLayout
    -- | A reference to a dynamically allocated value.  This occupies one
    --   pointer worth of space.
  | IndirectReference PointerLayout
    -- | A polymorphic value, accessed by reference
  | PolyReference !PolyRepr
    -- | A product type
  | ProductReference !Var [PointerLayout]
    -- | A sum-of-products type
  | SOPReference [(Var, [PointerLayout])]

-- | The layout of a boxed object.  It is like a referenced object,
--   except that there is a header we have to account for.
data OwnedLayout = Box PointerLayout

data Layout =
    ValueLayout !ValueLayout
  | OwnedLayout !OwnedLayout
  | PointerLayout !PointerLayout

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

pprOwnedLayout :: OwnedLayout -> Doc
pprOwnedLayout (Box pl) = 
  text "box" <+> parens (pprPointerLayout pl)

pprPointerLayout :: PointerLayout -> Doc
pprPointerLayout pl =
  case pl
  of ValueReference vl -> hang (text "value") 4 $ pprValueLayout vl
     ScalarReference vl -> hang (text "scalar") 4 $ pprValueLayout vl
     IndirectReference l -> text "ref" <+> parens (pprPointerLayout l)
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
lowerValueType :: TypeEnv -> Type -> FreshVarM LL.ValueType
lowerValueType tenv ty = do
  layout <- typeLayout tenv (ValRT ::: ty)
  case layout of
    ValueLayout vlayout -> return $ valueLayoutType vlayout
    _ -> internalError "lowerValueType"

-- | Determine the lowered type corresponding to the given data type and
--   representation, if there is one.  Side effect types don't have a
--   lowered equivalent.
lowerReturnType :: TypeEnv -> ReturnType -> FreshVarM (Maybe LL.ValueType)
lowerReturnType tenv (rrepr ::: rtype) =
  case rrepr
  of ValRT -> fmap Just $ lowerValueType tenv rtype
     BoxRT -> return $ Just (LL.PrimType LL.OwnedType)
     ReadRT -> return $ Just (LL.PrimType LL.PointerType)
     OutRT -> return $ Just (LL.PrimType LL.PointerType)
     WriteRT -> internalError "lowerReturnType: Invalid representation"
     SideEffectRT -> return Nothing

lowerParamType :: TypeEnv -> ParamType -> FreshVarM (Maybe LL.ValueType)
lowerParamType tenv (prepr ::: ptype) =
  lowerReturnType tenv (paramReprToReturnRepr prepr ::: ptype)

lowerFunctionReturn :: TypeEnv -> ReturnType -> FreshVarM [LL.ValueType]
lowerFunctionReturn tenv rt = fmap maybeToList $ lowerReturnType tenv rt

lowerFunctionType :: TypeEnv -> Type -> FreshVarM LL.FunctionType
lowerFunctionType tenv ty = do
  let (params, ret) = fromFunType ty
  m_param_types <- mapM (lowerParamType tenv) params
  let param_types = catMaybes m_param_types
  ret_type <- lowerFunctionReturn tenv ret
  return $ LL.closureFunctionType param_types ret_type

-------------------------------------------------------------------------------

-- | Get the layout of a value, given its parameter type.
paramTypeLayout :: TypeEnv -> ParamType -> FreshVarM Layout
paramTypeLayout tenv (repr ::: ty) =
  typeLayout tenv (paramReprToReturnRepr repr ::: ty)

-- | Get the layout of a value, given its return type.  The value must be
--   in the natural representation for its type, and the head term must
--   be a type constructor application.
--
--   This function calls one of several internal functions to find the
--   value's layout, depending on the given representation and type.
typeLayout :: TypeEnv -> ReturnType -> FreshVarM Layout
typeLayout tenv (repr ::: scrutinee_type) =
  case repr
  of ValRT  -> fmap ValueLayout $ valTypeLayout tenv scrutinee_type
     -- Boxed object have the same layout as referenced objects except
     -- for the boxing
     BoxRT  -> fmap (OwnedLayout . Box) $ memTypeLayout tenv scrutinee_type
     ReadRT -> fmap PointerLayout $ memTypeLayout tenv scrutinee_type
     OutRT  -> fmap PointerLayout $ memTypeLayout tenv scrutinee_type
     _ -> internalError "typeLayout: Unexpected representation"

lookupDataTypeForLayout tenv ty 
  | Just (tycon, ty_args) <- fromVarApp ty,
    Just data_type <- lookupDataType tycon tenv,
    Just cons <- sequence [lookupDataCon c tenv
                          | c <- dataTypeDataConstructors data_type] =
      (tycon, data_type, cons, ty_args)
  | otherwise = internalError $ "typeLayout: Unknown data type: " ++ show (pprType ty)

-- | Get the layout of a value of type 'ty', represented as a value
valTypeLayout tenv ty =
  case getLevel ty
  of TypeLevel ->
       valDataTypeLayout tenv $ lookupDataTypeForLayout tenv ty
     KindLevel ->
       -- Types are erased
       return $ SpecialValue (LL.PrimType LL.UnitType)
     _ -> internalError "valTypeLayout"

-- | Get the layout of an object field that is stored in memory.
memFieldLayout tenv ty =
  case fromVarApp ty
  of Just (op, args) ->
       case lookupDataType op tenv
       of Just _ ->
            -- This field is a data type; compute its layout
            memTypeLayout tenv ty
          Nothing ->
            -- This field is an application of a type variable.
            -- It has an unknown layout; use runtime layout information.
            return $ PolyReference (PolyRepr ty)
     Nothing ->
       case ty
       of FunT {} -> return $ ScalarReference OpaqueBoxedValue
          _ -> internalError "memFieldLayout"

-- | Get the layout of an object that is represented by reference.
memTypeLayout tenv ty =
  memDataTypeLayout tenv $ lookupDataTypeForLayout tenv ty

valDataTypeLayout :: TypeEnv -> (Var, DataType, [DataConType], [Type])
                  -> FreshVarM ValueLayout
valDataTypeLayout tenv (tycon, data_type, con_types, ty_args)
  | tycon `isPyonBuiltin` the_bool = return bool_layout
  | tycon `isPyonBuiltin` the_int = return int_layout
  | tycon `isPyonBuiltin` the_float = return float_layout

  | all_nullary_constructors, [con] <- cons = return $ unit_layout con

  | all_nullary_constructors =
      let disjuncts = zip (dataTypeDataConstructors data_type) $
                      map nativeWordL [0..]
      in return $ EnumValue LL.nativeWordType disjuncts

  | [con] <- cons, [con_type] <- con_types = do
      -- This is a product type
      (ex_vars, field_reprs, _) <-
        instantiateDataConTypeWithFreshVariables con_type ty_args

      let local_tenv = insertExistentialVars ex_vars tenv
      field_layouts <- sequence [valTypeLayout local_tenv ty
                                | repr ::: ty <- field_reprs,
                                  check_val_repr repr]
      return $ RecordValue con field_layouts

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

-- | Get the layout of an object that's stored in memory
memDataTypeLayout :: TypeEnv -> (Var, DataType, [DataConType], [Type])
                   -> FreshVarM PointerLayout
memDataTypeLayout tenv typedescr@(tycon, data_type, con_types, ty_args)
  -- bool, int, and float have special representations
  | tycon `isPyonBuiltin` the_bool ||
    tycon `isPyonBuiltin` the_int ||
    tycon `isPyonBuiltin` the_float =
      fmap ScalarReference $ valDataTypeLayout tenv typedescr

  -- Referenced has a special representation in memory
  | tycon `isPyonBuiltin` the_Referenced =
      let [arg] = ty_args
      in fmap IndirectReference $ memFieldLayout tenv arg

  | all_nullary_constructors, [con] <- cons =
      return $ ProductReference con []

  | all_nullary_constructors =
      let disjuncts = [(con, []) | con <- cons] 
      in return $ SOPReference disjuncts

  | [con] <- cons, [con_type] <- con_types = do
      -- This is a product type
      (ex_vars, field_reprs, _) <-
        instantiateDataConTypeWithFreshVariables con_type ty_args

      let local_tenv = insertExistentialVars ex_vars tenv
      field_layouts <- mapM (field_layout local_tenv) field_reprs
      return $ ProductReference con field_layouts

  | otherwise =
      internalError "memDataTypeLayout: Not implemented for SOP types"
  where
    cons = dataTypeDataConstructors data_type

    -- True if no constructors have fields
    all_nullary_constructors = all (null . dataConPatternArgs) con_types
    
    field_layout local_tenv (ValRT ::: ty) =
      fmap ValueReference $ valTypeLayout local_tenv ty

    field_layout local_tenv (BoxRT ::: _) =
      return $ ValueReference OpaqueBoxedValue

    field_layout local_tenv (ReadRT ::: ty) = memFieldLayout local_tenv ty

