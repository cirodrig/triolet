{-| Known values.

Most of the simplification performed by the simplifier relies on knowing some
approximation of the run-time value of an expresion or a variable.  The
'KnownValue' data type is how we store this information.

A data value that's in the correct representation for a @case@ statement is
represented by a 'DataValue' term.  If it's stored in memory and could be
inspected after loading, it's represented by a 'StoredValue' term.  If it's
an initializer for the contents of memory, it's a 'WriterValue' term.
-}

module SystemF.KnownValue where

import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import SystemF.Rename
import Type.Compare
import Type.Environment
import Type.Eval
import Type.Rename
import Type.Type

s1 `intersects` s2 = not $ Set.null $ Set.intersection s1 s2

-- | Map variables to their approximate values
type KnownValues = IntMap.IntMap KnownValue

type MaybeValue = Maybe KnownValue

-- | A value that is known (or partially known) at compile time.
--
--   Known values are used for compile-time partial evaluation:
--   inlining, constant propagation, copy propagation, and case of
--   known value elimination.
data KnownValue =
    -- | A literal value
    LitValue ExpInfo Lit
    
    -- | A variable reference, where nothing is known about the variable's
    --   value
  | VarValue ExpInfo !Var

    -- | A variable's inlined value.  The expression should be inlined
    --   wherever the variable is used.  The expression should be simplified
    --   after inlining.
  | InlinedValue ExpM

    -- | A complex value.  If a variable is given, the variable holds this 
    --   value.
  | ComplexValue !(Maybe Var) !ComplexValue

complexKnownValue :: ComplexValue -> KnownValue
complexKnownValue = ComplexValue Nothing

-- | A complex value.  Complex values are generally not worth inlining unless
--   it enables further optimizations.
data ComplexValue =
    -- | A function value
    FunValue ExpInfo !FunM
    
    -- | A fully applied data constructor value.
    --   This represents a value that can be matched by a case statement.
    --
    --   A 'DataValue' has the natural representation for its data type:
    --   a value, a boxed reference, or a readable reference.
  | DataValue
    { dataInfo        :: ExpInfo
    , dataCon         :: !Var
    , dataTyArgs      :: [TypM]
    , dataExTypes     :: [TypM]
    , dataFields      :: [MaybeValue]
    }

    -- | A writer value.  This is a one-parameter function that takes a
    --   pointer and initializes some data by writing into offsets from
    --   that pointer.
    --
    --   Writer values are produced by applications of data constructors
    --   that take an output pointer.  They are also produced by calls
    --   to \"copy\" and \"store\".
  | WriterValue KnownValue

    -- | A value that has been stored to memory.  The value's natural
    --   representation is included.
  | StoredValue !Repr KnownValue

-- | Get a trivial expression (a variable or literal) equivalent to this
--   known value, if possible.
--
--   If this value was chosen to be unconditionally inlined, this returns
--   the entire expression no matter how complex it is.
asTrivialValue :: KnownValue -> Maybe ExpM
asTrivialValue kv = 
  case kv
  of LitValue inf l -> Just $ ExpM $ LitE inf l 
     VarValue inf v -> Just $ ExpM $ VarE inf v
     InlinedValue _ -> Nothing
     ComplexValue (Just v) _ -> Just $ ExpM $ VarE defaultExpInfo v
     ComplexValue Nothing _ -> Nothing

-- | Record that a known value has been bound to a variable.
--   If the value is nontrivial and not already associated with a variable,
--   future calls to 'asTrivialValue' will return this variable.
setTrivialValue :: Var -> KnownValue -> KnownValue
setTrivialValue var kv =
  case kv
  of ComplexValue Nothing val -> ComplexValue (Just var) val
     _ -> kv

-- | Get the inlined expression for this value, if there is one.
asInlinedValue :: KnownValue -> Maybe ExpM
asInlinedValue kv =
  case kv
  of InlinedValue exp -> Just exp
     _ -> Nothing

assertNotInlinedValue :: KnownValue -> a -> a
assertNotInlinedValue (InlinedValue {}) _ =
  internalError "Unexpected inlined value"
assertNotInlinedValue _ x = x

assertNotInlinedValue' :: MaybeValue -> a -> a
assertNotInlinedValue' (Just (InlinedValue {})) _ =
  internalError "Unexpected inlined value"
assertNotInlinedValue' _ x = x

{-
setInlinedValue :: Var -> ExpM -> MaybeValue -> KnownValue
setInlinedValue var val kv =
  case kv
  of Just (ComplexValue Nothing _ kv') ->
       ComplexValue (Just var) (Just val) kv'
     Just kv' -> kv'
     Nothing -> InlinedValue var val

clearInlinedValue :: KnownValue -> KnownValue
clearInlinedValue (InlinedValue v _) = VarValue defaultExpInfo v
clearInlinedValue (ComplexValue v _ cv) = ComplexValue v Nothing cv
clearInlinedValue kv = kv-}

-- | Get the value stored in memory after a writer has executed.
resultOfWriterValue :: KnownValue -> MaybeValue
resultOfWriterValue (VarValue _ _) = Nothing 
resultOfWriterValue (InlinedValue _) = Nothing
resultOfWriterValue (ComplexValue _ (WriterValue kv)) = Just kv
resultOfWriterValue (ComplexValue _ (FunValue _ _)) = Nothing
resultOfWriterValue v =
  -- Other values are not valid
  internalError $ "resultOfWriterValue " ++ show (pprKnownValue v)

-- | Remove references to any of the given variables in the known value.
--   The given variables may not include data constructors.
forgetVariables :: Set.Set Var -> KnownValue -> MaybeValue
forgetVariables varset kv = forget kv
  where
    forget kv =
      case kv
      of VarValue _ v
           | v `Set.member` varset -> Nothing
           | otherwise -> Just kv
         InlinedValue e ->
           -- Al variables referenced by this value are guaranteed to be
           -- in scope.
           Just kv
         LitValue _ _ -> Just kv
         ComplexValue stored_name cv ->
           -- First eliminate variables from 'stored_name' and 'cv'
           -- individually.  Then construct a new value from what's left.
           let cv' =
                 case cv
                 of FunValue _ f
                      | varset `intersects` freeVariables f -> Nothing
                      | otherwise -> Just cv
                    DataValue { dataTyArgs = tys1
                              , dataExTypes = tys2
                              , dataFields = fields}
                      | any (`typeMentionsAny` varset) (map fromTypM tys1) ||
                        any (`typeMentionsAny` varset) (map fromTypM tys2) ->
                          Nothing
                      | otherwise ->
                          let fields' = map (>>= forget) fields
                          in Just $ cv {dataFields = fields'}
                    WriterValue kv ->
                      fmap WriterValue $ forget kv
                    StoredValue repr kv ->
                      fmap (StoredValue repr) $ forget kv
               stored_name' =
                 case stored_name
                 of Just v | v `Set.member` varset -> Nothing
                    _ -> stored_name
           in case cv'
              of Nothing ->
                   case stored_name'
                   of Nothing -> Nothing
                      Just v -> Just $ VarValue defaultExpInfo v
                 Just complex_value ->
                   Just $ ComplexValue stored_name' complex_value

-- | Pretty-print a known value
pprKnownValue :: KnownValue -> Doc
pprKnownValue kv =
  case kv
  of VarValue _ v -> pprVar v
     LitValue _ l -> pprLit l
     InlinedValue exp -> parens $ pprExp exp
     ComplexValue Nothing cv -> pprComplexValue cv
     ComplexValue (Just v) cv ->
       parens $ pprVar v <+> text "=" <+> pprComplexValue cv
                                 
pprComplexValue :: ComplexValue -> Doc
pprComplexValue cv =
  case cv
  of FunValue _ f -> pprFun f
     DataValue _ con ty_args ex_types fields ->
       let type_docs =
             map (text "@" <>) $ map (pprType . fromTypM) (ty_args ++ ex_types)
           field_docs = map pprMaybeValue fields
       in pprVar con <>
          parens (sep $ punctuate (text ",") $ type_docs ++ field_docs)
     WriterValue kv -> text "writer" <+> parens (pprKnownValue kv)
     StoredValue repr kv ->
       let repr_doc =
             case repr
             of Value -> text "val"
                Boxed -> text "box"
                Referenced -> text "ref"
       in text "stored" <+> repr_doc <+> parens (pprKnownValue kv)

pprMaybeValue :: MaybeValue -> Doc
pprMaybeValue Nothing = text "_"
pprMaybeValue (Just kv) = pprKnownValue kv

{-
-- | Is the variable mentioned in the value?
--
--   Does not check data constructors.
knownValueMentions :: KnownValue -> Var -> Bool
knownValueMentions kv search_v = undefined

-- | Is any of the variables mentioned in the value?
--
--   Does not check data constructors.
knownValueMentionsAny :: KnownValue -> Set.Set Var -> Bool

maybeValueMentions :: MaybeValue -> Var -> Bool
maybeValueMentions Nothing _ = False
maybeValueMentions (Just kv) v = knownValueMentions kv v

maybeValueMentionsAny :: MaybeValue -> Set.Set Var -> Bool
maybeValueMentionsAny Nothing _ = False
maybeValueMentionsAny (Just kv) v = knownValueMentionsAny kv v
-}

dataConValue :: ExpInfo
             -> DataType           -- ^ The data type being constructed
             -> DataConType        -- ^ The data constructor being used
             -> [TypM]             -- ^ Type arguments to the constructor
             -> [MaybeValue]       -- ^ Value arguments to the constructor
             -> MaybeValue
dataConValue inf d_type dcon_type ty_args val_args =
  trace "dataConValue" $
  dataConstructorValue inf True d_type dcon_type ty_args val_args

-- | Construct a known value for an expression that was satisfied by a 
--   pattern match, given the type arguments and matched fields.
patternValue :: ExpInfo
             -> DataType           -- ^ The data type being constructed
             -> DataConType        -- ^ The data constructor being used
             -> [TypM]             -- ^ Type arguments to the constructor
             -> [Var]              -- ^ Existential variables
             -> [MaybeValue]       -- ^ Value arguments to the constructor
             -> MaybeValue
patternValue inf d_type dcon_type ty_args ex_vars val_args =
  trace "patternValue" $
  let data_con_ty_args = ty_args ++ [TypM (VarT v) | v <- ex_vars]
  in dataConstructorValue inf False d_type dcon_type data_con_ty_args val_args

-- | Construct a known value for a data constructor application,
--   given the arguments.  The arguments may be those that were passed to 
--   a data constructor application, or those that were obtained by a
--   pattern match.
--
--   * If this data constructor is undersaturated, 'Nothing' is returned.
--
--   * If this data constructor is saturated and the data constructor does
--   not return by side effect, a 'DataValue' value is returned.
--
--   * If this data constructor is saturated (but no output pointer is
--   passed) and the data constructor returns by side effect, a 'WriterValue'
--   value is returned.
--
--   * If this data constructor is saturated and also passed an output
--   pointer, and the data constructor returns by side effect, a 'StoredValue'
--   value is returned.
dataConstructorValue :: ExpInfo
             -> Bool               -- ^ Based on constructor arguments?
             -> DataType           -- ^ The data type being constructed
             -> DataConType        -- ^ The data constructor being used
             -> [TypM]             -- ^ Type arguments to the constructor
             -> [MaybeValue]       -- ^ Value arguments to the constructor
             -> MaybeValue
dataConstructorValue inf is_constructor d_type dcon_type ty_args val_args =
  let x = dataConstructorValue' inf is_constructor d_type dcon_type ty_args val_args
  in traceShow (pprVar (dataConCon dcon_type) $$ nest 4 (vcat (map pprMaybeValue val_args))) $ traceShow (pprMaybeValue x) x

dataConstructorValue' inf is_constructor d_type dcon_type ty_args val_args
  | length ty_args /= num_expected_ty_args =
      internalError "dataConValue: Wrong number of type arguments"

  | length val_args < num_expected_args =
      Nothing                   -- Undersaturated application

  | is_referenced && is_constructor && length val_args == num_expected_args =
      -- Fully applied constructor with no output pointer
      Just $ complexKnownValue $ WriterValue data_value
  
  | length val_args == num_expected_args =
      -- Either a pattern with all arguments,
      -- or a data constructor that returns its result
      Just data_value

  | is_referenced && is_constructor && length val_args == 1 + num_expected_args =
      -- Fully applied constructor with output pointer
      Just $ complexKnownValue $ StoredValue Referenced data_value

  | otherwise = internalError "dataConValue: Too many value arguments"
  where
    is_referenced = dataTypeRepresentation d_type == Referenced

    con = dataConCon dcon_type

    (field_types, result_type) =
      instantiateDataConTypeWithExistentials dcon_type (map fromTypM ty_args)

    dcon_num_pattern_params = length (dataConPatternParams dcon_type)

    -- The number of type arguments needed to make a fully applied
    -- data constructor
    num_expected_ty_args = dcon_num_pattern_params +
                           length (dataConPatternExTypes dcon_type)

    parametric_ty_args = take dcon_num_pattern_params ty_args
    existential_ty_args = drop dcon_num_pattern_params ty_args

    -- The number of value arguments needed to make a fully applied
    -- data constructor.  This does not include the output pointer.
    num_expected_args = length (dataConPatternArgs dcon_type)

    -- The data constructor fields.  If there are more arguments, they number 
    -- one, and are the output pointer.
    field_args = take num_expected_args val_args

    -- If all type arguments and fields are present, this is the data value
    data_value =
      let fields =
            if is_constructor
            then zipWith makeConstructorDataField field_types field_args
            else zipWith makePatternDataField field_types field_args
      in complexKnownValue $
         DataValue inf con parametric_ty_args existential_ty_args fields

-- Determine the value that the field will have, given the parameter
-- that was passed for this field.
makeConstructorDataField _ Nothing = Nothing
makeConstructorDataField (field_repr ::: _) (Just field_arg) =
  case field_repr
  of ReadRT -> resultOfWriterValue field_arg
     ValRT -> Just field_arg
     BoxRT -> Just field_arg

makePatternDataField _ arg = arg

-- | Create known values for data constructors in the global type environment.
--   In particular, nullary data constructors get a 'DataValue'.
initializeKnownValues :: TypeEnv -> IntMap.IntMap KnownValue
initializeKnownValues tenv =  
  let datacons = getAllDataConstructors tenv
  in IntMap.mapMaybe make_datacon_value datacons
  where
     make_datacon_value dcon
       | null (dataConPatternParams dcon) &&
         null (dataConPatternExTypes dcon) &&
         null (dataConPatternArgs dcon) =
           let con = dataConCon dcon
               data_value = DataValue defaultExpInfo con [] [] []
           in Just $ ComplexValue (Just con) data_value
       | otherwise = Nothing
