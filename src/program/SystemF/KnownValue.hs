{-| Known values.

Most of the simplification performed by the simplifier relies on knowing some
approximation of the run-time value of an expresion or a variable.  The
'KnownValue' data type is how we store this information.

A data value that's in the correct representation for a @case@ statement is
represented by a 'DataValue' term.  If it's
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
    --   wherever the variable is used.
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
    --
    --   This represents a value that can be matched by a case statement.
    --   Note that a data constructor for a bare object creates a writer,  
    --   not a regular value.
  | DataValue
    { dataInfo        :: ExpInfo
    , dataValueType   :: !DataValueType
    , dataFields      :: [MaybeValue]
    }

    -- | A writer value.  This is a one-parameter function that takes a
    --   pointer and initializes some data by writing into offsets from
    --   that pointer.
    --
    --   Writer values are produced by applications of data constructors
    --   that take an output pointer.  They are also produced by calls
    --   to \"copy\".
  | WriterValue !KnownValue

data DataValueType =
    -- | A data constructor type, along with its type arguments.
    ConValueType
    { dataCon         :: !Var
    , dataTyArgs      :: [TypM]
    , dataExTypes     :: [TypM]
    }
    -- | An unboxed tuple type.
    --   It's not necessary to keep track of types.
  | TupleValueType

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

-- | Get the value that a writer stores into its destination.
--
--   Function-valued terms are valid writers, but we don't know what
--   they write.  Literals are not writers.
resultOfWriterValue :: KnownValue -> MaybeValue
resultOfWriterValue (VarValue _ _)                    = Nothing 
resultOfWriterValue (InlinedValue _)                  = Nothing
resultOfWriterValue (ComplexValue _ (WriterValue kv)) = Just kv
resultOfWriterValue (ComplexValue _ (FunValue _ _))   = Nothing
resultOfWriterValue v =
  -- Other values are not valid
  internalError $ "resultOfWriterValue " ++ show (pprKnownValue v)

forgetVariable :: Var -> KnownValue -> MaybeValue
forgetVariable v kv = forgetVariables (Set.singleton v) kv

-- | Remove references to any of the given variables in the known value.
--   The given variables may not include data constructors.
forgetVariables :: Set.Set Var -> KnownValue -> MaybeValue
forgetVariables varset kv = forget kv
  where
    data_type_mentions_vars (ConValueType _ tys1 tys2) =
      any (`typeMentionsAny` varset) (map fromTypM tys1) ||
      any (`typeMentionsAny` varset) (map fromTypM tys2)

    data_type_mentions_vars TupleValueType = False

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
                    DataValue { dataValueType = value_type
                              , dataFields = fields}
                      | data_type_mentions_vars value_type ->
                          Nothing
                      | otherwise ->
                          let fields' = map (>>= forget) fields
                          in Just $ cv {dataFields = fields'}
                    WriterValue kv ->
                      fmap WriterValue $ forget kv
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
     DataValue _ (ConValueType con ty_args ex_types) fields ->
       let type_docs =
             map (text "@" <>) $ map (pprType . fromTypM) (ty_args ++ ex_types)
           field_docs = map pprMaybeValue fields
       in pprVar con <>
          parens (sep $ punctuate (text ",") $ type_docs ++ field_docs)
     
     DataValue _ TupleValueType fields ->
       let field_docs = map pprMaybeValue fields
       in parens (sep $ punctuate (text ",") field_docs)

     WriterValue kv -> text "writer" <+> parens (pprKnownValue kv)

pprMaybeValue :: MaybeValue -> Doc
pprMaybeValue Nothing = text "_"
pprMaybeValue (Just kv) = pprKnownValue kv

-- | Construct a known value for the result of a data constructor application.
dataConValue :: ExpInfo
             -> TypeEnv
             -> DataType           -- ^ The data type being constructed
             -> DataConType        -- ^ The data constructor being used
             -> [TypM]             -- ^ Type arguments to the constructor
             -> [MaybeValue]       -- ^ Value arguments to the constructor
             -> MaybeValue
dataConValue inf tenv d_type dcon_type ty_args val_args
  | num_ty_args /= num_expected_ty_args =
      internalError "dataConValue: Wrong number of type arguments"
  | num_val_args < num_expected_val_args =
      Nothing
  | num_val_args == num_expected_val_args && not is_writer =
      Just known_value
  | num_val_args == num_expected_val_args && is_writer =
      Just $ complexKnownValue $ WriterValue known_value
  | num_val_args == num_expected_val_args + 1 && is_writer =
      Nothing
  | otherwise =
      internalError "dataConValue: Too many arguments to data constructor"
  where
    num_val_args = length val_args
    num_ty_args = length ty_args
    
    num_expected_val_args = length (dataConPatternArgs dcon_type)
    
    num_expected_ty_args =
      length (dataConPatternParams dcon_type) +
      length (dataConPatternExTypes dcon_type)
      
    -- If the data type is naturally represented as a bare reference,
    -- then the data constructor is a writer
    is_writer = dataTypeKind d_type == BareK

    -- This is the value created by the data constructor application,
    -- provided the data constructor is applied to all arguments.
    --
    -- The actual returned value might be a WriterValue of this.
    known_value =
      dataConstructorValue inf dcon_type ty_args reader_val_args
      where
        -- Convert arguments from writer values
        reader_val_args =
          zipWith from_writer (dataConFieldKinds tenv dcon_type) val_args
        
        -- Convert a data constructor argument.
        -- If the type is bare, convert from a writer to a non-writer value.
        -- Otherwise, leave the argument alone.
        from_writer :: BaseKind -> MaybeValue -> MaybeValue
        from_writer _     Nothing            = Nothing
        from_writer BareK (Just known_value) = resultOfWriterValue known_value
        from_writer _     mv                 = mv

-- | Construct a known value for an unboxed tuple.
--
--   All fields of an unboxed tuple are value or boxed, so we don't need to
--   deal with the writer/value distinction.
tupleConValue :: ExpInfo -> [MaybeValue] -> MaybeValue
tupleConValue inf val_args = Just $ tupleValue inf val_args

-- | Construct a known value for an expression that was satisfied by a 
--   pattern match, given the type arguments and matched fields.
--
--   Initializer values should not be passed for fields.
patternValue :: ExpInfo
             -> TypeEnv
             -> DataType           -- ^ The data type being constructed
             -> DataConType        -- ^ The data constructor being used
             -> [TypM]             -- ^ Type arguments to the constructor
             -> [Var]              -- ^ Existential variables
             -> [MaybeValue]       -- ^ Fields of the constructor
             -> MaybeValue
patternValue inf tenv d_type dcon_type ty_args ex_vars val_args
  | length ty_args /= length (dataConPatternParams dcon_type) =
      internalError "patternValue: Wrong number of type arguments"
  | length ex_vars /= length (dataConPatternExTypes dcon_type) =
      internalError "patternValue: Wrong number of existential types"
  | length val_args /= length (dataConPatternArgs dcon_type) =
      internalError "patternValue: Wrong number of fields"
  | otherwise =
      Just $ dataConstructorValue inf dcon_type data_con_ty_args val_args
  where
    data_con_ty_args = ty_args ++ [TypM (VarT v) | v <- ex_vars]

tuplePatternValue :: ExpInfo
                  -> [MaybeValue]
                  -> MaybeValue
tuplePatternValue inf val_args = Just $ tupleValue inf val_args

-- | Construct a known value for a data constructor,
--   given the values of its type arguments and fields.
dataConstructorValue :: ExpInfo
             -> DataConType        -- ^ The data constructor being used
             -> [TypM]             -- ^ Type arguments to the constructor
             -> [MaybeValue]       -- ^ Value arguments to the constructor
             -> KnownValue
dataConstructorValue inf dcon_type ty_args val_args =
  ComplexValue Nothing $
  DataValue { dataInfo = inf
            , dataValueType = ConValueType
                              { dataCon = dataConCon dcon_type
                              , dataTyArgs = forall_type_args
                              , dataExTypes = exists_type_args}
            , dataFields = val_args}
  where
    forall_type_args = take (length $ dataConPatternParams dcon_type) ty_args
    exists_type_args = drop (length $ dataConPatternParams dcon_type) ty_args

tupleValue :: ExpInfo -> [MaybeValue] -> KnownValue
tupleValue inf val_args =
  ComplexValue Nothing $
  DataValue { dataInfo = inf
            , dataValueType = TupleValueType
            , dataFields = val_args}

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
               data_value = DataValue defaultExpInfo (ConValueType con [] []) []
           in Just $ ComplexValue (Just con) data_value
       | otherwise = Nothing
