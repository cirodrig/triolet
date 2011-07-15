{-| Known values.

Most of the simplification performed by the simplifier relies on knowing some
approximation of the run-time value of an expresion or a variable.  The
'AbsValue' data type is how we store this information.

A data value that's in the correct representation for a @case@ statement is
represented by a 'DataAV' term.  If it's
an initializer for the contents of memory, it's a 'WriterAV' term.
-}

module SystemF.KnownValue where

import qualified Data.IntMap as IntMap
import Data.Maybe
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import SystemF.Rename
import Type.Compare
import Type.Environment
import Type.Eval
import Type.Rename
import Type.Type

-- Set intersecton
s1 `intersects` s2 = not $ Set.null $ Set.intersection s1 s2

-- | A value that is known (or partially known) at compile time.
--
--   'LitAV', 'VarAV', and 'InlAV' terms are unconditionally inlined,
--   replacing future uses of the value.  An 'InlAV' never appears as a
--   component of another value; it's always associated directly with 
--   a program variable.
--
--   'HeapAV' values represent the contents of memory.
--
--   'BigAV' values contain terms that may be inlined at the discretion
--   of the simplifier, and terms that won't be inlined by the simplifier.
--   The terms that won't be inlined could still be evaluated yielding terms 
--   that the simplifier can inline.
data AbsValue =
    -- | A literal value
    LitAV ExpInfo !Lit
    
    -- | A variable value. 
    --   If the variable's value is known, a 'BigAV' is used to hold the
    --   real value.
  | VarAV ExpInfo !Var

    -- | A variable's inlined value.  The expression should be inlined
    --   wherever the variable is used.  This abstract value may not appear
    --   inside another abstract value.
  | InlAV ExpM

    -- | A complex value.  If a variable is given, the variable holds this 
    --   value.
  | BigAV !(Maybe Var) !BigAbsValue

-- | A complex value.  Complex values are not necessarily representable as
--   expressions; those that are may be inlined at the discretion of the
--   optimizer.
data BigAbsValue =
    -- | An expression that may be inlined
    ExpAV !(Maybe AbsFunValue) !ExpM
    
    -- | An abstract function value.
    --
    --   This value approximates the value of a monomorphic function.
  | AbsFunAV {-#UNPACK#-}!AbsFunValue

    -- | A partially known heap state.
  | HeapAV HeapState

    -- | A fully applied data constructor value.
    --
    --   This represents a value that can be matched by a case statement.
    --   Note that a data constructor for a bare object creates a writer,  
    --   not a regular value.
  | DataAV {-#UNPACK#-}!DataValue

    -- | A writer value.  This is a one-parameter function that takes a
    --   pointer and initializes some data by writing into offsets from
    --   that pointer.
    --
    --   Writer values are produced by applications of data constructors
    --   that take an output pointer.  They are also produced by calls
    --   to \"copy\".
    --
    --   Writer values have an equivalent 'AbsFunValue' value.
  | WriterAV !AbsValue

-- | An abstract data value.
data DataValue =
  DataValue
  { dataInfo        :: ExpInfo
  , dataValueType   :: !DataValueType
  , dataFields      :: [MaybeValue]
  }

data DataValueType =
    -- | A data constructor type, along with its type arguments.
    ConValueType
    { dataCon         :: !Var
    , dataTyArgs      :: [TypM]
    , dataExTypes     :: [TypM]
    }
    -- | An unboxed tuple type.
  | TupleValueType
    { dataTyArgs :: [TypM]
    }

-- | An abstraction of a reference to a field of an object
data RefValue = RefValue !RefBase [FieldSelector]

-- | An abstraction of a base address
newtype RefBase =
    -- | A variable bound in the program 
    VarBase Var
    deriving(Eq, Ord)

-- | A field name.  Currently uninhabited.
data FieldSelector

-- | A partially known state of memory, represented as a list of
--   (address, value) pairs.  The list should be nonempty; empty lists
--   are useless.
newtype HeapState = HeapState [(RefValue, AbsValue)]

heapState :: [(RefValue, AbsValue)] -> Maybe HeapState
heapState [] = Nothing
heapState xs = Just $ HeapState xs

-- | Find the heap state entry at the given address
lookupHeapState :: RefValue -> HeapState -> Maybe AbsValue
lookupHeapState ref (HeapState bindings) = find_binding bindings
  where
    find_binding ((addr, val):bs)
      | match addr = Just val
      | otherwise = find_binding bs
    find_binding [] = Nothing

    RefValue ref_base [] = ref

    match (RefValue base []) = base == ref_base

-- | The abstract value of a monomorphic function.
data AbsFunValue =
  AbsFunValue
  { afunInfo :: ExpInfo
  , afunParams :: [PatM]
  , afunValue :: AbsValue
  }

abstractFunction :: ExpInfo -> [PatM] -> AbsValue -> AbsFunValue
abstractFunction inf params body =
  AbsFunValue inf params body

-- | A mapping from variables to their approximate value
type AbsValues = IntMap.IntMap AbsValue

type MaybeValue = Maybe AbsValue

bigAV :: BigAbsValue -> AbsValue
bigAV = BigAV Nothing

funAV :: ExpInfo -> Maybe AbsFunValue -> FunM -> AbsValue
funAV inf val f = bigAV $ ExpAV val (ExpM (LamE inf f))

absFunAV :: AbsFunValue -> AbsValue
absFunAV f = bigAV $ AbsFunAV f

heapAV :: HeapState -> AbsValue
heapAV x = bigAV $ HeapAV x

dataAV :: DataValue -> AbsValue
dataAV x = bigAV $ DataAV x

writerAV :: AbsValue -> AbsValue
writerAV kv = bigAV (WriterAV kv)

fromBigAV :: AbsValue -> Maybe BigAbsValue
fromBigAV (BigAV _ v) = Just v
fromBigAV _ = Nothing

fromFunAV :: AbsValue -> Maybe FunM
fromFunAV (BigAV _ (ExpAV _ (ExpM (LamE _ f)))) = Just f
fromFunAV _ = Nothing


fromHeapAV :: AbsValue -> Maybe HeapState
fromHeapAV (BigAV _ (HeapAV hs)) = Just hs
fromHeapAV _ = Nothing

fromDataAV :: AbsValue -> Maybe DataValue
fromDataAV (BigAV _ (DataAV x)) = Just x
fromDataAV _ = Nothing

-- | Get a trivial expression (a variable or literal) equivalent to this
--   known value, if possible.
asTrivialValue :: AbsValue -> Maybe ExpM
asTrivialValue kv = 
  case kv
  of LitAV inf l -> Just $ ExpM $ LitE inf l 
     VarAV inf v -> Just $ ExpM $ VarE inf v
     InlAV _ -> Nothing
     BigAV (Just v) _ -> Just $ ExpM $ VarE defaultExpInfo v
     BigAV Nothing _ -> Nothing

-- | Record that a known value has been bound to a variable.
--   If the value is nontrivial and not already associated with a variable,
--   future calls to 'asTrivialValue' will return this variable.
setTrivialValue :: Var -> AbsValue -> AbsValue
setTrivialValue var kv =
  case kv
  of BigAV Nothing val -> BigAV (Just var) val
     _ -> kv

-- | Get the inlined expression for this value, if there is one.
asInlinedValue :: AbsValue -> Maybe ExpM
asInlinedValue kv =
  case kv
  of InlAV exp -> Just exp
     _ -> Nothing

assertNotInlinedValue :: AbsValue -> a -> a
assertNotInlinedValue (InlAV {}) _ =
  internalError "Unexpected inlined value"
assertNotInlinedValue _ x = x

assertNotInlinedValue' :: MaybeValue -> a -> a
assertNotInlinedValue' (Just (InlAV {})) _ =
  internalError "Unexpected inlined value"
assertNotInlinedValue' _ x = x

-- | Get the value that a writer stores into its destination.
--
--   Function-valued terms are valid writers, but we don't know what
--   they write.
resultOfWriterValue :: AbsValue -> MaybeValue
resultOfWriterValue av = 
  case av
  of BigAV _ (WriterAV kv)        -> Just kv
     BigAV _ (ExpAV (Just afv) _) -> abs_fun_value afv
     BigAV _ (AbsFunAV afv)       -> abs_fun_value afv
     VarAV {}                     -> Nothing
     InlAV {}                     -> Nothing
     BigAV _ (ExpAV Nothing _)    -> Nothing
     _ ->
       -- Other values are not valid
       internalError $ "resultOfWriterValue " ++ show (pprAbsValue av)
  where
    abs_fun_value afv
      | [param] <- afunParams afv =
        case fromHeapAV $ afunValue afv
        of Just heap_state ->
             lookupHeapState (RefValue (VarBase (patMVar param)) []) heap_state
           _ -> Nothing

forgetVariable :: Var -> AbsValue -> MaybeValue
forgetVariable v kv = forgetVariables (Set.singleton v) kv

-- | Remove references to any of the given variables in the known value.
--   The given variables may not include data constructors.
forgetVariables :: Set.Set Var -> AbsValue -> MaybeValue
forgetVariables varset kv = forget kv
  where
    data_type_mentions_vars (ConValueType _ tys1 tys2) =
      any (`typeMentionsAny` varset) (map fromTypM tys1) ||
      any (`typeMentionsAny` varset) (map fromTypM tys2)

    data_type_mentions_vars (TupleValueType tys) =
      any (`typeMentionsAny` varset) (map fromTypM tys)

    forget kv =
      case kv
      of VarAV _ v
           | v `Set.member` varset -> Nothing
           | otherwise -> Just kv
         InlAV e ->
           -- Al variables referenced by this value are guaranteed to be
           -- in scope.
           Just kv
         LitAV _ _ -> Just kv
         BigAV stored_name cv ->
           -- First eliminate variables from 'stored_name' and 'cv'
           -- individually.  Then construct a new value from what's left.
           let stored_name' =
                 case stored_name
                 of Just v | v `Set.member` varset -> Nothing
                    _ -> stored_name
           in case forget_big_value cv
              of Nothing ->
                   case stored_name'
                   of Nothing -> Nothing
                      Just v -> Just $ VarAV defaultExpInfo v
                 Just complex_value ->
                   Just $ BigAV stored_name' complex_value

    forget_big_value cv@(ExpAV mval e)
      | varset `intersects` freeVariables e = Nothing
      | otherwise = Just $ ExpAV (mval >>= forget_abs_fun) e

    forget_big_value (AbsFunAV afv) = fmap AbsFunAV (forget_abs_fun afv) 

    forget_big_value (HeapAV (HeapState states)) =
      let new_states = [(k', v') | (k, v) <- states,
                                   Just k' <- return $ forget_ref k,
                                   Just v' <- return $ forget v]
      in fmap HeapAV $ heapState new_states

    forget_big_value (DataAV dv@(DataValue { dataValueType = value_type
                                           , dataFields = fields}))
      | data_type_mentions_vars value_type = Nothing
      | otherwise =
          let fields' = map (>>= forget) fields
          in Just $ DataAV $ dv {dataFields = fields'}

    forget_big_value (WriterAV kv) =
      fmap WriterAV $ forget kv
    
    forget_abs_fun (AbsFunValue { afunInfo = inf
                                , afunParams = params
                                , afunValue = ret_val})
      | any (`typeMentionsAny` varset) (map patMType params) = Nothing
      | otherwise =
        case forget ret_val
        of Nothing -> Nothing
           Just ret_val' -> Just $ AbsFunValue inf params ret_val'

    forget_ref cv@(RefValue base fss)
      | in_varset base = Nothing
      | any field_mentions fss = Nothing
      | otherwise = Just cv
      where
        in_varset (VarBase v) = v `Set.member` varset
    
    -- Does this field mention one of the variables that should be forgotten?
    field_mentions _ = internalError "forgetValue: Unexpected field selector"

-- | Pretty-print a known value
pprAbsValue :: AbsValue -> Doc
pprAbsValue kv =
  case kv
  of VarAV _ v -> pprVar v
     LitAV _ l -> pprLit l
     InlAV exp -> parens $ pprExp exp
     BigAV Nothing cv -> pprBigAbsValue cv
     BigAV (Just v) cv ->
       parens $ pprVar v <+> text "=" <+> pprBigAbsValue cv
                                 
pprBigAbsValue :: BigAbsValue -> Doc
pprBigAbsValue cv =
  case cv
  of ExpAV Nothing e -> pprExp e
     ExpAV (Just afv) e -> parens (pprExp e <+> text "=" <+> pprAbsFun afv)
     AbsFunAV av -> pprAbsFun av
     HeapAV hs -> pprHeapState hs
     DataAV dv -> pprDataValue dv
     WriterAV kv -> text "writer" <+> parens (pprAbsValue kv)

pprAbsFun (AbsFunValue { afunInfo = inf
                       , afunParams = params
                       , afunValue = val}) =
  let params_doc = sep $ map pprPat params
      body_doc = pprAbsValue val
  in text "lambda" <+> params_doc <> text "." $$ nest 4 body_doc

pprHeapState :: HeapState -> Doc
pprHeapState (HeapState assocs) = braces $ sep $ punctuate (text ",") entries
  where
    entries =
      [pprRefValue k <+> text "|->" <+> pprAbsValue v | (k, v) <- assocs]

pprDataValue :: DataValue -> Doc
pprDataValue (DataValue _ d_type fields) =
  let field_docs = map pprMaybeValue fields
  in case d_type 
     of ConValueType con ty_args ex_types ->
          let type_docs =
                map (text "@" <>) $ map (pprType . fromTypM) (ty_args ++ ex_types)
          in pprVar con <>
             parens (sep $ punctuate (text ",") $ type_docs ++ field_docs)
        TupleValueType _ ->
          let field_docs = map pprMaybeValue fields
          in parens (sep $ punctuate (text ",") field_docs)

pprRefValue (RefValue (VarBase v) []) = pprVar v

pprMaybeValue :: MaybeValue -> Doc
pprMaybeValue Nothing = text "_"
pprMaybeValue (Just kv) = pprAbsValue kv

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
      Just $ bigAV $ WriterAV known_value
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
    -- The actual returned value might be a WriterAV of this.
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
tupleConValue :: ExpInfo -> [TypM] -> [MaybeValue] -> MaybeValue
tupleConValue inf types val_args =
  Just $ tupleValue inf types val_args

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
                  -> [TypM]
                  -> [MaybeValue]
                  -> MaybeValue
tuplePatternValue inf types val_args =
  Just $ tupleValue inf types val_args

-- | Construct a known value for a data constructor,
--   given the values of its type arguments and fields.
dataConstructorValue :: ExpInfo
             -> DataConType        -- ^ The data constructor being used
             -> [TypM]             -- ^ Type arguments to the constructor
             -> [MaybeValue]       -- ^ Value arguments to the constructor
             -> AbsValue
dataConstructorValue inf dcon_type ty_args val_args =
  bigAV $
  DataAV (DataValue { dataInfo = inf
                    , dataValueType = ConValueType
                              { dataCon = dataConCon dcon_type
                              , dataTyArgs = forall_type_args
                              , dataExTypes = exists_type_args}
                    , dataFields = val_args})
  where
    forall_type_args = take (length $ dataConPatternParams dcon_type) ty_args
    exists_type_args = drop (length $ dataConPatternParams dcon_type) ty_args

tupleValue :: ExpInfo -> [TypM] -> [MaybeValue] -> AbsValue
tupleValue inf types val_args =
  bigAV $
  DataAV (DataValue { dataInfo = inf
                    , dataValueType = TupleValueType types
                    , dataFields = val_args})

-- | An abstract environment, mapping value variables to known values.
type AbsEnv = IntMap.IntMap MaybeValue

lookupVarAbs :: Var -> AbsEnv -> Maybe MaybeValue
lookupVarAbs v e = IntMap.lookup (fromIdent $ varID v) e

-- | Substitute in an abstract value
substituteAbsValue :: AbsEnv -> AbsValue -> MaybeValue
substituteAbsValue env value =
  case value
  of VarAV _ v ->
       case lookupVarAbs v env
       of Nothing -> Just value
          Just mv -> mv
     BigAV mvar val -> fmap (BigAV mvar) (substituteBigAbsValue env val)
     _ -> Just value

substituteBigAbsValue env value =
  case value
  of AbsFunAV f -> fmap AbsFunAV $ substituteAbsFunValue env f
     HeapAV st -> fmap HeapAV $ substituteHeapState env st
     DataAV dv -> fmap DataAV $ substituteDataValue env dv
     WriterAV av -> fmap WriterAV $ substituteAbsValue env av

substituteAbsFunValue env f
  | any (`IntMap.member` env) $ map (fromIdent . varID . patMVar) $ afunParams f =
      -- Name shadowing is not allowed.
      -- Instead of aborting, we should rename bound variables to
      -- avoid shadowing.
      internalError "substituteAbsFunValue"
  | otherwise =
      -- Substitute into the body of the function
      case substituteAbsValue env (afunValue f)
      of Just v -> Just (f {afunValue = v})
         Nothing -> Nothing

substituteHeapState :: AbsEnv -> HeapState -> Maybe HeapState
substituteHeapState env (HeapState bindings) =
  heapState (mapMaybe substitute_binding bindings)
  where
    substitute_binding (addr, val) = do
      addr' <- substituteRefValue env addr
      val' <- substituteAbsValue env val
      return (addr', val')

substituteDataValue :: AbsEnv -> DataValue -> Maybe DataValue
substituteDataValue env (DataValue inf con fields) = 
  Just $ DataValue inf con (map subst_field fields)
  where
  subst_field Nothing  = Nothing
  subst_field (Just f) = substituteAbsValue env f

substituteRefValue :: AbsEnv -> RefValue -> Maybe RefValue
substituteRefValue env (RefValue base fs) = do
  -- Substitute in the base address.  Convert the substituted expression to a
  -- new base address
  RefValue new_base base_fs <-
    case base
    of VarBase v ->
         case lookupVarAbs v env
         of Nothing -> return (RefValue base [])
            Just mv -> mv >>= convertAbsValueToRefValue

  -- Substitute fields
  case fs of [] -> return (RefValue new_base base_fs)


-- | Create a reference to an object field, given an abstract value.
--   We can translate variables and built-in functions.
convertAbsValueToRefValue :: AbsValue -> Maybe RefValue
convertAbsValueToRefValue (VarAV _ v) = Just (RefValue (VarBase v) [])
convertAbsValueToRefValue _ = internalError "convertAbsValueToRefValue: Not implemented"

-- | Apply an abstract value to arguments.
--
--   Values are constructed from well-typed code, so it's an error if
--   a non-function value is applied to arguments.  Due to currying, the
--   number of arguments may be wrong.
--
--   Only 'AbsFunAV' and 'WriterAV' values can actually be evaluated.  Other
--   values result in a 'Nothing' result.
applyAbsValue :: AbsValue -> [MaybeValue] -> MaybeValue
applyAbsValue av [] = Just av
applyAbsValue av args = 
  case av
  of LitAV {} -> bad_operator

     -- TODO: Create an 'app' term that can be evaluated when a value is
     -- substituted in place of the variable
     VarAV {} -> cannot_evaluate
     InlAV {} -> cannot_evaluate
     BigAV _ (ExpAV _ _) -> cannot_evaluate
     BigAV _ (AbsFunAV afun) -> applyAbsFun afun args
     BigAV _ (WriterAV written_value) -> apply_writer written_value
     BigAV _ _ -> bad_operator
  where
    bad_operator = internalError "applyAbsValue: Operator is not a function"
    cannot_evaluate = Nothing

    -- A writer function puts its value onto the heap
    apply_writer written_value =
      case args
      of [marg] -> do
           arg <- marg
           addr <- convertAbsValueToRefValue arg -- Address to write
           hpval <- heapState [(addr, written_value)]
           return $ heapAV hpval

applyAbsFun :: AbsFunValue -> [MaybeValue] -> MaybeValue
applyAbsFun av args
  | length (afunParams av) > length args = do
    -- Fewer parameters than arguments
    let extra_params = drop (length args) $ afunParams av
        substitution = mk_subst $ zip (afunParams av) args
    new_body <- substituteAbsValue substitution (afunValue av)
    return $ absFunAV $ AbsFunValue (afunInfo av) extra_params new_body
  | otherwise = do
    let extra_args = drop (length $ afunParams av) args
        substitution = mk_subst $ zip (afunParams av) args
    new_value <- substituteAbsValue substitution (afunValue av)
    applyAbsValue new_value extra_args
  where
    -- Create a substitution from a list of (pattern, value) pairs
    mk_subst assocs =
      IntMap.fromList [(fromIdent $ varID $ patMVar p, x) | (p, x) <- assocs]

-- | Create known values for data constructors in the global type environment.
--   In particular, nullary data constructors get a 'DataAV'.
initializeKnownValues :: TypeEnv -> IntMap.IntMap AbsValue
initializeKnownValues tenv =  
  let datacons = getAllDataConstructors tenv
  in IntMap.mapMaybe make_datacon_value datacons
  where
     make_datacon_value dcon
       | null (dataConPatternParams dcon) &&
         null (dataConPatternExTypes dcon) &&
         null (dataConPatternArgs dcon) =
           let con = dataConCon dcon
               data_value = DataAV (DataValue defaultExpInfo (ConValueType con [] []) [])
           in Just $ BigAV (Just con) data_value
       | otherwise = Nothing
