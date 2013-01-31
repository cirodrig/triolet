{-| Initialization of symbols used in the frontend.

The 'setupTypeEnvironment' function performs initialization in three stages.

1. Create type constructors and initialize the global array of builtins so
   that the 'builtinTyCon' function may be used.

2. Create type assignments for type constructors.  This must be done as a
   separate step, because type functions and classes can contain references 
   to other type constructors.

3. Create variables and their type assignments.
-}
module Untyped.InitializeBuiltins2
       (setupTypeEnvironment, dumpTypeEnvironment)
where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace
  
import Common.Error
import Common.Identifier
import Common.Label
import Common.Supply
import Builtins.Builtins
import qualified Type.Environment as SF
import qualified Type.Eval as SF
import qualified Type.Type as SF
import Untyped.Builtins2
import Untyped.Kind
import Untyped.Type
import Untyped.TypeUnif
import Untyped.TIExp
import Untyped.TIMonad
import Untyped.Unif
import Untyped.Variable

-- | A mapping from System F variables to 'TyCon's
type TyConMap = Map.Map SF.Var TyCon

lookupBuiltinCon :: BuiltinThing -> TyConMap -> HMType
lookupBuiltinCon thing m =
  case Map.lookup (coreBuiltin thing) m
  of Just v -> ConTy v
     Nothing -> internalError $ "lookupBuiltinThing: Not defined:" ++ show (coreBuiltin thing)

lookupBuiltinVar :: SF.Var -> TyConMap -> HMType
lookupBuiltinVar v m =
  case Map.lookup v m
  of Just v -> ConTy v
     Nothing -> internalError $ "lookupBuiltinThing: Not defined:" ++ show v

type InitM a = MaybeT SF.TypeEvalM a

runInitM = runMaybeT

reduceSF :: SF.Type -> InitM SF.Type
reduceSF t = lift (SF.reduceToWhnf t)

-- | Helper function to create polymorphic types.
--   System F type variables are _not_ added to the type environment.
polymorphic :: [Kind] -> ([TyCon] -> InitM (Constraint, a))
            -> InitM (Qualified a)
polymorphic ks f = do
  vs <- lift $ mapM (newTyVar Nothing) ks
  (c, x) <- f vs
  return $ Qualified vs c x

instancePredicate :: BuiltinTyCon -> HMType -> Predicate
instancePredicate tc ty = IsInst (builtinTyCon tc) ty

monomorphicClassInstance :: HMType -> [SF.Var]
                         -> Qualified (Instance ClassInstance)
monomorphicClassInstance head methods =
  return $ Instance head (MethodsInstance methods)

global_mzero = mzero

-------------------------------------------------------------------------------
-- Type translation from System F to frontend

-- | Convert a fully boxed System F kind to a frontend kind.
--   Return 'Nothing' if it can't be converted.
frontendKind :: SF.Kind -> InitM Kind
frontendKind sf_kind = reduceSF sf_kind >>= examine
  where
    examine (SF.VarT v)
      | v == SF.boxV = return Star

    examine (SF.FunT k1 k2) = do
      k1' <- frontendKind k1
      k2' <- frontendKind k2
      return $ k1' :-> k2'

    examine _ = mzero

frontendTypes tc_map sf_types = mapM (frontendType tc_map) sf_types

-- | Convert a fully boxed System F type to a frontend monotype.
--   Return 'Nothing' if it can't be converted.
frontendType :: TyConMap -> SF.Type -> InitM HMType
frontendType tc_map sf_type = do
  ty' <- reduceSF sf_type
  case ty' of
    -- SF.FunT _ _ handled by this case
    _ | (dom@(_:_), rng) <- SF.fromFunType ty' -> do
          -- Create a function type
          dom' <- frontendTypes tc_map dom
          rng' <- frontendType tc_map rng
          return $ functionTy dom' rng'

    SF.VarT v ->
      case Map.lookup v tc_map
      of Just tc 
           | tyConClass tc == TCCCon || 
             tyConClass tc == TCCVar -> return $ ConTy tc

         -- Unknown types are not representable in frontend.
         -- Dictionary types are also not representable.
         -- Unsaturated type functions are not representable.
         Nothing -> mzero

    -- Examine application terms; some cases are handled specially
    SF.AppT {} ->
      case SF.fromTypeApp ty'
      of (SF.VarT op_var, args)
           | Just tc <- Map.lookup op_var tc_map, tyConClass tc == TCCFun -> do
               -- Type function application.
               -- Create an application term.
               args' <- frontendTypes tc_map args
               return $ appTyCon tc args'
           | isTupleTypeCon op_var -> do
               let op | op_var `isCoreBuiltin` The_Tuple2 = TupleTy 2
                      | op_var `isCoreBuiltin` The_Tuple3 = TupleTy 3
                      | op_var `isCoreBuiltin` The_Tuple4 = TupleTy 4
                      | otherwise =
                          internalError "frontendType: Unhandled tuple constructor"
               args' <- frontendTypes tc_map args
               return $ appTys op args'

           -- Hack to translate @Stream1@ -> @iter list_dim@
           | op_var `isCoreBuiltin` The_Stream1 -> do
               let op = ConTy (builtinTyCon TheTC_iter) @@
                        ConTy (builtinTyCon TheTC_list_dim)
               args' <- frontendTypes tc_map args
               return $ appTys op args'

         (op, args) -> do
           op' <- frontendType tc_map op
           args' <- frontendTypes tc_map args
           return $ appTys op' args'

    SF.AnyT k -> AnyTy `liftM` frontendKind k

    SF.CoT k -> mzero           -- Equality constraints are not representable
    SF.LamT _ _ -> mzero
    SF.AllT _ _ -> mzero        -- Not a monotype
    SF.IntT _ -> mzero
    SF.UTupleT _ -> mzero
  where
    -- mzero = trace ("frontendType failed " ++ show (SF.pprType sf_type)) global_mzero

-- | Convert a fully boxed System F type to a frontend predicate.
--   Return 'Nothing' if it can't be converted.
frontendPredicate :: TyConMap -> SF.Type -> InitM Predicate
frontendPredicate tc_map sf_type = do
  sf_type' <- reduceSF sf_type
  case SF.fromTypeApp sf_type' of
    (SF.VarT op_var, args) ->
      case Map.lookup op_var tc_map
      of Just op_tycon | tyConClass op_tycon == TCCCls ->
           dictionary_constraint op_tycon args
         _ -> mzero
    (SF.CoT k, [t1, t2]) ->
      equality_constraint k t1 t2 
    _ -> mzero
  where
    dictionary_constraint dict_con [arg] = do
      arg' <- frontendType tc_map arg
      return $ IsInst dict_con arg'

    equality_constraint k t1 t2 = do
      k' <- frontendKind k
      t1' <- frontendType tc_map t1
      t2' <- frontendType tc_map t2
      return $ IsEqual t1' t2'

-- | Extract all @forall@-bound variables from the head of a type
withForallParams :: TyConMap -> SF.Type
                 -> (TyConMap -> [TyCon] -> SF.Type -> InitM a)
                 -> InitM a
withForallParams tc_map sf_type cont = reduceSF sf_type >>= examine
  where
    examine (SF.AllT (a SF.::: k) rng) = SF.assume a k $ do
      (a', tc_map') <- translateTyVar tc_map a
      withForallParams tc_map' rng (\tcm bs -> cont tcm (a':bs))

    examine t = cont tc_map [] t

-- | Extract the constraint from the head of a function type
frontendConstraint :: TyConMap -> SF.Type -> InitM (Constraint, SF.Type)
frontendConstraint tc_map sf_type = extract_predicates [] sf_type 
  where
    -- Extract predicates one at a time.  Build a reversed list of predicates.
    extract_predicates cst ty = do
      -- Check if the type is of the form @P -> t@ for some predicate type @P@
      ty' <- reduceSF ty
      case ty' of
        dom `SF.FunT` rng ->
          let get_predicate = do
                prd <- frontendPredicate tc_map dom
                extract_predicates (prd : cst) rng
          in get_predicate `mplus` finish cst ty'
        _ -> finish cst ty'

    finish cst ty = return (reverse cst, ty)

-- | Create a type scheme
frontendTyScheme :: TyConMap -> SF.Type -> InitM TyScheme
frontendTyScheme tc_map sf_type =
  -- Extract parameters 
  withForallParams tc_map sf_type $ \tc_map' params sf_type' -> do
    -- Extract class constraints
    (cst, sf_type'') <- frontendConstraint tc_map' sf_type'
    monotype <- frontendType tc_map' sf_type''
    return $ Qualified params cst monotype

-- | A data structure field being analyzed for a class signature
data ClassSigField =
    CSP Predicate               -- ^ Field type is a predicate
  | CSM TyScheme                -- ^ Field type is a type scheme
  | CSX                         -- ^ Unrecognized field type

-- | Create a class signature from a class dictionary's type constructor 
--   and data constructor
frontendClassSignature :: TyConMap -> Bool -> SF.DataConType
                       -> InitM (Qualified [ClassMethod])
frontendClassSignature tc_map abstract dcon_type =
  SF.assumeBinders sf_params $ do
    (params', tc_map') <- translateTyVars tc_map $ map SF.binderVar sf_params

    -- Convert fields to predicates and types
    field_types <- mapM (convert_field tc_map') $ SF.dataConFields dcon_type
    (constraint, methods) <- MaybeT $ return $ split_fields field_types

    let method_list = map ClassMethod methods
    return $ Qualified params' constraint method_list
  where
    data_type = SF.dataConType dcon_type
    sf_params = SF.dataTypeParams data_type

    convert_field tc_map (t, _) =
      (CSP `liftM` frontendPredicate tc_map t) `mplus`
      (CSM `liftM` frontendTyScheme tc_map t) `mplus`
      (return CSX)

    -- Split a list of field types into predicates and field types.
    -- Predicates must precede field types.
    split_fields :: [ClassSigField] -> Maybe (Constraint, [TyScheme])
    split_fields fs = get_predicates id fs
      where
        get_predicates ps (CSP p : fs) = get_predicates (ps . (p:)) fs
        get_predicates ps fs = do
          -- If this is an abstract class, ignore the class methods
          methods <- if abstract then Just [] else get_fields id fs
          return (ps [], methods)

        get_fields ts (CSM t : fs) = get_fields (ts . (t:)) fs
        get_fields ts (_ : _)      = Nothing
        get_fields ts []           = Just (ts [])

-- | Decide whether the range of a core kind is boxed.
--
--   Use the given type environment as the type environment for
--   reduction.
isBoxedKind :: SF.TypeEnv
            -> SF.Kind
            -> InitM Bool
isBoxedKind tenv sf_kind = lift $ SF.TypeEvalM $ \supply _ ->
  SF.runTypeEvalM (examine sf_kind) supply tenv
  where
    examine k = do
      k' <- SF.reduceToWhnf k
      case k' of
        SF.VarT v | v == SF.boxV -> return True
                  | otherwise    -> return False
        SF.FunT _ rng -> examine rng
        _ -> return False

-------------------------------------------------------------------------------
-- Type constructor initialization

data TyConInitializer =
    TyConInitializer
  | TyFamInitializer (TyConMap -> InitM (Instances TyFamilyInstance))
    -- | A type class initializer.  
    --
    --   The boolean flag indicates whether the class is abstract.
    --   The frontend cannot create data or case expressions of
    --   abstract class dictionaries.  Abstract classes have empty
    --   method lists and abstract instances.
  | TyClsInitializer Bool (TyConMap -> InitM (Instances ClassInstance))

initializerClass :: TyConInitializer -> TyConClass
initializerClass (TyConInitializer {}) = TCCCon
initializerClass (TyFamInitializer {}) = TCCFun
initializerClass (TyClsInitializer {}) = TCCCls

tyConInitializers :: [(BuiltinTyCon, Either SF.Var BuiltinThing, TyConInitializer)]
tyConInitializers =
  [(c, t, TyConInitializer) | (c, t) <- con_initializers] ++
  [(c, Right t, TyFamInitializer f) | (c, t, f) <- fam_initializers] ++
  [(c, Right t, TyClsInitializer b f) | (c, t, b, f) <- cls_initializers]
  where
    con_initializers =
      [ (TheTC_int,              Left SF.intV)
      , (TheTC_float,            Left SF.floatV)
      , (TheTC_bool,             Right The_bool)
      , (TheTC_NoneType,         Right The_NoneType)
      , (TheTC_SliceObject,      Right The_SliceObject)
      , (TheTC_StuckRef,         Right The_StuckRef)
      , (TheTC_iter,             Right The_Stream)
      , (TheTC_list,             Right The_list)
      , (TheTC_array0,           Right The_array0)
      , (TheTC_array1,           Right The_array1)
      , (TheTC_array2,           Right The_array2)
      , (TheTC_array3,           Right The_array3)
      , (TheTC_blist,            Right The_blist)
      , (TheTC_barray1,          Right The_barray1)
      , (TheTC_barray2,          Right The_barray2)
      , (TheTC_barray3,          Right The_barray3)
      , (TheTC_Maybe,            Right The_Maybe)
      , (TheTC_intset,           Right The_intset)
      , (TheTC_llist,            Right The_llist)
      , (TheTC_list_dim,         Right The_list_dim)
      , (TheTC_dim0,             Right The_dim0)
      , (TheTC_dim1,             Right The_dim1)
      , (TheTC_dim2,             Right The_dim2)
      , (TheTC_dim3,             Right The_dim3)
      , (TheTC_view,             Right The_view)
      , (TheTC_Scatter,          Right The_Scatter)
      ]

    fam_initializers =
      [ (TheTC_shape,            The_shape,            shapeTyFamily)
      , (TheTC_index,            The_index,            indexTyFamily)
      , (TheTC_slice,            The_slice,            sliceTyFamily)
      , (TheTC_cartesianDomain,  The_cartesianDomain,  cartesianTyFamily)
      ]

    cls_initializers =
      [ (TheTC_Repr,           The_Repr,             True,  reprClass)
      , (TheTC_Eq,             The_EqDict,           False, eqClass)
      , (TheTC_Ord,            The_OrdDict,          False, ordClass)
      , (TheTC_Traversable,    The_TraversableDict,  False, traversableClass)
      , (TheTC_Shape,          The_ShapeDict,        False, shapeClass)
      , (TheTC_Indexable,      The_IndexableDict,    False, indexableClass)
      , (TheTC_Additive,       The_AdditiveDict,     False, additiveClass)
      , (TheTC_Multiplicative, The_MultiplicativeDict, False, multiplicativeClass)
      , (TheTC_Remainder,      The_RemainderDict,    False, remainderClass)
      , (TheTC_Fractional,     The_FractionalDict,   False, fractionalClass)
      , (TheTC_Floating,       The_FloatingDict,     False, floatingClass)
      , (TheTC_Cartesian,      The_CartesianDict,    False, cartesianClass)
        {- TODO: Vector -}
      ]

shapeTyFamily, indexTyFamily, sliceTyFamily, cartesianTyFamily ::
  TyConMap -> InitM (Instances TyFamilyInstance)

shapeTyFamily tc_map = do
  let instances = [let container = lookupBuiltinCon x tc_map
                       shape = lookupBuiltinCon y tc_map
                   in return $ Instance container $ TyFamilyInstance shape
                  | (x, y) <- insts]
  view_instance <-
    polymorphic [Star] $ \ [sh] ->
    let head = ConTy (builtinTyCon TheTC_view) @@ ConTy sh
        inst = TyFamilyInstance (ConTy sh)
    in return ([], Instance head inst)
  iter_instance <-
    polymorphic [Star] $ \ [sh] ->
    let head = ConTy (builtinTyCon TheTC_iter) @@ ConTy sh
        inst = TyFamilyInstance (ConTy sh)
    in return ([], Instance head inst)
  return $ view_instance : iter_instance : instances
  where
    insts = [(The_list, The_list_dim),
             (The_blist, The_list_dim),
             (The_array1, The_dim1),
             (The_barray1, The_dim1),
             (The_array2, The_dim2),
             (The_barray2, The_dim2),
             (The_array3, The_dim3),
             (The_barray3, The_dim3),
             (The_llist, The_list_dim)]

indexTyFamily tc_map = do
  let instances = [let container = lookupBuiltinCon x tc_map
                   in return $ Instance container $ TyFamilyInstance shape
                  | (x, shape) <- insts]
  return instances
  where
    int = lookupBuiltinVar SF.intV tc_map
    tuple2 = TupleTy 2 @@ int @@ int
    tuple3 = TupleTy 3 @@ int @@ int @@ int
    insts = [(The_list_dim, int),
             (The_dim1, int),
             (The_dim2, tuple2),
             (The_dim3, tuple3)]

sliceTyFamily tc_map = do
  let instances = [let container = lookupBuiltinCon x tc_map
                   in return $ Instance container $ TyFamilyInstance shape
                  | (x, shape) <- insts]
  return instances
  where
    slice = lookupBuiltinCon The_SliceObject tc_map
    tuple2 = TupleTy 2 @@ slice @@ slice
    tuple3 = TupleTy 3 @@ slice @@ slice @@ slice
    insts = [(The_list_dim, slice),
             (The_dim1, slice),
             (The_dim2, tuple2),
             (The_dim3, tuple3)]

cartesianTyFamily tc_map = do
  let instances = [let shape = lookupBuiltinCon x tc_map
                   in return $ Instance container $ TyFamilyInstance shape
                  | (container, x) <- insts]
  return instances
  where
    int = lookupBuiltinVar SF.intV tc_map
    tuple2 = TupleTy 2 @@ int @@ int
    tuple3 = TupleTy 3 @@ int @@ int @@ int
    insts = [(lookupBuiltinCon The_NoneType tc_map, The_dim0),
             (int, The_dim1),
             (tuple2, The_dim2),
             (tuple3, The_dim3)]

reprClass tc_map = do
  let instances1 =
        [return $ Instance head (AbstractClassInstance (coreBuiltin inst_var) [])
        | (head, inst_var) <- monomorphic_instances]
  instances2 <-
    sequence [polymorphic [Star] $ \ [a] ->
               let head = ConTy (builtinTyCon tycon) @@ ConTy a
                   inst = AbstractClassInstance (coreBuiltin repr_fun) [ConTy a]
               in return ([], Instance head inst)
             | (tycon, repr_fun) <- container_instances]
  instances3 <- mapM mk_boxed_instance boxed_instances
  maybe_instance <-
    polymorphic [Star] $ \ [a] ->
    let head = ConTy (builtinTyCon TheTC_Maybe) @@ ConTy a
        inst = AbstractClassInstance (coreBuiltin The_repr_Maybe) [ConTy a]
        cst = [instancePredicate TheTC_Repr (ConTy a)]
    in return (cst, Instance head inst)
  tuple2_instance <-
    polymorphic [Star, Star] $ \ [a, b] ->
    let head = TupleTy 2 @@ ConTy a @@ ConTy b
        inst = AbstractClassInstance (tupleReprCon 2) [ConTy a, ConTy b]
        cst = [instancePredicate TheTC_Repr (ConTy a),
               instancePredicate TheTC_Repr (ConTy b)]
    in return (cst, Instance head inst)
  tuple3_instance <-
    polymorphic [Star, Star, Star] $ \ [a, b, c] ->
    let head = TupleTy 3 @@ ConTy a @@ ConTy b @@ ConTy c
        inst = AbstractClassInstance (tupleReprCon 3) [ConTy a, ConTy b, ConTy c]
        cst = [instancePredicate TheTC_Repr (ConTy a),
               instancePredicate TheTC_Repr (ConTy b),
               instancePredicate TheTC_Repr (ConTy c)]
    in return (cst, Instance head inst)
  tuple4_instance <-
    polymorphic [Star, Star, Star, Star] $ \ [a, b, c, d] ->
    let head = TupleTy 4 @@ ConTy a @@ ConTy b @@ ConTy c @@ ConTy d
        inst = AbstractClassInstance (tupleReprCon 4) [ConTy a, ConTy b, ConTy c, ConTy d]
        cst = [instancePredicate TheTC_Repr (ConTy a),
               instancePredicate TheTC_Repr (ConTy b),
               instancePredicate TheTC_Repr (ConTy c),
               instancePredicate TheTC_Repr (ConTy d)]
    in return (cst, Instance head inst)
  return $
    [maybe_instance, tuple2_instance, tuple3_instance, tuple4_instance] ++
    instances1 ++ instances2 ++ instances3
  where
    monomorphic_instances =
      [(lookupBuiltinVar SF.intV tc_map, The_repr_int),
       (lookupBuiltinVar SF.floatV tc_map, The_repr_float),
       (lookupBuiltinCon The_bool tc_map, The_repr_bool),
       (lookupBuiltinCon The_NoneType tc_map, The_repr_NoneType),
       (lookupBuiltinCon The_SliceObject tc_map, The_repr_SliceObject),
       (lookupBuiltinCon The_intset tc_map, The_repr_intset)]

    -- Instances for bare container types whose representation is
    -- independent of their contents
    container_instances =
      [(TheTC_StuckRef, The_repr_StuckRef),
       (TheTC_list, The_repr_list),
       (TheTC_array1, The_repr_array1),
       (TheTC_array2, The_repr_array2),
       (TheTC_array3, The_repr_array3),
       (TheTC_barray1, The_repr_barray1),
       (TheTC_barray2, The_repr_barray2),
       (TheTC_barray3, The_repr_barray3)]

    -- Instances for boxed types.
    boxed_instances =
      [The_list_dim, The_dim1, The_dim2, The_dim3,
       The_Stream, The_view, The_Scatter]

    -- Create an abstract Repr instance for a boxed type.
    -- The instance is parameterized over the boxed type's type parameters.
    mk_boxed_instance thing = do
      -- Look up this type constructor and its kind
      let tc@(ConTy tycon) = lookupBuiltinCon thing tc_map
          (dom, rng) = fromArrowKind $ tyConKind tycon

      -- Create a polymorphic instance
      polymorphic dom $ \ty_args ->
        let head = tc `appTys` map ConTy ty_args 
            inst = AbstractClassInstance (coreBuiltin The_repr_Box) [head]
        in return ([], Instance head inst)

eqClass tc_map = do
  let int_instance =
        monomorphicClassInstance (lookupBuiltinVar SF.intV tc_map)
        [coreBuiltin The_EqDict_int_eq,
         coreBuiltin The_EqDict_int_ne]
  let float_instance =
        monomorphicClassInstance (lookupBuiltinVar SF.floatV tc_map)
        [coreBuiltin The_EqDict_float_eq,
         coreBuiltin The_EqDict_float_ne]
  tuple2_instance <-
    polymorphic [Star, Star] $ \ [a, b] ->
    let head = TupleTy 2 @@ ConTy a @@ ConTy b
        body = MethodsInstance [coreBuiltin The_EqDict_Tuple2_eq,
                                coreBuiltin The_EqDict_Tuple2_ne]
        cst = [instancePredicate TheTC_Eq (ConTy a),
               instancePredicate TheTC_Eq (ConTy b)]
    in return (cst, Instance head body)
  tuple3_instance <-
    polymorphic [Star, Star, Star] $ \ [a, b, c] ->
    let head = TupleTy 3 @@ ConTy a @@ ConTy b @@ ConTy c
        body = MethodsInstance [coreBuiltin The_EqDict_Tuple3_eq,
                                coreBuiltin The_EqDict_Tuple3_ne]
        cst = [instancePredicate TheTC_Eq (ConTy a),
               instancePredicate TheTC_Eq (ConTy b),
               instancePredicate TheTC_Eq (ConTy c)]
    in return (cst, Instance head body)

  return [int_instance, float_instance, tuple2_instance, tuple3_instance]

ordClass tc_map = do
  let int_instance =
        monomorphicClassInstance (lookupBuiltinVar SF.intV tc_map)
        [coreBuiltin The_OrdDict_int_lt,
         coreBuiltin The_OrdDict_int_le,
         coreBuiltin The_OrdDict_int_gt,
         coreBuiltin The_OrdDict_int_ge]
  let float_instance =
        monomorphicClassInstance (lookupBuiltinVar SF.floatV tc_map)
        [coreBuiltin The_OrdDict_float_lt,
         coreBuiltin The_OrdDict_float_le,
         coreBuiltin The_OrdDict_float_gt,
         coreBuiltin The_OrdDict_float_ge]
  tuple2_instance <-
    polymorphic [Star, Star] $ \ [a, b] ->
    let head = TupleTy 2 @@ ConTy a @@ ConTy b
        body = MethodsInstance [coreBuiltin The_OrdDict_Tuple2_lt,
                                coreBuiltin The_OrdDict_Tuple2_le,
                                coreBuiltin The_OrdDict_Tuple2_gt,
                                coreBuiltin The_OrdDict_Tuple2_ge]
        cst = [instancePredicate TheTC_Ord (ConTy a),
               instancePredicate TheTC_Ord (ConTy b)]
    in return (cst, Instance head body)

  return [int_instance, float_instance, tuple2_instance]

traversableClass tc_map = do
  let instances1 = [monomorphicClassInstance head methods
                   | (head, methods) <- monomorphic_instances]
  iter_instance <- polymorphic [Star] $ \ [sh] ->
    let head = ConTy (builtinTyCon TheTC_iter) @@ ConTy sh
        body = MethodsInstance [coreBuiltin The_TraversableDict_Stream_traverse,
                                coreBuiltin The_TraversableDict_Stream_build]
    in return ([], Instance head body)

  return $ [iter_instance] ++ instances1
  where
    monomorphic_instances =
      [(ConTy $ builtinTyCon TheTC_list,
        [coreBuiltin The_TraversableDict_list_traverse,
         coreBuiltin The_TraversableDict_list_build]),
       (ConTy $ builtinTyCon TheTC_blist,
        [coreBuiltin The_TraversableDict_blist_traverse,
         coreBuiltin The_TraversableDict_blist_build]),
       (ConTy $ builtinTyCon TheTC_array1,
        [coreBuiltin The_TraversableDict_array1_traverse,
         coreBuiltin The_TraversableDict_array1_build]),
       (ConTy $ builtinTyCon TheTC_array2,
        [coreBuiltin The_TraversableDict_array2_traverse,
         coreBuiltin The_TraversableDict_array2_build]),
       (ConTy $ builtinTyCon TheTC_array3,
        [coreBuiltin The_TraversableDict_array3_traverse,
         coreBuiltin The_TraversableDict_array3_build]),
       (ConTy $ builtinTyCon TheTC_barray1,
        [coreBuiltin The_TraversableDict_barray1_traverse,
         coreBuiltin The_TraversableDict_barray1_build]),
       (ConTy $ builtinTyCon TheTC_barray2,
        [coreBuiltin The_TraversableDict_barray2_traverse,
         coreBuiltin The_TraversableDict_barray2_build]),
       (ConTy $ builtinTyCon TheTC_barray3,
        [coreBuiltin The_TraversableDict_barray3_traverse,
         coreBuiltin The_TraversableDict_barray3_build]),
       (ConTy (builtinTyCon TheTC_view) @@ ConTy (builtinTyCon TheTC_list_dim),
        [coreBuiltin The_TraversableDict_view_list_dim_traverse,
         coreBuiltin The_TraversableDict_view_list_dim_build]),
       (ConTy (builtinTyCon TheTC_view) @@ ConTy (builtinTyCon TheTC_dim1),
        [coreBuiltin The_TraversableDict_view_dim1_traverse,
         coreBuiltin The_TraversableDict_view_dim1_build]),
       (ConTy (builtinTyCon TheTC_view) @@ ConTy (builtinTyCon TheTC_dim2),
        [coreBuiltin The_TraversableDict_view_dim2_traverse,
         coreBuiltin The_TraversableDict_view_dim2_build]),
       (ConTy (builtinTyCon TheTC_view) @@ ConTy (builtinTyCon TheTC_dim3),
        [coreBuiltin The_TraversableDict_view_dim3_traverse,
         coreBuiltin The_TraversableDict_view_dim3_build])]

shapeClass tc_map = do
  let instances =
        [monomorphicClassInstance head methods
        | (head, methods) <- monomorphic_instances]
  return instances
  where
    monomorphic_instances =
      [(ConTy (builtinTyCon TheTC_list_dim),
        [coreBuiltin The_ShapeDict_list_dim_member,
         coreBuiltin The_ShapeDict_list_dim_intersect,
         coreBuiltin The_ShapeDict_list_dim_flatten,
         coreBuiltin The_ShapeDict_list_dim_generate,
         coreBuiltin The_ShapeDict_list_dim_map,
         coreBuiltin The_ShapeDict_list_dim_zipWith,
         coreBuiltin The_ShapeDict_list_dim_zipWith3,
         coreBuiltin The_ShapeDict_list_dim_zipWith4,
         coreBuiltin The_ShapeDict_list_dim_slice]),
       (ConTy (builtinTyCon TheTC_dim0),
        [coreBuiltin The_ShapeDict_dim0_member,
         coreBuiltin The_ShapeDict_dim0_intersect,
         coreBuiltin The_ShapeDict_dim0_flatten,
         coreBuiltin The_ShapeDict_dim0_generate,
         coreBuiltin The_ShapeDict_dim0_map,
         coreBuiltin The_ShapeDict_dim0_zipWith,
         coreBuiltin The_ShapeDict_dim0_zipWith3,
         coreBuiltin The_ShapeDict_dim0_zipWith4,
         coreBuiltin The_ShapeDict_dim0_slice]),
       (ConTy (builtinTyCon TheTC_dim1),
        [coreBuiltin The_ShapeDict_dim1_member,
         coreBuiltin The_ShapeDict_dim1_intersect,
         coreBuiltin The_ShapeDict_dim1_flatten,
         coreBuiltin The_ShapeDict_dim1_generate,
         coreBuiltin The_ShapeDict_dim1_map,
         coreBuiltin The_ShapeDict_dim1_zipWith,
         coreBuiltin The_ShapeDict_dim1_zipWith3,
         coreBuiltin The_ShapeDict_dim1_zipWith4,
         coreBuiltin The_ShapeDict_dim1_slice]),
       (ConTy (builtinTyCon TheTC_dim2),
        [coreBuiltin The_ShapeDict_dim2_member,
         coreBuiltin The_ShapeDict_dim2_intersect,
         coreBuiltin The_ShapeDict_dim2_flatten,
         coreBuiltin The_ShapeDict_dim2_generate,
         coreBuiltin The_ShapeDict_dim2_map,
         coreBuiltin The_ShapeDict_dim2_zipWith,
         coreBuiltin The_ShapeDict_dim2_zipWith3,
         coreBuiltin The_ShapeDict_dim2_zipWith4,
         coreBuiltin The_ShapeDict_dim2_slice]),
       (ConTy (builtinTyCon TheTC_dim3),
        [coreBuiltin The_ShapeDict_dim3_member,
         coreBuiltin The_ShapeDict_dim3_intersect,
         coreBuiltin The_ShapeDict_dim3_flatten,
         coreBuiltin The_ShapeDict_dim3_generate,
         coreBuiltin The_ShapeDict_dim3_map,
         coreBuiltin The_ShapeDict_dim3_zipWith,
         coreBuiltin The_ShapeDict_dim3_zipWith3,
         coreBuiltin The_ShapeDict_dim3_zipWith4,
         coreBuiltin The_ShapeDict_dim3_slice])]

indexableClass tc_map = do
  let instances =
        [monomorphicClassInstance head methods
        | (head, methods) <- monomorphic_instances]
  view_instance <-
    polymorphic [Star] $ \ [sh] ->
    let head = ConTy (builtinTyCon TheTC_view) @@ ConTy sh
        cst = [instancePredicate TheTC_Shape (ConTy sh)]
        body = [coreBuiltin The_IndexableDict_view_at_point,
                coreBuiltin The_IndexableDict_view_get_shape]
    in return (cst, Instance head $ MethodsInstance body)
  return $ view_instance : instances
  where
    monomorphic_instances =
      [(ConTy $ builtinTyCon TheTC_list,
        [coreBuiltin The_IndexableDict_list_at_point,
         coreBuiltin The_IndexableDict_list_get_shape]),
       (ConTy $ builtinTyCon TheTC_blist,
        [coreBuiltin The_IndexableDict_blist_at_point,
         coreBuiltin The_IndexableDict_blist_get_shape]),
       (ConTy $ builtinTyCon TheTC_array1,
        [coreBuiltin The_IndexableDict_array1_at_point,
         coreBuiltin The_IndexableDict_array1_get_shape]),
       (ConTy $ builtinTyCon TheTC_array2,
        [coreBuiltin The_IndexableDict_array2_at_point,
         coreBuiltin The_IndexableDict_array2_get_shape]),
       (ConTy $ builtinTyCon TheTC_array3,
        [coreBuiltin The_IndexableDict_array3_at_point,
         coreBuiltin The_IndexableDict_array3_get_shape]),
       (ConTy $ builtinTyCon TheTC_barray1,
        [coreBuiltin The_IndexableDict_barray1_at_point,
         coreBuiltin The_IndexableDict_barray1_get_shape]),
       (ConTy $ builtinTyCon TheTC_barray2,
        [coreBuiltin The_IndexableDict_barray2_at_point,
         coreBuiltin The_IndexableDict_barray2_get_shape]),
       (ConTy $ builtinTyCon TheTC_barray3,
        [coreBuiltin The_IndexableDict_barray3_at_point,
         coreBuiltin The_IndexableDict_barray3_get_shape])]

additiveClass tc_map = do
  let instances =
        [monomorphicClassInstance head methods
        | (head, methods) <- monomorphic_instances]
  tuple2_instance <-
    polymorphic [Star, Star] $ \ [a,b] ->
    let head = TupleTy 2 @@ ConTy a @@ ConTy b
        cst = [instancePredicate TheTC_Repr (ConTy a),
               instancePredicate TheTC_Repr (ConTy b),
               instancePredicate TheTC_Additive (ConTy a),
               instancePredicate TheTC_Additive (ConTy b)]
        methods = [coreBuiltin The_AdditiveDict_Tuple2_add,
                   coreBuiltin The_AdditiveDict_Tuple2_sub,
                   coreBuiltin The_AdditiveDict_Tuple2_negate,
                   coreBuiltin The_AdditiveDict_Tuple2_zero]
    in return (cst, Instance head $ MethodsInstance methods)
  return $ tuple2_instance : instances
  where
    monomorphic_instances =
      [(ConTy $ builtinTyCon TheTC_int,
        [coreBuiltin The_AdditiveDict_int_add,
         coreBuiltin The_AdditiveDict_int_sub,
         coreBuiltin The_AdditiveDict_int_negate,
         coreBuiltin The_AdditiveDict_int_zero]),
       (ConTy $ builtinTyCon TheTC_float,
        [coreBuiltin The_AdditiveDict_float_add,
         coreBuiltin The_AdditiveDict_float_sub,
         coreBuiltin The_AdditiveDict_float_negate,
         coreBuiltin The_AdditiveDict_float_zero])]

multiplicativeClass tc_map = do
  let instances =
        [monomorphicClassInstance head methods
        | (head, methods) <- monomorphic_instances]
  return instances
  where
    monomorphic_instances =
      [(ConTy $ builtinTyCon TheTC_int,
        [coreBuiltin The_MultiplicativeDict_int_mul,
         coreBuiltin The_MultiplicativeDict_int_fromInt,
         coreBuiltin The_MultiplicativeDict_int_one]),
       (ConTy $ builtinTyCon TheTC_float,
        [coreBuiltin The_MultiplicativeDict_float_mul,
         coreBuiltin The_MultiplicativeDict_float_fromInt,
         coreBuiltin The_MultiplicativeDict_float_one])]

remainderClass tc_map = do
  let instances =
        [monomorphicClassInstance head methods
        | (head, methods) <- monomorphic_instances]
  return instances
  where
    monomorphic_instances =
      [(ConTy $ builtinTyCon TheTC_int,
        [coreBuiltin The_RemainderDict_int_floordiv,
         coreBuiltin The_RemainderDict_int_mod]),
       (ConTy $ builtinTyCon TheTC_float,
        [coreBuiltin The_RemainderDict_float_floordiv,
         coreBuiltin The_RemainderDict_float_mod])]

fractionalClass tc_map = do
  let instances =
        [monomorphicClassInstance head methods
        | (head, methods) <- monomorphic_instances]
  return instances
  where
    monomorphic_instances =
      [(ConTy $ builtinTyCon TheTC_float,
        [coreBuiltin The_FractionalDict_float_div])]

floatingClass tc_map = do
  let instances =
        [monomorphicClassInstance head methods
        | (head, methods) <- monomorphic_instances]
  return instances
  where
    monomorphic_instances =
      [(ConTy $ builtinTyCon TheTC_float,
        [coreBuiltin The_FloatingDict_float_fromfloat,
         coreBuiltin The_FloatingDict_float_power,
         coreBuiltin The_FloatingDict_float_exp,
         coreBuiltin The_FloatingDict_float_log,
         coreBuiltin The_FloatingDict_float_sqrt,
         coreBuiltin The_FloatingDict_float_sin,
         coreBuiltin The_FloatingDict_float_cos,
         coreBuiltin The_FloatingDict_float_tan,
         coreBuiltin The_FloatingDict_float_pi])]

cartesianClass tc_map = do
  let instances =
        [monomorphicClassInstance head methods
        | (head, methods) <- monomorphic_instances]
  return instances
  where
    monomorphic_instances =
      [(ConTy $ builtinTyCon TheTC_dim0,
        [coreBuiltin The_CartesianDict_dim0_loBound,
         coreBuiltin The_CartesianDict_dim0_hiBound,
         coreBuiltin The_CartesianDict_dim0_stride,
         coreBuiltin The_CartesianDict_dim0_arrayDomain,
         coreBuiltin The_CartesianDict_dim0_displaceDomain,
         coreBuiltin The_CartesianDict_dim0_multiplyDomain,
         coreBuiltin The_CartesianDict_dim0_divideDomain,
         coreBuiltin The_CartesianDict_dim0_multiplyIndex,
         coreBuiltin The_CartesianDict_dim0_divideIndex,
         coreBuiltin The_CartesianDict_dim0_unbounded]),
       (ConTy $ builtinTyCon TheTC_dim1,
        [coreBuiltin The_CartesianDict_dim1_loBound,
         coreBuiltin The_CartesianDict_dim1_hiBound,
         coreBuiltin The_CartesianDict_dim1_stride,
         coreBuiltin The_CartesianDict_dim1_arrayDomain,
         coreBuiltin The_CartesianDict_dim1_displaceDomain,
         coreBuiltin The_CartesianDict_dim1_multiplyDomain,
         coreBuiltin The_CartesianDict_dim1_divideDomain,
         coreBuiltin The_CartesianDict_dim1_multiplyIndex,
         coreBuiltin The_CartesianDict_dim1_divideIndex,
         coreBuiltin The_CartesianDict_dim1_unbounded]),
       (ConTy $ builtinTyCon TheTC_dim2,
        [coreBuiltin The_CartesianDict_dim2_loBound,
         coreBuiltin The_CartesianDict_dim2_hiBound,
         coreBuiltin The_CartesianDict_dim2_stride,
         coreBuiltin The_CartesianDict_dim2_arrayDomain,
         coreBuiltin The_CartesianDict_dim2_displaceDomain,
         coreBuiltin The_CartesianDict_dim2_multiplyDomain,
         coreBuiltin The_CartesianDict_dim2_divideDomain,
         coreBuiltin The_CartesianDict_dim2_multiplyIndex,
         coreBuiltin The_CartesianDict_dim2_divideIndex,
         coreBuiltin The_CartesianDict_dim2_unbounded]),
       (ConTy $ builtinTyCon TheTC_dim3,
        [coreBuiltin The_CartesianDict_dim3_loBound,
         coreBuiltin The_CartesianDict_dim3_hiBound,
         coreBuiltin The_CartesianDict_dim3_stride,
         coreBuiltin The_CartesianDict_dim3_arrayDomain,
         coreBuiltin The_CartesianDict_dim3_displaceDomain,
         coreBuiltin The_CartesianDict_dim3_multiplyDomain,
         coreBuiltin The_CartesianDict_dim3_divideDomain,
         coreBuiltin The_CartesianDict_dim3_multiplyIndex,
         coreBuiltin The_CartesianDict_dim3_divideIndex,
         coreBuiltin The_CartesianDict_dim3_unbounded])]
  

-- | Create all type constructors
createTyCons :: SF.TypeEvalM ([(BuiltinTyCon, TyCon)], TyConMap)
createTyCons = do
  m_results <- mapM (runMaybeT . createTyCon) tyConInitializers
  let tc_map = Map.fromList [(sf, tc) | (_, tc, sf) <- catMaybes m_results]
      assocs = [(i, c) | (i, c, _) <- catMaybes m_results]
  return (assocs, tc_map)
  where
    createTyCon (frontend_con, core_con, init) = do
      let core_var = either id coreBuiltin core_con
      unless (SF.getLevel core_var == SF.TypeLevel) $
        internalError "createTyCons: Not a type variable"
      tycon <- translateVar core_var (initializerClass init)
      return (frontend_con, tycon, core_var)

-- | Translate a System F variable to a frontend variable
translateVar :: SF.Var -> TyConClass -> InitM TyCon
translateVar v cls = do
  -- Compute kind
  tenv <- SF.getTypeEnv
  let Just sf_kind = SF.lookupType v tenv
  k <- frontendKind sf_kind

  -- If it is a type function, get its arity
  let arity =
        case cls
        of TCCFun ->
             let Just tf = SF.lookupTypeFunction v tenv
             in SF.typeFunctionArity tf
           _ -> 0

  -- Create type constructor
  liftIO $ newTyCon v k cls arity

-- | Translate a type variable and add the translation to the map
translateTyVar :: TyConMap -> SF.Var -> InitM (TyCon, TyConMap)
translateTyVar m v = do
  v' <- translateVar v TCCVar
  let m' = Map.insert v v' m
  return (v', m')

translateTyVars :: TyConMap -> [SF.Var] -> InitM ([TyCon], TyConMap)
translateTyVars m (v:vs) = do
  (v', m') <- translateTyVar m v
  (vs', m'') <- translateTyVars m' vs
  return (v':vs', m'')

translateTyVars m [] = return ([], m)

-- | After translating type variables, create type bindings
mkTypeBindings :: TyConMap
               -> SF.TypeEnv    -- ^ Core type environment
               -> SF.TypeEvalM (Map.Map TyCon TypeBinding)
mkTypeBindings tc_map core_type_env = do
  assocs <- mapM (runMaybeT . mk_binding) tyConInitializers
  return $ Map.fromList $ catMaybes assocs
  where
    mk_binding (_, sf_name, initializer) = do
      -- Look up the frontend type constructor
      let sf_var = either id coreBuiltin sf_name
          Just tc_var = Map.lookup sf_var tc_map
      binding <-
        case initializer
        of TyConInitializer ->
             mkDataTypeBinding tc_var core_type_env
           TyFamInitializer mk_instances ->
             mkTypeFamilyBinding tc_var (mk_instances tc_map)
           TyClsInitializer abstract mk_instances ->
             mkTypeClassBinding tc_map tc_var abstract (mk_instances tc_map)
      return (tc_var, binding)

mkDataTypeBinding :: TyCon -> SF.TypeEnv -> InitM TypeBinding
mkDataTypeBinding tycon core_type_env = do
  let sf_var = tyConSFVar tycon
  let Just core_kind = SF.lookupType sf_var core_type_env
  is_boxed <- isBoxedKind core_type_env core_kind
  return $ TyConAss (DataType is_boxed)

mkTypeFamilyBinding :: TyCon             -- ^ Type family constructor
                    -> InitM (Instances TyFamilyInstance)
                    -> InitM TypeBinding
mkTypeFamilyBinding tycon mk_instances = do
  tenv <- SF.getTypeEnv
  let sf_var = tyConSFVar tycon
      Just kind = SF.lookupType sf_var tenv
      Just type_function = SF.lookupTypeFunction sf_var tenv
      arity = SF.typeFunctionArity type_function

  kind' <- frontendKind kind
  instances <- mk_instances
  return $ TyFunAss $ TyFamily sf_var arity kind' instances

mkTypeClassBinding :: TyConMap
                   -> TyCon
                   -> Bool
                   -> InitM (Instances ClassInstance)
                   -> InitM TypeBinding
mkTypeClassBinding tc_map tycon abstract mk_instances = do
  tenv <- SF.getTypeEnv
  let sf_var = tyConSFVar tycon
      Just data_type = SF.lookupDataType sf_var tenv
      [dict_var] = SF.dataTypeDataConstructors data_type
      Just dcon_type = SF.lookupDataCon dict_var tenv

  signature <- frontendClassSignature tc_map abstract dcon_type
  instances <- mk_instances
  return $ TyClsAss $ Class sf_var dict_var abstract signature instances

-------------------------------------------------------------------------------
-- Variable initialization

-- | Data to create the value binding for a variable
data VarInitializer =
    FromSF BuiltinThing
    -- | A class method.  The varible's name is given. 
    --   Its other properties are looked up from the given class and
    --   method index.
  | MethodInitializer String BuiltinTyCon Int

varInitializers :: [(BuiltinVar, VarInitializer)]
varInitializers =
  [(v, FromSF t) | (v, t) <- sf_initializers] ++
  [(v, MethodInitializer name c i) | (v, c, i, name) <- method_initializers]
  where
    sf_initializers =
      [ -- Data constructors
        (TheV_Just, The_just)
      , (TheV_Nothing, The_nothing)
      , (TheV_dim0, The_mk_dim0)
      , (TheV_dim2, The_mk_dim2)
      , (TheV_dim3, The_mk_dim3)
      , (TheV_cons, The_cons)
      , (TheV_nil, The_nil)

        -- Functions
      , (TheV_isJust, The_fun_isJust)
      , (TheV_isNothing, The_fun_isNothing)
      , (TheV_fromJust, The_fun_fromJust)
      , (TheV_isCons, The_isCons)
      , (TheV_isNil, The_isNil)
      , (TheV_head, The_head)
      , (TheV_tail, The_tail)
      , (TheV_list_dim, The_fun_list_dim)
      , (TheV_map, The_fun_map)
      , (TheV_filter, The_fun_filter)
      , (TheV_reduce, The_fun_reduce)
      , (TheV_reduce1, The_fun_reduce1)
      , (TheV_sum, The_fun_sum)
      , (TheV_zip, The_fun_zip)
      , (TheV_zip3, The_fun_zip3)
      , (TheV_zip4, The_fun_zip4)
      , (TheV_count, The_count)
      , (TheV_range, The_range)
      , (TheV_arrayRange, The_arrayRange)
      , (TheV_chain, The_chain)
      , (TheV_singletonIter, The_singletonIter)
      , (TheV_indices, The_fun_indices)
      , (TheV_len, The_len)
      , (TheV_width, The_width)
      , (TheV_height, The_height)
      , (TheV_rows, The_rows)
      , (TheV_cols, The_cols)
      , (TheV_outerproduct, The_outerproduct)
      , (TheV_displaceView, The_displaceView)
      , (TheV_multiplyView, The_multiplyView)
      , (TheV_divideView, The_divideView)
      , (TheV_permute1D, The_permute1D)
      , (TheV_boxedPermute1D, The_boxedPermute1D)
      , (TheV_stencil2D, The_stencil2D)
      , (TheV_boxedStencil2D, The_boxedStencil2D)
      , (TheV_extend2D, The_extend2D)
      , (TheV_stencil3D, The_stencil3D)
      , (TheV_boxedStencil3D, The_boxedStencil3D)
      , (TheV_extend3D, The_extend3D)
      , (TheV_unionView3D, The_unionView3D)
      , (TheV_histogram, The_histogram)
      , (TheV_floor, The_floor)
      , (TheV_intScatter, The_intScatter)
      , (TheV_floatScatter, The_floatScatter)
      , (TheV_boolScatter, The_boolScatter)
      , (TheV_intSumScatter, The_intSumScatter)
      , (TheV_floatSumScatter, The_floatSumScatter)
      , (TheV_countingScatter, The_countingScatter)
      , (TheV_boxedScatter, The_boxedScatter)
      , (TheV_appendScatter, The_appendScatter)
      , (TheV_listScatter, The_listScatter)
      , (TheV_array1Scatter, The_array1Scatter)
      , (TheV_array2Scatter, The_array2Scatter)
      , (TheV_array3Scatter, The_array3Scatter)
      , (TheV_blistScatter, The_blistScatter)
      , (TheV_barray1Scatter, The_barray1Scatter)
      , (TheV_barray2Scatter, The_barray2Scatter)
      , (TheV_barray3Scatter, The_barray3Scatter)
      , (TheV_scatter, The_fun_scatter)
      , (TheV_intset, The_build_intset)
      , (TheV_intsetLookup, The_intsetLookup)
      , (TheV_intsetElements, The_intsetElements)
      , (TheV___undefined__, The_fun_undefined)
      , (TheV___and__, The_oper_BITWISEAND)
      , (TheV___or__, The_oper_BITWISEOR)
      , (TheV___xor__, The_oper_BITWISEXOR)
      , (TheV_and, The_and)
      , (TheV_or, The_or)
      , (TheV_not, The_not)
      , (TheV___lshift__, The_lshift)
      , (TheV___rshift__, The_rshift)
      , (TheV___getitem__, The_safeIndex)
      , (TheV___getslice__, The_safeSlice)
      , (TheV_do, The_Stream1_return)
      , (TheV_guard, The_Stream1_guard)
      , (TheV_iterBind, The_Stream1_bind)
      , (TheV_make_sliceObject, The_make_sliceObject)
      ]

    method_initializers =
      [ (TheV___eq__,         TheTC_Eq,              0, "__eq__")
      , (TheV___ne__,         TheTC_Eq,              1, "__ne__")

      , (TheV___lt__,         TheTC_Ord,             0, "__lt__")
      , (TheV___le__,         TheTC_Ord,             1, "__le__")
      , (TheV___gt__,         TheTC_Ord,             2, "__gt__")
      , (TheV___ge__,         TheTC_Ord,             3, "__ge__")

      , (TheV_iter,           TheTC_Traversable,     0, "iter")
      , (TheV_build,          TheTC_Traversable,     1, "build")

      , (TheV_member,         TheTC_Shape,           0, "member")
      , (TheV_intersection,   TheTC_Shape,           1, "intersection")
      , (TheV_flatten,        TheTC_Shape,           2, "flatten")
      , (TheV_generate,       TheTC_Shape,           3, "generate")
      , (TheV_mapStream,      TheTC_Shape,           4, "mapIter")
      , (TheV_zipWithStream,  TheTC_Shape,           5, "zipWithIter")
      , (TheV_zipWith3Stream, TheTC_Shape,           6, "zipWith3Iter")
      , (TheV_zipWith4Stream, TheTC_Shape,           7, "zipWith4Iter")
      , (TheV_getSlice,       TheTC_Shape,           8, "getSlice")

      , (TheV_at_point,       TheTC_Indexable,       0, "at_point")
      , (TheV_domain,         TheTC_Indexable,       1, "domain")

      , (TheV___add__,        TheTC_Additive,        0, "__add__")
      , (TheV___sub__,        TheTC_Additive,        1, "__sub__")
      , (TheV___negate__,     TheTC_Additive,        2, "__negate__")
      , (TheV_zero,           TheTC_Additive,        3, "zero")

      , (TheV___mul__,        TheTC_Multiplicative,  0, "__mul__")
      , (TheV___fromint__,    TheTC_Multiplicative,  1, "__fromint__")
      , (TheV_one,            TheTC_Multiplicative,  2, "one")

      , (TheV___floordiv__,   TheTC_Remainder,       0, "__floordiv__")
      , (TheV___mod__,        TheTC_Remainder,       1, "__mod__")

      , (TheV___div__,        TheTC_Fractional,      0, "__div__")

      , (TheV___fromfloat__,  TheTC_Floating,        0, "__fromfloat__")
      , (TheV___power__,      TheTC_Floating,        1, "__power__")
      , (TheV_exp,            TheTC_Floating,        2, "exp")
      , (TheV_log,            TheTC_Floating,        3, "log")
      , (TheV_sqrt,           TheTC_Floating,        4, "sqrt")
      , (TheV_sin,            TheTC_Floating,        5, "sin")
      , (TheV_cos,            TheTC_Floating,        6, "cos")
      , (TheV_tan,            TheTC_Floating,        7, "tan")
      , (TheV_pi,             TheTC_Floating,        8, "pi")
        
      , (TheV_loBound,        TheTC_Cartesian,       0, "loBound")
      , (TheV_hiBound,        TheTC_Cartesian,       1, "hiBound")
      , (TheV_stride,         TheTC_Cartesian,       2, "stride")
      , (TheV_arrayDomain,    TheTC_Cartesian,       3, "arrayDomain")
      , (TheV_displaceDomain, TheTC_Cartesian,       4, "displaceDomain")
      , (TheV_multiplyDomain, TheTC_Cartesian,       5, "multiplyDomain")
      , (TheV_divideDomain,   TheTC_Cartesian,       6, "divideDomain")
      , (TheV_multiplyIndex,  TheTC_Cartesian,       7, "multiplyIndex")
      , (TheV_divideIndex,    TheTC_Cartesian,       8, "divideIndex")
      , (TheV_unbounded,      TheTC_Cartesian,       9, "unbounded")
      ]

-- | Create all variables and their value bindings
createVars :: TyConMap
           -> Map.Map TyCon TypeBinding
           -> SF.TypeEvalM ([(BuiltinVar, Variable)],
                            Map.Map Variable ValueBinding)
createVars tc_map t_bindings = do
  results <- mapM (runMaybeT . createVar) varInitializers
  let m = Map.fromList [(v, binding) | (_, v, binding) <- catMaybes results]
      assocs = [(frontend_var, var) | (frontend_var, var, _) <- catMaybes results]
  return (assocs, m)
  where
    createVar (frontend_thing, init) =
      case init
      of FromSF core_thing ->
           translateVariable tc_map frontend_thing core_thing
         MethodInitializer name cls_tycon index ->
           createMethod tc_map t_bindings frontend_thing name cls_tycon index

createMethod tc_map t_bindings frontend_thing name cls_tycon index = do
  -- Create a new frontend variable
  var <- liftIO $ newVariable (Just $ builtinLabel name) Nothing

  -- Get the method's type from the type class
  --let Just (TyClsAss cls) = Map.lookup (builtinTyCon cls_tycon) t_bindings
  --let signature = make_signature $ clsSignature cls
  --let binding = MethodAss signature
  let binding = MethodAss (builtinTyCon cls_tycon) index

  return (frontend_thing, var, binding)
  where
    -- The method signature is based on the class and class method signatures.
    -- Use the class's type parameters, but remove the class's context.
    make_signature (Qualified [cls_typaram] _ methods)
      | index < 0 || index > length methods =
          internalError "createVars: Index out of bounds"
      | otherwise =
          let method_signature = clmSignature $ methods !! index
              constraint = [instancePredicate cls_tycon (ConTy cls_typaram)]
          in Qualified [cls_typaram] constraint method_signature

translateVariable :: TyConMap -> BuiltinVar -> BuiltinThing
                  -> InitM (BuiltinVar, Variable, ValueBinding)
translateVariable tc_map frontend_thing core_thing = do
  -- Look up the System F variable
  let v = coreBuiltin core_thing
  unless (SF.getLevel v == SF.ObjectLevel) $
    internalError "translateVariable: Not a value variable"

  -- Create a frontend variable
  frontend_var <- liftIO $ newVariable (SF.varName v) (Just v)

  -- Create a binding
  tenv <- SF.getTypeEnv
  binding <- case ()
             of _ | Just dcon_type <- SF.lookupDataCon v tenv ->
                      translateDataCon tc_map v dcon_type
                  | Just ty <- SF.lookupType v tenv ->
                      translateGlobalVar tc_map v ty
  return (frontend_thing, frontend_var, binding)

translateDataCon tc_map v dcon_type = SF.assumeBinders ty_params $ do
  (ty_params', tc_map') <- translateTyVars tc_map $ map SF.binderVar ty_params

  -- Existential types aren't supported
  guard (null ex_types)

  -- Translate field types
  field_types' <- mapM (frontendType tc_map') field_types

  let signature =
        Qualified ty_params' [] (field_types', FOConstructor data_type_con)
  return $ DataConAss $ DataCon signature
  where
    ty_params = SF.dataTypeParams $ SF.dataConType dcon_type
    ex_types = SF.dataConExTypes dcon_type
    field_types = SF.dataConFieldTypes dcon_type
    Just data_type_con = Map.lookup (SF.dataConTyCon dcon_type) tc_map

translateGlobalVar tc_map v ty = do
  scm <- frontendTyScheme tc_map ty
  return $ PolyVarAss scm

-------------------------------------------------------------------------------
-- Exported top-level routines

setupTypeEnvironment :: IdentSupply SF.Var
                     -> SF.TypeEnv     -- ^ System F type environment
                     -> SF.TypeEnv     -- ^ Core type nvironment
                     -> IO Environment
setupTypeEnvironment id_supply sf_type_env core_type_env = do
  -- Create type constructors
  (tc_list, tc_map) <- run_type_action createTyCons
  initializeFrontendBuiltinTypes tc_list
            
  -- Create type bindings
  tc_bindings <- run_type_action $ mkTypeBindings tc_map core_type_env

  -- Create variables
  (v_list, v_bindings) <- run_type_action $ createVars tc_map tc_bindings
  initializeFrontendBuiltinVars v_list
  
  return $ Environment tc_bindings v_bindings id_supply
  where
    run_type_action :: SF.TypeEvalM a -> IO a
    run_type_action m = SF.runTypeEvalM m id_supply sf_type_env

-- | Dump the type environment in human-readable form.
dumpTypeEnvironment :: Environment -> IO ()
dumpTypeEnvironment env = do
  print =<< runTE env (runPpr $ pprTypeEnvironment $ envTypes env)
  print =<< runTE env (runPpr $ pprValueEnvironment $ envValues env)