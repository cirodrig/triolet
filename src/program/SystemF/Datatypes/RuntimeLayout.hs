
module SystemF.Datatypes.RuntimeLayout where

import Control.Monad
import qualified Data.IntMap as IntMap
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Label
import Builtins.Builtins
import SystemF.Build
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import SystemF.Datatypes.ComputeLayout
import Type.Type
import Type.Environment
import qualified LowLevel.Types as LL

{-# INLINE primFunApp #-}
primFunApp name tys es = appE' (varE' (pyonBuiltin name)) tys es

uintType = VarT $ pyonBuiltin The_uint

-------------------------------------------------------------------------------

-- | Tag for computing a 'copy' method
data Copy

-- | Tag for computing size and alignment
data SizeAlign

-- | Tag for computing a 'Repr' object
data Repr

type ComputeRepr a = Compute Var (TypedData a)

-- | Values used in computing an 'a', with attached type information
data TypedData a =
    -- These are descriptions of "real" types

    -- | Description of a boxed field (always a pointer)
    TBox
    { trType :: !Type
    }
    -- | Description of a bare object
  | TBare
    { trType :: !Type
    , trExp  :: ExpM
    }
    -- | Description of a value object
  | TVal
    { trType :: !Type
    , trExp  :: ExpM
    }
    -- | Description of a type-level integer
  | TInt
    { trType :: !Type
    , trExp  :: ExpM
    }

    -- These are descriptions of structures finer than types.
    -- Algebraic data types are made from one or more of these.

    -- | Description of a tag value
  | TITag
    { trTagSize  :: {-#UNPACK#-}!Int
    , trTagAlign :: {-#UNPACK#-}!Int
    }
    -- | Product of some objects
  | TIProduct
    { trMembers :: [TypedData a]
    }
    -- | Union of some objects
  | TIUnion
    { trMembers :: [TypedData a]
    }

pprTypedData :: TypedData a -> Doc
pprTypedData (TBox t) = text "TBox" <+> parens (pprType t)
pprTypedData (TBare t e) = text "TBare" <+> sep [parens (pprType t), 
                                                 parens (pprExp e)]
pprTypedData (TVal t e) = text "TVal" <+> sep [parens (pprType t), 
                                               parens (pprExp e)]

pprTypedData (TInt t e) = text "TInt" <+> sep [parens (pprType t), 
                                               parens (pprExp e)]
pprTypedData (TITag s a) = text "TITag" <+> int s <+> int a
pprTypedData (TIProduct xs) = text "TIProduct" <+> vcat (map pprTypedData xs)
pprTypedData (TIUnion xs) = text "TIUnion" <+> vcat (map pprTypedData xs)

-- | Description of a tag field
tagData :: BaseKind -> Int -> TypedData a
tagData k n = TITag (LL.sizeOf primtype) (LL.alignOf primtype)
  where
    primtype =
      case k
      of BoxK           -> LL.PointerType
         _ | n == 1     -> LL.UnitType
           | n <= 256   -> LL.IntType LL.Unsigned LL.S8
           | n <= 65536 -> LL.IntType LL.Unsigned LL.S16

useEvidence k t v =
  case k
  of BareK     -> TBare t derivation
     ValK      -> TVal t derivation
     IntIndexK -> TInt t derivation
  where
    derivation = varE' v

-------------------------------------------------------------------------------
-- Compute nothing; just keep track of the structure 

adtStructureOnly :: Algorithm () (TypedData ())
adtStructureOnly =
  Algorithm
  { lcNewEvidence = \_ _ -> return ()
  , lcUseEvidence = \k t _ -> unitTypedData k t
  , lcIntType     = return $ TVal (VarT $ pyonBuiltin The_int) dummy
  , lcUintType    = return $ TVal (VarT $ pyonBuiltin The_uint) dummy
  , lcFloatType   = return $ TVal (VarT $ pyonBuiltin The_float) dummy
  , lcBoolType    = return $ TVal (VarT $ pyonBuiltin The_bool) dummy
  , lcUnitType    = \t -> return $ TVal t dummy
  , lcUninhabited = \k t -> return $! unitTypedData k t
  , lcBox         = \t -> return $ TBox t
  , lcArrType     = \s e -> let t = varApp (pyonBuiltin The_arr)
                                    [trType s, trType e]
                            in return $ TBare t dummy
  , lcTag         = tagData
  , lcUnion       = return . TIUnion
  , lcProduct     = return . TIProduct
  , lcAlgType     = \k t _ -> return $! unitTypedData k t
  , lcTypeInt     = \n -> return $ TInt (IntT n) dummy
  }
  where
    -- Expressions aren't actually used
    dummy = internalError "adtStructureOnly does not compute expressions"
    -- dummy = ExpM $ ExceptE defaultExpInfo (VarT $ pyonBuiltin The_int)

    unitTypedData :: BaseKind -> Type -> TypedData ()
    unitTypedData BareK     t = TBare t dummy
    unitTypedData ValK      t = TVal t dummy
    unitTypedData IntIndexK t = TInt t dummy

-------------------------------------------------------------------------------
-- Size and alignment computation

-- | In an 'SAData', all data constructors except 'TInt' are represented by
--   @(uint, uint)@ pairs at run time.  'TInt' is represented by an 'IInt a'
--   value.
type SAData = TypedData SizeAlign

type SACompute a = ComputeRepr SizeAlign a

adtSizeAlign :: Algorithm Var SAData
adtSizeAlign =
  Algorithm
  { lcNewEvidence = \_ _ -> newAnonymousVar ObjectLevel
  , lcUseEvidence = useEvidence
  , lcIntType     = return $ sizeAlignForVal (VarT $ pyonBuiltin The_int) LL.pyonIntType
  , lcUintType    = return $ sizeAlignForVal (VarT $ pyonBuiltin The_uint) LL.pyonUintType
  , lcFloatType   = return $ sizeAlignForVal (VarT $ pyonBuiltin The_float) LL.pyonFloatType
  , lcBoolType    = return $ sizeAlignForVal (VarT $ pyonBuiltin The_bool) LL.pyonBoolType
  , lcUnitType    = \t -> return $ sizeAlignForVal t LL.pyonNoneType
  , lcUninhabited = \k t -> case k
                            of BoxK  -> return $ TBox t
                               BareK -> return $ sizeAlignForBare t LL.UnitType
                               ValK  -> return $ sizeAlignForVal t LL.UnitType
  , lcBox         = \t -> return $ TBox t
  , lcArrType     = arraySizeAlign
  , lcTag         = tagData
  , lcUnion       = return . TIUnion
  , lcProduct     = return . TIProduct
  , lcAlgType     = algebraicSizeAlign
  , lcTypeInt     = undefined
  }

-- | Create a literal value @N@ of type @uint@
uintValue n = ExpM $ LitE defaultExpInfo $ IntL (fromIntegral n) uintType

-- | Create a literal value @(x, y)@ of type @(uint, uint)@
uintPairValue x y =
  ExpM $ ConE defaultExpInfo (TupleCon [uintType, uintType]) [x, y]

-- | Deconstruct a uint into its component fields
unpackUint :: ExpM -> (ExpM -> ExpM -> Compute e d ExpM) -> Compute e d ExpM
unpackUint e k = do
  v1 <- newVar (Just $ builtinLabel "size") ObjectLevel
  v2 <- newVar (Just $ builtinLabel "align") ObjectLevel
  body <- k (varE' v1) (varE' v2)
  let decon = TupleDeCon [uintType, uintType]
      alt = AltM $
            Alt decon [patM (v1 ::: uintType), patM (v2 ::: uintType)] body
  return $ ExpM $ CaseE defaultExpInfo e [alt]

unpackUints (e:es) k = do
  unpackUint e $ \s a -> unpackUints es $ \ss as -> k (s:ss) (a:as)

unpackUints [] k = k [] []

sizeAlignForVal :: Type -> LL.PrimType -> SAData
sizeAlignForVal ty ll_ty =
  let sz = uintValue $ LL.sizeOf ll_ty
      al = uintValue $ LL.sizeOf ll_ty
  in TVal ty (uintPairValue sz al)
  
sizeAlignForBare :: Type -> LL.PrimType -> SAData
sizeAlignForBare ty ll_ty =
  let sz = uintValue $ LL.sizeOf ll_ty
      al = uintValue $ LL.sizeOf ll_ty
  in TBare ty (uintPairValue sz al)

arraySizeAlign (TInt n length_exp) (TBare elt elt_exp) =
  let array_type = varApp (pyonBuiltin The_arr) [n, elt]
      array_exp = primFunApp The_sizealign_arr [n] [length_exp, elt_exp]
  in return $ TBare array_type array_exp

-- | A computation of a pair of size and alignment values.
--   Given 
newtype SizeAlignIntro e d =
  SizeAlignIntro
  {sizeAlignElim :: (ExpM -> ExpM -> Compute e d ExpM) -> Compute e d ExpM}

sizeAlignIntro :: ExpM -> ExpM -> SizeAlignIntro e d
sizeAlignIntro s a = SizeAlignIntro (\f -> f s a)

sizeAlignIntroFromTuple :: ExpM -> SizeAlignIntro e d
sizeAlignIntroFromTuple e = SizeAlignIntro (\f -> unpackUint e f)

-- | Use a list of (size, alignment) pairs in a computation
sizeAlignElimList :: [SizeAlignIntro e d]
                  -> ([(ExpM, ExpM)] -> Compute e d ExpM)
                  -> Compute e d ExpM
sizeAlignElimList (SizeAlignIntro f : xs) k =
  -- Eliminate one (size, alignment) pair;
  -- call 'sizeAlignElimList' to eliminate the rest
  f $ \s a -> sizeAlignElimList xs $ \sas -> k ((s, a) : sas)

sizeAlignElimList [] k = k []

-- | Compute size and alignment of a product
sizeAlignProduct :: (ExpM, ExpM) -- ^ Initial size and alignment
                 -> (ExpM, ExpM) -- ^ Next object's size and alignment
                 -> (ExpM -> ExpM -> Compute e d ExpM)
                 -> Compute e d ExpM
sizeAlignProduct (s1, a1) (s2, a2) k = do
  s3 <- newVar (Just $ builtinLabel "size") ObjectLevel
  a3 <- newVar (Just $ builtinLabel "align") ObjectLevel
  e <- k (varE' s3) (varE' a3)

  -- Add padding bytes (-s1 `mod` a2) so that object 2 is properly aligned
  -- s3 = s1 + (-s1 `mod` a2) + s2
  let size_expr = primFunApp The_AdditiveDict_uint_add []
                  [primFunApp The_AdditiveDict_uint_add []
                   [s1, s2],
                   primFunApp The_RemainderDict_uint_mod []
                   [primFunApp The_AdditiveDict_uint_negate [] [s1], a2]]
      align_expr = primFunApp The_max_uint [] [a1, a2]
      expr = letE (patM (s3 ::: uintType)) size_expr $
             letE (patM (a3 ::: uintType)) align_expr $ e
  return expr

sizeAlignProducts :: [(ExpM, ExpM)]
                  -> (ExpM -> ExpM -> Compute e d ExpM)
                  -> Compute e d ExpM
sizeAlignProducts sas k = go (uintValue 0) (uintValue 1) sas
  where
    go s a (sa:sas) = sizeAlignProduct (s, a) sa $ \s' a' -> go s' a' sas
    go s a []       = k s a

sizeAlignUnion :: (ExpM, ExpM) -- ^ Initial size and alignment
               -> (ExpM, ExpM) -- ^ Next object's size and alignment
               -> (ExpM -> ExpM -> Compute e d ExpM)
               -> Compute e d ExpM
sizeAlignUnion (s1, a1) (s2, a2) k = do
  s3 <- newVar (Just $ builtinLabel "size") ObjectLevel
  a3 <- newVar (Just $ builtinLabel "align") ObjectLevel
  e <- k (varE' s3) (varE' a3)

  let size_expr = primFunApp The_max_uint [] [s1, s2]
      align_expr = primFunApp The_max_uint [] [a1, a2]
      expr = letE (patM (s3 ::: uintType)) size_expr $
             letE (patM (a3 ::: uintType)) align_expr $ e
  return expr

sizeAlignUnions :: [(ExpM, ExpM)]
                -> (ExpM -> ExpM -> Compute e d ExpM)
                -> Compute e d ExpM
sizeAlignUnions sas k = go (uintValue 0) (uintValue 1) sas
  where
    go s a (sa:sas) = sizeAlignUnion (s, a) sa $ \s' a' -> go s' a' sas
    go s a []       = k s a

-- | Compute the size and alignment of an 'SAData'
--   in the form of a @(uint, uint)@ pair.
algebraicSizeAlignIntro :: SAData -> SizeAlignIntro Var SAData
algebraicSizeAlignIntro (TBox _) =
  sizeAlignIntro
  (uintValue $ LL.sizeOf LL.OwnedType)
  (uintValue $ LL.alignOf LL.OwnedType)

algebraicSizeAlignIntro (TBare _ e) = sizeAlignIntroFromTuple e
algebraicSizeAlignIntro (TVal _ e)  = sizeAlignIntroFromTuple e
algebraicSizeAlignIntro (TInt {}) = internalError "algebraicSizeAlignIntro"
algebraicSizeAlignIntro (TITag s a) =
  sizeAlignIntro (uintValue s) (uintValue a)

algebraicSizeAlignIntro (TIProduct xs) = SizeAlignIntro $ \k ->
  -- Get size and alignment of each product member
  sizeAlignElimList (map algebraicSizeAlignIntro xs) $ \sas ->
  -- Combine into the size and alignment of their product
  sizeAlignProducts sas k

algebraicSizeAlignIntro (TIUnion xs) = SizeAlignIntro $ \k ->
  -- Get size and alignment of each product member
  sizeAlignElimList (map algebraicSizeAlignIntro xs) $ \sas ->
  -- Combine into the size and alignment of their union
  sizeAlignUnions sas k

-- | Compute the size and alignment of an 'SAData'
--   in the form of a @SizeAlign t@ or @SizeAlignVal t@ object.
--
--   There's no actual run-time type for describing boxed objects, so they
--   produce a @(uint, uint)@ pair.
--
--   This function calls 'algebraicSizeAlignIntro' to compute the
--   size and alignment expressions,
--   then constructs the appropriate return value out of those.
algebraicSizeAlign :: BaseKind -> Type -> SAData -> SACompute SAData
algebraicSizeAlign k ty sa = do
  expr <- sizeAlignElim (algebraicSizeAlignIntro sa)
          (\x y -> return $ uintPairValue x y)
  return $! case k
            of ValK  -> TVal ty expr
               BareK -> TBare ty expr
               BoxK  -> internalError "algebraicSizeAlign: Boxed objects do not have a size or alignment"

sizeAlignObjectType k ty =
  case k
  of IntIndexK -> varApp (pyonBuiltin The_IInt) [ty]
     BareK     -> uint_pair_type
     ValK      -> uint_pair_type
     BoxK      -> uint_pair_type
  where
    uint_pair_type = typeApp (UTupleT [ValK, ValK]) [uintType, uintType]

runSizeAlign :: SACompute SAData -> ReprCompute ExpM
runSizeAlign m = runSubcomputation derive_premise create_result m
  where
    derive_premise :: Entry Var -> ReprCompute SAData
    derive_premise (k, ty, v) = do
      -- Get the Repr object for this premise
      premise_v <- lookupOrCreatePremise adtRepr k ty

      case k of
        ValK -> do
          -- Convert a @SizeAlignVal t@ to a @(uint, uint)@
          tenv <- getTypeEnv
          expr <- caseE (mkVarE premise_v)
                  [mkAlt tenv (pyonBuiltin The_sizeAlignVal) [ty]
                   (\ [] [x, y] -> return $ uintPairValue (varE' x) (varE' y))]
          return $ TVal ty expr
        BareK -> do
          -- Convert a @Repr t@ to a @(uint, uint)@
          tenv <- getTypeEnv
          expr <- caseE (mkVarE premise_v)
                  [mkAlt tenv (pyonBuiltin The_repr) [ty]
                   (\ [] [sa, _, _, _, _] ->
                     caseE (mkVarE sa)
                     [mkAlt tenv (pyonBuiltin The_sizeAlign) [ty]
                      (\ [] [x, y] ->
                        return $ uintPairValue (varE' x) (varE' y))])]
          return $ TBare ty expr
        IntIndexK ->
          -- Int indices are the same for both computations
          return $ TInt ty (varE' premise_v)

    create_result bindings deriv = 
      return $ foldr make_let_binding (trExp deriv) bindings
      where
        make_let_binding (k, ty, (v, derivation)) e =
          let binder_type = sizeAlignObjectType k ty
              rhs = trExp derivation
          in ExpM $ LetE defaultExpInfo (patM $ v ::: binder_type) rhs e

-------------------------------------------------------------------------------
-- Copy method computation

type CopyData = TypedData Copy

type CopyCompute a = Compute Var CopyData a

-- Computation of copy methods.
-- Only kinds 'bare' and 'intindex' are used.
adtCopy :: Algorithm Var CopyData
adtCopy =
  Algorithm
  { lcNewEvidence = \_ _ -> newAnonymousVar ObjectLevel
  , lcUseEvidence = useEvidence
  , lcIntType     = dummyCopyValue (VarT $ pyonBuiltin The_int)
  , lcUintType    = dummyCopyValue (VarT $ pyonBuiltin The_uint)
  , lcFloatType   = dummyCopyValue (VarT $ pyonBuiltin The_float)
  , lcBoolType    = dummyCopyValue (VarT $ pyonBuiltin The_bool)
  , lcUnitType    = dummyCopyValue
  , lcUninhabited = \k t -> case k
                            of BareK -> return $ dynamicCopyError t
                               ValK  -> dummyCopyValue t
  , lcBox         = dummyCopyBox
  , lcArrType     = arrayCopy
  , lcTag         = tagData
  , lcUnion       = return . TIUnion
  , lcProduct     = return . TIProduct
  , lcAlgType     = algebraicCopy
  , lcTypeInt     = \_ -> cannotCopyInt
  }

dummyCopyValue t = return $ TVal t (internalError "Cannot copy kind val")
dummyCopyBox t = return $ TBox t

cannotCopyInt :: CopyCompute CopyData
cannotCopyInt = internalError "Cannot generate a copy method for kind intindex"

-- | A copy method that produces a run-time error if called
dynamicCopyError :: Type -> CopyData
dynamicCopyError ty =
  TIProduct [TBare ty (primFunApp The_dynamicCopyError [ty] [])]

arrayCopy :: CopyData -> CopyData -> CopyCompute CopyData
arrayCopy (TInt size_ty size_val) (TBare elt_ty elt_val) =
  let arr_ty = varApp (pyonBuiltin The_arr) [size_ty, elt_ty]
      arr_exp = primFunApp The_copyArray [size_ty, elt_ty] [size_val, elt_val]
  in return $ TBare arr_ty arr_exp

algebraicCopy :: BaseKind -> Type -> CopyData -> CopyCompute CopyData
algebraicCopy ValK ty _ = dummyCopyValue ty
algebraicCopy BoxK ty _ = dummyCopyBox ty
algebraicCopy BareK ty deriv = do
  expr <- make_expr
  return $ TBare ty expr
  where
    -- Type must be an algebraic data type
    Just (type_con, ty_args) = fromVarApp ty

    -- Create a copy function
    make_expr :: CopyCompute ExpM 
    make_expr =
      lamE $ mkFun []
      (\ [] -> return ([ty, varApp (pyonBuiltin The_OutPtr) [ty]],
                       VarT $ pyonBuiltin The_Store))
      (\ [] [src, ret] -> do
          -- Look up the data constructors for this type
          tenv <- getTypeEnv
          let Just data_type = trace ("algebraicCopy " ++ show type_con) $ lookupDataType type_con tenv
              constructors = dataTypeDataConstructors data_type

          -- Create a case statement to deconstruct this type,
          -- using the derivation to decide how to copy fields
          caseE (mkVarE src) $
            zipWith (make_alt tenv ret) (products deriv) constructors)

    -- Create a case alternative within a copy function
    make_alt :: TypeEnv -> Var -> [CopyData] -> Var -> CopyCompute AltM
    make_alt tenv ret product data_con =
      -- Create a case alternative
      mkAlt tenv data_con ty_args $ \exvars field_vars -> do
        -- Create a data constructor expression
        let con = VarCon data_con ty_args (map VarT exvars)
        appExp (mkConE defaultExpInfo con
                (zipWith make_field product field_vars)) [] [mkVarE ret]

    -- Copy one field inside a data constructor.
    -- If the field is bare, use the previously computed copy method.
    make_field :: CopyData -> Var -> CopyCompute ExpM
    make_field field_data field_var =
      case field_data
      of TBox {} -> mkVarE field_var
         TVal {} -> mkVarE field_var
         TBare _ copy_expr -> appExp (return copy_expr) [] [mkVarE field_var]

copyObjectType k ty =
  case k
  of IntIndexK -> varApp (pyonBuiltin The_IInt) [ty]
     BareK     -> ty `FunT` varApp (pyonBuiltin The_OutPtr) [ty] `FunT`
                  VarT (pyonBuiltin The_Store)
     ValK      -> varApp (pyonBuiltin The_SizeAlignVal) [ty]

runCopy :: CopyCompute CopyData -> ReprCompute ExpM
runCopy m = runSubcomputation derive_premise create_result m
  where
    derive_premise :: Entry Var -> ReprCompute CopyData
    derive_premise (k, ty, v) = do
      -- Get the Repr object for this premise
      premise_v <- lookupOrCreatePremise adtRepr k ty

      case k of
        ValK -> do
          -- Premise is already a @SizeAlignVal t@
          return $ TVal ty (varE' premise_v)
        BareK -> do
          -- Convert a @Repr t@ to a copy method
          tenv <- getTypeEnv
          expr <- caseE (mkVarE premise_v)
                  [mkAlt tenv (pyonBuiltin The_repr) [ty]
                   (\ [] [_, copy, _, _, _] -> mkVarE copy)]
          return $ TBare ty expr
        IntIndexK ->
          -- Int indices are the same for both computations
          return $ TInt ty (varE' premise_v)

    create_result bindings deriv = 
      return $ foldr make_let_binding (trExp deriv) bindings
      where
        make_let_binding (k, ty, (v, derivation)) e =
          let binder_type = copyObjectType k ty
              rhs = trExp derivation
          in ExpM $ LetE defaultExpInfo (patM $ v ::: binder_type) rhs e

-- Get the derivation in sum-of-products form
products deriv =
  case deriv
  of TIUnion xs -> map from_product xs
     TITag {}   -> repeat [] -- Unknown number of empty products
     _          -> [from_product deriv]
  where
    from_product (TIProduct (TITag {} : xs)) = xs
    from_product (TIProduct xs)              = xs

-------------------------------------------------------------------------------

type ReprData = TypedData Repr

type ReprCompute a = Compute Var ReprData a

-- | Computation of @Repr@ dictionaries.
--   Kind 'val' are represented by @SizeAlignVal t@ objects.
--   Kind 'bare' is represented by @Repr t@ objects.
adtRepr :: Algorithm Var ReprData
adtRepr =
  Algorithm
  { lcNewEvidence = \_ _ -> newAnonymousVar ObjectLevel
  , lcUseEvidence = useEvidence
  , lcIntType     = valueRepr (VarT $ pyonBuiltin The_int)
  , lcUintType    = valueRepr (VarT $ pyonBuiltin The_uint)
  , lcFloatType   = valueRepr (VarT $ pyonBuiltin The_float)
  , lcBoolType    = valueRepr (VarT $ pyonBuiltin The_bool)
  , lcUnitType    = valueRepr
  , lcUninhabited = \k t -> case k
                            of BareK -> internalError "lcUninhabited: Not implemented"
                               ValK  -> valueRepr t
  , lcBox         = \t -> return $ TBox t
  , lcArrType     = arrayRepr
  , lcTag         = tagData
  , lcUnion       = return . TIUnion
  , lcProduct     = return . TIProduct
  , lcAlgType     = algebraicRepr
  , lcTypeInt     = \_ -> internalError "lcTypeInt: Not implemented"
  }

valueRepr ty = do
  -- Compute the size and alignment
  size_and_align <- runSizeAlign $ computeObjectLayout adtSizeAlign ValK ty

  -- Convert to a 'SizeAlignVal'
  s <- newAnonymousVar ObjectLevel
  a <- newAnonymousVar ObjectLevel
  let expr = ExpM $ CaseE defaultExpInfo size_and_align [alt]
      alt = AltM $ Alt (TupleDeCon [uintType, uintType])
            [patM (s ::: uintType), patM (a ::: uintType)]
            body
      body = ExpM $ ConE defaultExpInfo
             (VarCon (pyonBuiltin The_SizeAlignVal) [ty] [])
             [varE' s, varE' a]
  return $ TVal ty expr

arrayRepr (TInt size_ty size_val) (TBare elt_ty elt_val) =
  let arr_ty = varApp (pyonBuiltin The_arr) [size_ty, elt_ty]
      arr_val = primFunApp The_repr_arr_2 [size_ty, elt_ty] [size_val, elt_val]
  in return $ TBare arr_ty arr_val

-- | Get the type of the expression encoded in a TypedRepr object
reprType k ty =
  case k
  of BareK -> varApp (pyonBuiltin The_Repr) [ty]
     ValK  -> varApp (pyonBuiltin The_SizeAlignVal) [ty]

algebraicRepr ValK ty _ = valueRepr ty

algebraicRepr BareK ty _ = traceShow (text "algebraicRepr" <+> pprType ty) $ do
  let Just (data_con, ty_args) = fromVarApp ty

  -- Compute the size and alignment
  sizealign <- do
    size_and_align <- runSizeAlign $ computeObjectLayout adtSizeAlign BareK ty
  
    -- Convert to a 'SizeAlign'
    s <- newAnonymousVar ObjectLevel
    a <- newAnonymousVar ObjectLevel
    let expr = ExpM $ CaseE defaultExpInfo size_and_align [alt]
        alt = AltM $ Alt (TupleDeCon [uintType, uintType])
              [patM (s ::: uintType), patM (a ::: uintType)]
              body
        body = ExpM $ ConE defaultExpInfo
               (VarCon (pyonBuiltin The_SizeAlign) [ty] [])
               [varE' s, varE' a]
    return expr

  -- Compute the copy method
  copy <- runCopy $ computeObjectLayout adtCopy BareK ty

  -- Create conversion methods.  'StoredBox' has a special conversion method.
  (to_boxed, from_boxed) <-
    if (data_con `isPyonBuiltin` The_Ref)
    then conversionMethods_StoredBox ty_args
    else conversionMethods ty copy

  let false =
        ExpM $ ConE defaultExpInfo (VarCon (pyonBuiltin The_False) [] []) []
  let repr_exp =
        ExpM $ ConE defaultExpInfo
        (VarCon (pyonBuiltin The_repr) [ty] [])
        [sizealign, copy, to_boxed, from_boxed, false]

  return $ TBare ty repr_exp

-- | Create the code for converting between boxed and bare types
conversionMethods ty copy = do
  let boxed_type = varApp (pyonBuiltin The_Boxed) [ty]
      ret_type = varApp (pyonBuiltin The_OutPtr) [ty]
      writer_type = ret_type `FunT` VarT (pyonBuiltin The_Store)
  from_boxed <-
    lamE $ mkFun [] (\ [] -> return ([boxed_type, ret_type],
                                     VarT (pyonBuiltin The_Store)))
    (\ [] [x, r] -> do
        tenv <- getTypeEnv
        caseE (mkVarE x)
          [mkAlt tenv (pyonBuiltin The_boxed) [ty]
           (\ [] [y] -> return $ appE' copy [] [varE' y, varE' r])])
  to_boxed <-
    lamE $ mkFun [] (\ [] -> return ([writer_type], boxed_type))
    (\ [] [x] ->
      let con = VarCon (pyonBuiltin The_boxed) [ty] []
      in return $ ExpM $ ConE defaultExpInfo con [varE' x])
  return (to_boxed, from_boxed)

-- | Create the code for converting a 'StoredBox' between
--   boxed and bare types.
conversionMethods_StoredBox [arg_ty] = do
  let bare_type = varApp (pyonBuiltin The_Ref) [arg_ty]
      ret_type = varApp (pyonBuiltin The_OutPtr) [bare_type]
      writer_type = ret_type `FunT` VarT (pyonBuiltin The_Store)
  -- Convert from @StoredBox t@ to @t@
  tenv <- getTypeEnv
  from_boxed <-
    lamE $ mkFun [] (\ [] -> return ([arg_ty, ret_type],
                                     VarT (pyonBuiltin The_Store)))
    (\ [] [x, r] ->
        let con = VarCon (pyonBuiltin The_ref) [arg_ty] []
        in return $ ExpM $ ConE defaultExpInfo con [varE' x, varE' r])
  to_boxed <-
    lamE $ mkFun [] (\ [] -> return ([writer_type], arg_ty))
    (\ [] [w] ->
      caseE (appExp (mkVarE $ pyonBuiltin The_StuckBox) [bare_type] [mkVarE w])
      [mkAlt tenv (pyonBuiltin The_stuckBox) [bare_type]
       (\ [] [x] ->
         caseE (mkVarE x)
         [mkAlt tenv (pyonBuiltin The_ref) [arg_ty]
          (\ [] [y] -> mkVarE y)])])
  return (to_boxed, from_boxed)

-------------------------------------------------------------------------------
