-- | This module exports one function, which is called to initialize the
-- untyped built-in constants.  It inhabits a separate file due to module 
-- dependences.

{-# LANGUAGE TemplateHaskell, DoRec #-}
module Untyped.InitializeBuiltins
       (initializeTIBuiltins, printTIBuiltinGlobals)
where

import Control.Concurrent.MVar
import Control.Monad
import qualified Language.Haskell.TH as TH

import Common.Error
import Common.Label
import Common.THRecord
import qualified Builtins.Builtins as SystemF
import qualified SystemF.Syntax as SystemF
import Untyped.Data
import Untyped.Kind
import Untyped.Syntax
import Untyped.HMType
import Untyped.TypeAssignment
import Untyped.GenSystemF
import Untyped.Unification
import Untyped.BuiltinsTH
import Untyped.Builtins
import qualified Type.Type

pyonBuiltin = SystemF.pyonBuiltin

f @@ g = appTy f g

-- | Create an 'untyped' type constructor that corresponds to the given
-- System F type constructor
builtinTyCon name kind sf_con =
  let y = Type.Type.VarT sf_con
  in mkTyCon (builtinLabel name) kind y

shapeType ty = TFunAppTy (tiBuiltin the_con_shape) [ty]

-- | Create the type of an iterator/stream.
--   The first argument is the stream shape, the second is the element type.
iterType :: HMType -> HMType -> HMType
iterType shp ty =
  ConTy (tiBuiltin the_con_iter) @@ (shapeType shp) @@ ty

listIterType = iterType (ConTy (tiBuiltin the_con_list))
matrixIterType = iterType (ConTy (tiBuiltin the_con_array2))

-------------------------------------------------------------------------------
-- Class initialization

-- | Create a class method variable's signature from the class method's
-- signature.
mkMethodType :: Class -> TyScheme -> TyScheme
mkMethodType cls (TyScheme qvars cst fot) =
  let cls_var = clsParam $ clsSignature cls
      qvars' = cls_var : qvars
      cst' = (ConTy cls_var `IsInst` cls) : cst
  in TyScheme qvars' cst' fot

-- | Create a class method.
--
-- The returned method is added to the fields of the class, so the 'cls' 
-- parameter must be used lazily.
mkClassMethod cls index name sig = do
  -- Add the class parameter and class constraint to the method's signature 
  let method_sig = mkMethodType cls sig
      ass = methodAssignment cls index method_sig
  var <- predefinedVariable (Just $ builtinLabel name) ass
  return $ ClassMethod name sig var

getClassMethod :: Class -> Int -> ClassMethod
getClassMethod cls ix
  | ix < 0 || ix >= length (clsMethods cls) = internalError "getClassMethod"
  | otherwise = clsMethods cls !! ix

-- | Look up a method of the given class and return its type scheme
classMethodType :: (TIBuiltins -> Class) -> Int -> TyScheme
classMethodType cls_field index =
  let cls = tiBuiltin cls_field
  in mkMethodType cls (clmSignature $ getClassMethod cls index)

monomorphicInstance cls ty methods =
  mkInstance [] [] (clsSignature cls) ty Nothing methods

monomorphicExplicitInstance cls ty con methods =
  mkInstance [] [] (clsSignature cls) ty (Just con) methods

polyInstance qvars cst cls ty methods =
  mkInstance qvars cst (clsSignature cls) ty Nothing methods

polyExplicitInstance qvars cst cls ty con methods =
  mkInstance qvars cst (clsSignature cls) ty (Just con) methods

mkTyFunction :: String -> Kind -> Constraint -> Type.Type.Var
             -> [TyFamilyInstance]
             -> IO (TyCon, TyFamily)
mkTyFunction name kind cst sf_var instances = do
  rec { con <- newTyFun (builtinLabel name) kind family
      ; let family = mkTyFamily name con cst sf_var instances
      }
  return (con, family)

mkShapeTyFun = do
  rec { (con, fam) <- mkTyFunction "shape" shape_kind []
                      (pyonBuiltin SystemF.The_shape)
                      [list_instance, array1_instance, array2_instance,
                       listView_instance, matrixView_instance,
                       iter_instance]

      ; let list_instance =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_list)
              (ConTy $ tiBuiltin the_con_dim1)
      ; let array1_instance =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_array1)
              (ConTy $ tiBuiltin the_con_dim1)
      ; let array2_instance =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_array2)
              (ConTy $ tiBuiltin the_con_dim2)
      ; let listView_instance =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_view1)
              (ConTy $ tiBuiltin the_con_dim1)
      ; let matrixView_instance =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_view2)
              (ConTy $ tiBuiltin the_con_dim2)
      ; sh <- newTyVar Star Nothing
      ; let iter_instance =
              mkTyFamilyInstance [sh] [] (tfSignature fam)
              (ConTy (tiBuiltin the_con_iter) @@ ConTy sh)
              (ConTy sh)
      }
  return con
  where
    shape_kind = (Star :-> Star) :-> Star

mkArrayTyFun = do
  rec { (con, fam) <- mkTyFunction "array" (Star :-> Star :-> Star) []
                      (pyonBuiltin SystemF.The_array)
                      [inst0, inst1, inst2]

      ; let inst0 =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_dim0)
              (ConTy $ tiBuiltin the_con_array0)
      ; let inst1 =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_dim1)
              (ConTy $ tiBuiltin the_con_array1)
      ; let inst2 =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_dim2)
              (ConTy $ tiBuiltin the_con_array2)
      }
  return con

mkIndexTyFun = do
  rec { (con, fam) <- mkTyFunction "index" (Star :-> Star) []
                      (pyonBuiltin SystemF.The_index)
                      [list_instance, matrix_instance]
      ; let list_instance =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_dim1)
              int_type
      ; let matrix_instance =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_dim2)
              (TupleTy 2 @@ int_type @@ int_type)
      }
  return con
  where
   int_type = ConTy $ tiBuiltin the_con_int

mkSliceTyFun = do
  rec { (con, fam) <- mkTyFunction "slice" (Star :-> Star) []
                      (pyonBuiltin SystemF.The_slice)
                      [list_instance, matrix_instance]
      ; let list_instance =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_dim1)
              slice_type
      ; let matrix_instance =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_dim2)
              (TupleTy 2 @@ slice_type @@ slice_type)
      }
  return con
  where
   slice_type = ConTy $ tiBuiltin the_con_SliceObject
   int_type = ConTy $ tiBuiltin the_con_int

mkViewTyFun = do
  rec { (con, fam) <- mkTyFunction "view" (Star :-> Star :-> Star) []
                      (pyonBuiltin SystemF.The_view)
                      [list_instance, matrix_instance]
      ; let list_instance =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_dim1)
              (ConTy $ tiBuiltin the_con_view1)
      ; let matrix_instance =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_dim2)
              (ConTy $ tiBuiltin the_con_view2)
      }
  return con

{- mkShapeElimTyFun = do
  rec { (con, fam) <- mkTyFunction "shape_eliminator" (Star :-> Star :-> Star) []
                      (pyonBuiltin SystemF.The_shape_eliminator)
                      [list_instance, matrix_instance]
      ; let list_instance =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_dim1)
              (ConTy $ tiBuiltin the_con_ListShapeEliminator)
      ; let matrix_instance =
              mkTyFamilyInstance [] [] (tfSignature fam)
              (ConTy $ tiBuiltin the_con_dim2)
              (ConTy $ tiBuiltin the_con_MatrixShapeEliminator)
      }
  return con -}

mkEqClass = do
  rec { a <- newTyVar Star Nothing
        ; let compareScheme = monomorphic $ functionType [ConTy a, ConTy a] (ConTy $ tiBuiltin the_con_bool)

        ; let cls = mkClass "Eq" a []
                    (pyonBuiltin SystemF.The_EqDict)
                    (pyonBuiltin SystemF.The_eqDict)
                    [eq, ne]
                    [int_instance, float_instance, tuple2_instance]
  
        ; eq <- mkClassMethod cls 0 "__eq__" compareScheme
        ; ne <- mkClassMethod cls 1 "__ne__" compareScheme

        ; let int_instance =
               monomorphicInstance cls
               (ConTy $ tiBuiltin the_con_int)
               [ InstanceMethod $
                 pyonBuiltin SystemF.The_EqDict_int_eq
               , InstanceMethod $
                 pyonBuiltin SystemF.The_EqDict_int_ne]
              float_instance =
               monomorphicInstance cls
               (ConTy $ tiBuiltin the_con_float)
               [ InstanceMethod $
                 pyonBuiltin SystemF.The_EqDict_float_eq
               , InstanceMethod $
                 pyonBuiltin SystemF.The_EqDict_float_ne]
        ; tuple2_instance <- do
          a <- newTyVar Star Nothing
          b <- newTyVar Star Nothing
          return $ polyInstance
                   [a, b]
                   [ConTy a `IsInst` cls, ConTy b `IsInst` cls]
                   cls
                   (TupleTy 2 @@ ConTy a @@ ConTy b)
                   [ InstanceMethod $ pyonBuiltin SystemF.The_EqDict_Tuple2_eq,
                     InstanceMethod $ pyonBuiltin SystemF.The_EqDict_Tuple2_ne]
        }
  return cls

mkOrdClass = do
  rec { a <- newTyVar Star Nothing
        ; let compareScheme = monomorphic $ functionType [ConTy a, ConTy a] (ConTy $ tiBuiltin the_con_bool)

        ; let cls = mkClass "Ord" a [ConTy a `IsInst` tiBuiltin the_c_Eq]
                    (pyonBuiltin SystemF.The_OrdDict)
                    (pyonBuiltin SystemF.The_ordDict)
                    [lt, le, gt, ge]
                    [int_instance, float_instance, tuple2_instance]

        ; lt <- mkClassMethod cls 0 "__lt__" compareScheme
        ; le <- mkClassMethod cls 1 "__le__" compareScheme
        ; gt <- mkClassMethod cls 2 "__gt__" compareScheme
        ; ge <- mkClassMethod cls 3 "__ge__" compareScheme

        ; let int_instance =
                monomorphicInstance cls
                (ConTy $ tiBuiltin the_con_int)
                [ InstanceMethod $
                  pyonBuiltin SystemF.The_OrdDict_int_lt
                , InstanceMethod $
                  pyonBuiltin SystemF.The_OrdDict_int_le
                , InstanceMethod $
                  pyonBuiltin SystemF.The_OrdDict_int_gt
                , InstanceMethod $
                  pyonBuiltin SystemF.The_OrdDict_int_ge]
              float_instance =
                monomorphicInstance cls
                (ConTy $ tiBuiltin the_con_float)
                [ InstanceMethod $
                  pyonBuiltin SystemF.The_OrdDict_float_lt
                , InstanceMethod $
                  pyonBuiltin SystemF.The_OrdDict_float_le
                , InstanceMethod $
                  pyonBuiltin SystemF.The_OrdDict_float_gt
                , InstanceMethod $
                  pyonBuiltin SystemF.The_OrdDict_float_ge]

        ; tuple2_instance <- do
            a <- newTyVar Star Nothing
            b <- newTyVar Star Nothing
            return $ polyInstance [a, b]
                     [ConTy a `IsInst` cls, ConTy b `IsInst` cls]
                     cls
                     (TupleTy 2 @@ ConTy a @@ ConTy b)
                     [ InstanceMethod $ pyonBuiltin SystemF.The_OrdDict_Tuple2_lt
                     , InstanceMethod $ pyonBuiltin SystemF.The_OrdDict_Tuple2_le
                     , InstanceMethod $ pyonBuiltin SystemF.The_OrdDict_Tuple2_gt
                     , InstanceMethod $ pyonBuiltin SystemF.The_OrdDict_Tuple2_ge]
        }
  return cls

mkTraversableClass = do
  t <- newTyVar (Star :-> Star) Nothing
  iter_scheme <-
    forallType [Star] $ \[a] ->
    let aT = ConTy a
        tT = ConTy t
    in ([passable aT], functionType [tT @@ aT] (iterType tT aT))

  build_scheme <-
    forallType [Star] $ \[a] ->
    let aT = ConTy a
        tT = ConTy t
    in ([passable aT], functionType [iterType tT aT] (tT @@ aT))

  domain_scheme <-
    forallType [Star] $ \[a] ->
    let aT = ConTy a
        tT = ConTy t
    in ([passable aT], functionType [tT @@ aT] (shapeType tT))

  rec { let cls = mkClass "Traversable" t []
                  (pyonBuiltin SystemF.The_TraversableDict)
                  (pyonBuiltin SystemF.The_traversableDict)
                  [domain, iter, build]
                  [list_instance, array1_instance, array2_instance,
                   listView_instance, matrixView_instance,
                   iter_instance]

      ; domain <- mkClassMethod cls 0 "domain" domain_scheme
      ; iter <- mkClassMethod cls 1 "__iter__" iter_scheme
      ; build <- mkClassMethod cls 2 "__build__" build_scheme
  
      ; sh <- newTyVar Star Nothing

      ; let list_instance =
                monomorphicInstance cls
                (ConTy $ tiBuiltin the_con_list)
                [ InstanceMethod $
                  pyonBuiltin SystemF.The_TraversableDict_list_domain
                , InstanceMethod $
                  pyonBuiltin SystemF.The_TraversableDict_list_traverse
                , InstanceMethod $
                  pyonBuiltin SystemF.The_TraversableDict_list_build]

            array2_instance =
                monomorphicInstance cls
                (ConTy $ tiBuiltin the_con_array2)
                [ InstanceMethod $
                  pyonBuiltin SystemF.The_TraversableDict_array2_domain
                , InstanceMethod $
                  pyonBuiltin SystemF.The_TraversableDict_array2_traverse
                , InstanceMethod $
                  pyonBuiltin SystemF.The_TraversableDict_array2_build]

            array1_instance =
                monomorphicInstance cls
                (ConTy $ tiBuiltin the_con_array1)
                [ InstanceMethod $
                  pyonBuiltin SystemF.The_TraversableDict_array1_domain
                , InstanceMethod $
                  pyonBuiltin SystemF.The_TraversableDict_array1_traverse
                , InstanceMethod $
                  pyonBuiltin SystemF.The_TraversableDict_array1_build]

            listView_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_view1)
              [ InstanceMethod $
                pyonBuiltin SystemF.The_TraversableDict_view1_domain
              , InstanceMethod $
                pyonBuiltin SystemF.The_TraversableDict_view1_traverse
              , InstanceMethod $
                pyonBuiltin SystemF.The_TraversableDict_view1_build]

            matrixView_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_view2)
              [ InstanceMethod $
                pyonBuiltin SystemF.The_TraversableDict_view2_domain
              , InstanceMethod $
                pyonBuiltin SystemF.The_TraversableDict_view2_traverse
              , InstanceMethod $
                pyonBuiltin SystemF.The_TraversableDict_view2_build]

            iter_instance =
              -- A stream of anything is iterable
              polyInstance [sh] [] cls
              (ConTy (tiBuiltin the_con_iter) @@ ConTy sh)
              [ InstanceMethod $
                pyonBuiltin SystemF.The_TraversableDict_Stream_domain
              , InstanceMethod $
                pyonBuiltin SystemF.The_TraversableDict_Stream_traverse
              , InstanceMethod $
                pyonBuiltin SystemF.The_TraversableDict_Stream_build] }

  return cls

mkShapeClass = do
  sh <- newTyVar Star Nothing
  let index_type = TFunAppTy (tiBuiltin the_con_index) [ConTy sh]
      slice_type = TFunAppTy (tiBuiltin the_con_slice) [ConTy sh]

  let indices_scheme =
        monomorphic $ functionType [ConTy sh] (ConTy (tiBuiltin the_con_iter) @@ ConTy sh @@ index_type)

  flattenStreamScheme <- forallType [Star] $ \[a] ->
    let aT = ConTy a
        shT = ConTy sh
    in ([passable aT],
        functionType [ConTy (tiBuiltin the_con_iter) @@ shT @@ aT]
        (iterType (ConTy $ tiBuiltin the_con_list) aT))

  map_scheme <- zipWithN_scheme (ConTy sh) 1
  zip_scheme <- zipWithN_scheme (ConTy sh) 2
  zip3_scheme <- zipWithN_scheme (ConTy sh) 3
  zip4_scheme <- zipWithN_scheme (ConTy sh) 4
  let in_range_scheme =
        monomorphic $
        functionType [ConTy sh, index_type]
        (ConTy $ tiBuiltin the_con_bool)
  slice_scheme <-
    forallType [Star :-> Star, Star] $ \[t, a] ->
    let tT = ConTy t
        aT = ConTy a
    in ([shapeType tT `IsEqual` ConTy sh,
         tT `IsInst` tiBuiltin the_c_Indexable,
         passable aT],
        functionType [slice_type]
        (TFunAppTy (tiBuiltin the_con_view) [ConTy sh] @@ aT))

  rec let cls = mkClass "Shape" sh [passable index_type, passable slice_type]
                (pyonBuiltin SystemF.The_ShapeDict)
                (pyonBuiltin SystemF.The_shapeDict)
                [indices, flattenStream, mapStream,
                 zipWithStream, zipWith3Stream, zipWith4Stream,
                 inRange, getSlice]
                [list_instance, matrix_instance]

      indices <- mkClassMethod cls 0 "indices" indices_scheme
      flattenStream <- mkClassMethod cls 1 "flattenStream" flattenStreamScheme
      mapStream <- mkClassMethod cls 2 "mapStream" map_scheme
      zipWithStream <- mkClassMethod cls 3 "zipWithStream" zip_scheme
      zipWith3Stream <- mkClassMethod cls 4 "zipWith3Stream" zip3_scheme
      zipWith4Stream <- mkClassMethod cls 5 "zipWith4Stream" zip4_scheme
      inRange <- mkClassMethod cls 6 "inRange" in_range_scheme
      getSlice <- mkClassMethod cls 7 "getSlice" slice_scheme

      let list_instance =
            monomorphicInstance cls
            (ConTy (tiBuiltin the_con_dim1))
            [ InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim1_indices,
              InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim1_flatten,
              InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim1_map,
              InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim1_zipWith,
              InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim1_zipWith3,
              InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim1_zipWith4,
              InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim1_inRange,
              InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim1_slice]
          matrix_instance =
            monomorphicInstance cls
            (ConTy (tiBuiltin the_con_dim2))
            [ InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim2_indices,
              InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim2_flatten,
              InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim2_map,
              InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim2_zipWith,
              InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim2_zipWith3,
              InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim2_zipWith4,
              InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim2_inRange,
              InstanceMethod $ pyonBuiltin SystemF.The_ShapeDict_dim2_slice]

  return cls
  where
    -- Generalized map/zipWith
    --
    -- forall (a ... z). (Repr a, ..., Repr z) =>
    -- (a -> ... -> z) -> iter sh a -> ... -> iter sh z
    zipWithN_scheme sh n =
      forallType (replicate (n+1) Star) $ \(range : domain) ->
      let constraint = [passable (ConTy tv) | tv <- range : domain]
          transform = functionType (map ConTy domain) (ConTy range)
          iter t = ConTy (tiBuiltin the_con_iter) @@ sh @@ t
          fun_type = functionType
                     (transform : [iter $ ConTy tv | tv <- domain])
                     (iter $ ConTy range)
      in (constraint, fun_type)

mkIndexableClass = do
  t <- newTyVar (Star :-> Star) Nothing
  let int_type = ConTy $ tiBuiltin the_con_int
  let t_shape = TFunAppTy (tiBuiltin the_con_shape) [ConTy t]
  at_scheme <- forallType [Star] $ \[a] ->
    ([passable (ConTy a)],
     functionType [ConTy t @@ ConTy a,
                   TFunAppTy (tiBuiltin the_con_index) [t_shape]] (ConTy a))
  get_shape_scheme <- forallType [Star] $ \[a] ->
    ([], functionType [ConTy t @@ ConTy a] t_shape)
  rec { let cls = mkClass "Indexable" t []
                  (pyonBuiltin SystemF.The_IndexableDict)
                  (pyonBuiltin SystemF.The_indexableDict)
                  [at, get_shape]
                  [list_instance, listview_instance,
                   array1_instance, array2_instance, matrixview_instance]

      ; at <- mkClassMethod cls 0 "at_point" at_scheme
      ; get_shape <- mkClassMethod cls 1 "get_shape" get_shape_scheme
      ; let list_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_list)
              [ InstanceMethod $ pyonBuiltin SystemF.The_IndexableDict_list_at_point
              , InstanceMethod $ pyonBuiltin SystemF.The_IndexableDict_list_get_shape]
      ; let listview_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_view1)
              [ InstanceMethod $ pyonBuiltin SystemF.The_IndexableDict_view1_at_point
              , InstanceMethod $ pyonBuiltin SystemF.The_IndexableDict_view1_get_shape]
      ; let matrixview_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_view2)
              [ InstanceMethod $ pyonBuiltin SystemF.The_IndexableDict_view2_at_point
              , InstanceMethod $ pyonBuiltin SystemF.The_IndexableDict_view2_get_shape]
      ; let array1_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_array1)
              [ InstanceMethod $ pyonBuiltin SystemF.The_IndexableDict_array1_at_point
              , InstanceMethod $ pyonBuiltin SystemF.The_IndexableDict_array1_get_shape]
      ; let array2_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_array2)
              [ InstanceMethod $ pyonBuiltin SystemF.The_IndexableDict_array2_at_point
              , InstanceMethod $ pyonBuiltin SystemF.The_IndexableDict_array2_get_shape]
      }
  return cls

{-
mkIndexable2Class = do
  t <- newTyVar (Star :-> Star) Nothing
  let int_type = ConTy $ tiBuiltin the_con_int
  let t_shape = TFunAppTy (tiBuiltin the_con_shape) [ConTy t]
  at_scheme <- forallType [Star] $ \[a] ->
    ([passable (ConTy a)],
     functionType [ConTy t @@ ConTy a, int_type, int_type] (ConTy a))
  -- slice takes 6 int parameters
  slice_scheme <- forallType [Star] $ \[a] ->
    ([passable (ConTy a)],
     functionType [ConTy t @@ ConTy a, int_type, int_type, int_type, int_type, int_type, int_type]
     (ConTy (tiBuiltin the_con_view1) @@ ConTy a))
  with_shape_scheme <- forallType [Star] $ \[a] ->
    ([], functionType [ConTy t @@ ConTy a] t_shape)
  rec { let cls = mkClass "Indexable2" t []
                  (pyonBuiltin SystemF.The_Indexable2Dict)
                  (pyonBuiltin SystemF.The_indexable2Dict)
                  [at, slice, with_shape]
                  [matrix_instance, matrixview_instance]

      ; at <- mkClassMethod cls 0 "at_point2" at_scheme
      ; slice <- mkClassMethod cls 1 "at_slice2" slice_scheme
      ; with_shape <- mkClassMethod cls 2 "with_shape2" with_shape_scheme
      ; let matrix_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_array2)
              [ InstanceMethod $ pyonBuiltin SystemF.The_Indexable2Dict_matrix_at_point2
              , InstanceMethod $ pyonBuiltin SystemF.The_Indexable2Dict_matrix_at_slice2
              , InstanceMethod $ pyonBuiltin SystemF.The_Indexable2Dict_matrix_with_shape2]
      ; let matrixview_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_view2)
              [ InstanceMethod $ pyonBuiltin SystemF.The_Indexable2Dict_MatrixView_at_point2
              , InstanceMethod $ pyonBuiltin SystemF.The_Indexable2Dict_MatrixView_at_slice2
              , InstanceMethod $ pyonBuiltin SystemF.The_Indexable2Dict_MatrixView_with_shape2]
      }
  return cls-}

mkAdditiveClass = do 
  rec {
  a <- newTyVar Star Nothing
  ; let binScheme = monomorphic $ functionType [ConTy a, ConTy a] (ConTy a)
        negScheme = monomorphic $ functionType [ConTy a] (ConTy a)

  ; let cls = mkClass "Additive" a []
              (pyonBuiltin SystemF.The_AdditiveDict)
              (pyonBuiltin SystemF.The_additiveDict)
              [add, sub, negate, zero]
              [int_instance, float_instance, complex_instance]

  ; add <- mkClassMethod cls 0 "__add__" binScheme
  ; sub <- mkClassMethod cls 1 "__sub__" binScheme
  ; negate <- mkClassMethod cls 2 "__negate__" negScheme
  ; zero <- mkClassMethod cls 3 "zero" $ monomorphic $ ConTy a

  ; let int_instance =
          monomorphicInstance cls
          (ConTy $ tiBuiltin the_con_int)
          [ InstanceMethod $ pyonBuiltin SystemF.The_AdditiveDict_int_add
          , InstanceMethod $ pyonBuiltin SystemF.The_AdditiveDict_int_sub
          , InstanceMethod $ pyonBuiltin SystemF.The_AdditiveDict_int_negate
          , InstanceMethod $ pyonBuiltin SystemF.The_AdditiveDict_int_zero]
        float_instance =
          monomorphicInstance cls
          (ConTy $ tiBuiltin the_con_float)
          [ InstanceMethod $ pyonBuiltin SystemF.The_AdditiveDict_float_add
          , InstanceMethod $ pyonBuiltin SystemF.The_AdditiveDict_float_sub
          , InstanceMethod $ pyonBuiltin SystemF.The_AdditiveDict_float_negate
          , InstanceMethod $ pyonBuiltin SystemF.The_AdditiveDict_float_zero]
  
  ; b <- newTyVar Star Nothing
  ; let complex_instance =
          polyInstance [b] [passable (ConTy b), ConTy b `IsInst` cls] cls
          (ConTy (tiBuiltin the_con_Complex) @@ ConTy b)
          [ InstanceMethod (pyonBuiltin SystemF.The_AdditiveDict_Complex_add)
          , InstanceMethod (pyonBuiltin SystemF.The_AdditiveDict_Complex_sub)
          , InstanceMethod (pyonBuiltin SystemF.The_AdditiveDict_Complex_negate)
          , InstanceMethod (pyonBuiltin SystemF.The_AdditiveDict_Complex_zero)]
  }
  return cls

mkMultiplicativeClass = do
  rec {
  a <- newTyVar Star Nothing
  ; let binScheme = monomorphic $ functionType [ConTy a, ConTy a] (ConTy a)
        fromIntScheme = monomorphic $
                        functionType [ConTy (tiBuiltin the_con_int)] (ConTy a)
  ; let cls = mkClass "Multiplicative" a [ConTy a `IsInst` tiBuiltin the_c_Additive]
              (pyonBuiltin SystemF.The_MultiplicativeDict)
              (pyonBuiltin SystemF.The_multiplicativeDict)
              [times, fromInt, one]
              [int_instance, float_instance, complex_instance]

  ; times <- mkClassMethod cls 0 "__mul__" binScheme
  ; fromInt <- mkClassMethod cls 1 "__fromint__" fromIntScheme
  ; one <- mkClassMethod cls 2 "one" (monomorphic (ConTy a))
  
  ; let int_instance =
          monomorphicInstance cls
          (ConTy $ tiBuiltin the_con_int)
          [ InstanceMethod $
            pyonBuiltin $ SystemF.The_MultiplicativeDict_int_mul
          , InstanceMethod $
            pyonBuiltin $ SystemF.The_MultiplicativeDict_int_fromInt
          , InstanceMethod $
            pyonBuiltin $ SystemF.The_MultiplicativeDict_int_one]
        float_instance =
          monomorphicInstance cls
          (ConTy $ tiBuiltin the_con_float)
          [ InstanceMethod $
            pyonBuiltin $ SystemF.The_MultiplicativeDict_float_mul
          , InstanceMethod $
            pyonBuiltin $ SystemF.The_MultiplicativeDict_float_fromInt
          , InstanceMethod $
            pyonBuiltin $ SystemF.The_MultiplicativeDict_float_one]
  ; b <- newTyVar Star Nothing
  ; let complex_instance =
          polyInstance [b] [ConTy b `IsInst` cls] cls
          (ConTy (tiBuiltin the_con_Complex) @@ ConTy b)
          [ InstanceMethod (pyonBuiltin SystemF.The_MultiplicativeDict_Complex_mul)
          , InstanceMethod (pyonBuiltin SystemF.The_MultiplicativeDict_Complex_fromInt)
          , InstanceMethod (pyonBuiltin SystemF.The_MultiplicativeDict_Complex_one)]
          }
  
  return cls
  
mkFloatingClass = do
  rec a <- newTyVar Star Nothing
      let binScheme = monomorphic $ functionType [ConTy a, ConTy a] (ConTy a)
          unScheme  = monomorphic $ functionType [ConTy a] (ConTy a)
          fromFloatScheme = monomorphic $
                            functionType [ConTy $ tiBuiltin the_con_float] (ConTy a)
      let cls = mkClass "Floating" a []
                (pyonBuiltin SystemF.The_FloatingDict)
                (pyonBuiltin SystemF.The_floatingDict)
                [fromfloat, power, expfn, logfn, sqrtfn,
                 sinfn, cosfn, tanfn, pi]
                [float_instance, complex_instance]

      fromfloat <- mkClassMethod cls 0 "__fromfloat__" fromFloatScheme
      power <- mkClassMethod cls 1 "__power__" binScheme
      expfn <- mkClassMethod cls 2 "exp" unScheme
      logfn <- mkClassMethod cls 3 "log" unScheme
      sqrtfn <- mkClassMethod cls 4 "sqrt" unScheme
      sinfn <- mkClassMethod cls 5 "sin" unScheme
      cosfn <- mkClassMethod cls 6 "cos" unScheme
      tanfn <- mkClassMethod cls 7 "tan" unScheme
      pi <- mkClassMethod cls 8 "pi" (monomorphic (ConTy a))
  
      let float_instance =
            monomorphicInstance cls
            (ConTy $ tiBuiltin the_con_float)
            [ InstanceMethod $
              pyonBuiltin $ SystemF.The_FloatingDict_float_fromfloat
            , InstanceMethod $
              pyonBuiltin $ SystemF.The_FloatingDict_float_power
            , InstanceMethod $
              pyonBuiltin $ SystemF.The_FloatingDict_float_exp
            , InstanceMethod $
              pyonBuiltin $ SystemF.The_FloatingDict_float_log
            , InstanceMethod $
              pyonBuiltin $ SystemF.The_FloatingDict_float_sqrt
            , InstanceMethod $
              pyonBuiltin $ SystemF.The_FloatingDict_float_sin
            , InstanceMethod $
              pyonBuiltin $ SystemF.The_FloatingDict_float_cos
            , InstanceMethod $
              pyonBuiltin $ SystemF.The_FloatingDict_float_tan
            , InstanceMethod $
              pyonBuiltin $ SystemF.The_FloatingDict_float_pi]

      b <- newTyVar Star Nothing
      let complex_instance =
             polyInstance [b]
             [ConTy b `IsInst` tiBuiltin the_c_Multiplicative,
              ConTy b `IsInst` tiBuiltin the_c_Fractional,
              ConTy b `IsInst` cls]
             cls
             (ConTy (tiBuiltin the_con_Complex) @@ ConTy b)
             [ InstanceMethod $
               pyonBuiltin SystemF.The_FloatingDict_Complex_fromfloat
             , InstanceMethod $
               pyonBuiltin SystemF.The_FloatingDict_Complex_power
             , InstanceMethod $
               pyonBuiltin SystemF.The_FloatingDict_Complex_exp
             , InstanceMethod $
               pyonBuiltin SystemF.The_FloatingDict_Complex_log
             , InstanceMethod $
               pyonBuiltin SystemF.The_FloatingDict_Complex_sqrt
             , InstanceMethod $
               pyonBuiltin SystemF.The_FloatingDict_Complex_sin
             , InstanceMethod $
               pyonBuiltin SystemF.The_FloatingDict_Complex_cos
             , InstanceMethod $
               pyonBuiltin SystemF.The_FloatingDict_Complex_tan
             , InstanceMethod $
               pyonBuiltin SystemF.The_FloatingDict_Complex_pi]
  
  return cls
  
mkVectorClass = do
  rec a <- newTyVar Star Nothing
      let float_type = ConTy $ tiBuiltin the_con_float
          normScheme = monomorphic $ functionType [ConTy a] float_type
          scaleScheme = monomorphic $
                        functionType [ConTy a, float_type] (ConTy a)
          dotScheme = monomorphic $
                      functionType [ConTy a, ConTy a] float_type

      let cls =
            mkClass "Vector" a [ConTy a `IsInst` tiBuiltin the_c_Additive]
            (pyonBuiltin SystemF.The_VectorDict)
            (pyonBuiltin SystemF.The_vectorDict)
            [scale, magnitude, dot]
            [float_instance, complex_instance]

      scale <- mkClassMethod cls 0 "scale" scaleScheme
      magnitude <- mkClassMethod cls 1 "magnitude" normScheme
      dot <- mkClassMethod cls 2 "dot" dotScheme

      let float_instance =
            monomorphicInstance cls
            (ConTy $ tiBuiltin the_con_float)
            [ InstanceMethod $
              pyonBuiltin SystemF.The_VectorDict_float_scale
            , InstanceMethod $
              pyonBuiltin SystemF.The_VectorDict_float_magnitude
            , InstanceMethod $
              pyonBuiltin SystemF.The_VectorDict_float_dot]

      b <- newTyVar Star Nothing
      let complex_instance =
            polyInstance [b] [ConTy b `IsInst` cls] cls
            (ConTy (tiBuiltin the_con_Complex) @@ ConTy b)
            [ InstanceMethod $
              pyonBuiltin SystemF.The_VectorDict_Complex_scale
            , InstanceMethod $
              pyonBuiltin SystemF.The_VectorDict_Complex_magnitude
            , InstanceMethod $
              pyonBuiltin SystemF.The_VectorDict_Complex_dot]

  return cls

mkRemainderClass = do
  a <- newTyVar Star Nothing
  let divScheme = monomorphic $
                  functionType [ConTy a, ConTy a] (ConTy (tiBuiltin the_con_int))
      remScheme = monomorphic $
                  functionType [ConTy a, ConTy a] (ConTy a)
  rec let cls =
            mkClass "Remainder" a [ConTy a `IsInst` tiBuiltin the_c_Multiplicative]
            (pyonBuiltin SystemF.The_RemainderDict)
            (pyonBuiltin SystemF.The_remainderDict)
            [divide, remainder]
            [int_instance, float_instance]
      divide <- mkClassMethod cls 0 "__floordiv__" divScheme
      remainder <- mkClassMethod cls 1 "__mod__" remScheme
      let int_instance =
            monomorphicInstance cls
            (ConTy $ tiBuiltin the_con_int)
            [ InstanceMethod $
              pyonBuiltin $ SystemF.The_RemainderDict_int_floordiv
            , InstanceMethod $
              pyonBuiltin $ SystemF.The_RemainderDict_int_mod]
          float_instance =
            monomorphicInstance cls
            (ConTy $ tiBuiltin the_con_float)
            [ InstanceMethod $
              pyonBuiltin $ SystemF.The_RemainderDict_float_floordiv
            , InstanceMethod $
              pyonBuiltin $ SystemF.The_RemainderDict_float_mod]

  return cls

mkFractionalClass = do
  a <- newTyVar Star Nothing
  let divScheme = monomorphic $
                  functionType [ConTy a, ConTy a] (ConTy a)
  rec let cls =
            mkClass "Fractional" a [ConTy a `IsInst` tiBuiltin the_c_Multiplicative]
            (pyonBuiltin SystemF.The_FractionalDict)
            (pyonBuiltin SystemF.The_fractionalDict)
            [divide]
            [float_instance, complex_instance]

      divide <- mkClassMethod cls 0 "__div__" divScheme
      let float_instance =
            monomorphicInstance cls
            (ConTy $ tiBuiltin the_con_float)
            [ InstanceMethod $
              pyonBuiltin $ SystemF.The_FractionalDict_float_div]

      b <- newTyVar Star Nothing
      let complex_instance =
            polyInstance [b] [ConTy b `IsInst` cls] cls
            (ConTy (tiBuiltin the_con_Complex) @@ ConTy b)
            [ InstanceMethod $ pyonBuiltin SystemF.The_FractionalDict_Complex_div]

  return cls

mkPassableClass = do
  rec {
  a <- newTyVar Star Nothing
  ; let cls = mkClass "Repr" a []
              (pyonBuiltin SystemF.The_Repr)
              (internalError "Class 'Repr' has no dictionary constructor")
              []
              [int_instance, float_instance, bool_instance, none_instance,
               maybe_val_instance,
               complex_instance, sliceobject_instance,
               dim1_instance, dim2_instance,
               any_instance,
               list_instance,
               array1_instance, array2_instance,
               iter_instance,
               view1_instance, view2_instance,
               tuple2_instance, tuple3_instance,
               tuple4_instance]
  
  ; let int_instance =
          monomorphicExplicitInstance cls (ConTy $ tiBuiltin the_con_int)
          (pyonBuiltin SystemF.The_repr_int) []
  ; let float_instance =
          monomorphicExplicitInstance cls (ConTy $ tiBuiltin the_con_float)
          (pyonBuiltin SystemF.The_repr_float) []
  ; let bool_instance =
          monomorphicExplicitInstance cls (ConTy $ tiBuiltin the_con_bool)
          (pyonBuiltin SystemF.The_repr_bool) []
  ; let none_instance =
          monomorphicExplicitInstance cls (ConTy $ tiBuiltin the_con_NoneType)
          (pyonBuiltin SystemF.The_repr_NoneType) []
  ; let dim1_instance =
          monomorphicExplicitInstance cls (ConTy $ tiBuiltin the_con_dim1)
          (pyonBuiltin SystemF.The_repr_dim1) []
  ; let dim2_instance =
          monomorphicExplicitInstance cls (ConTy $ tiBuiltin the_con_dim2)
          (pyonBuiltin SystemF.The_repr_dim2) []
  ; let any_instance =
          monomorphicExplicitInstance cls (ConTy $ tiBuiltin the_con_Any)
          (pyonBuiltin SystemF.The_repr_Any) []
  ; let sliceobject_instance =
          monomorphicExplicitInstance cls (ConTy $ tiBuiltin the_con_SliceObject)
          (pyonBuiltin SystemF.The_repr_SliceObject) []
        
  ; b <- newTyVar Star Nothing
  ; c <- newTyVar Star Nothing
  ; let maybe_val_instance =
          -- We don't need a Repr instance for the contained type.  Since
          -- it's a value, it can be computed on demand.
          polyExplicitInstance [b] [] cls
          (ConTy (tiBuiltin the_con_MaybeVal) @@ ConTy b)
          (pyonBuiltin SystemF.The_repr_MaybeVal)
          []
  ; let list_instance =
          polyExplicitInstance [b] [passable $ ConTy b] cls
          (ConTy (tiBuiltin the_con_list) @@ ConTy b)
          (pyonBuiltin SystemF.The_repr_list)
          []
  ; let array1_instance =
          polyExplicitInstance [b] [passable $ ConTy b] cls
          (ConTy (tiBuiltin the_con_array1) @@ ConTy b)
          (pyonBuiltin SystemF.The_repr_array1)
          []
  ; let array2_instance =
          polyExplicitInstance [b] [passable $ ConTy b] cls
          (ConTy (tiBuiltin the_con_array2) @@ ConTy b)
          (pyonBuiltin SystemF.The_repr_array2)
          []
  ; let iter_instance =
          polyExplicitInstance [b, c] [] cls
          (ConTy (tiBuiltin the_con_iter) @@ ConTy b @@ ConTy c)
          (pyonBuiltin SystemF.The_repr_Stream)
          []
  ; let view1_instance =
          polyExplicitInstance [b] [] cls
          (ConTy (tiBuiltin the_con_view1) @@ ConTy b)
          (pyonBuiltin SystemF.The_repr_view1)
          []
  ; let view2_instance =
          polyExplicitInstance [b] [] cls
          (ConTy (tiBuiltin the_con_view2) @@ ConTy b)
          (pyonBuiltin SystemF.The_repr_view2)
          []
  ; let complex_instance =
          polyExplicitInstance [b] [passable $ ConTy b] cls
          (ConTy (tiBuiltin the_con_Complex) @@ ConTy b)
          (pyonBuiltin SystemF.The_repr_Complex)
          []
  ; let tuple2_instance =
          polyExplicitInstance [b, c] [passable $ ConTy b, passable $ ConTy c] cls
          (TupleTy 2 @@ ConTy b @@ ConTy c)
          (SystemF.pyonTupleReprCon 2)
          []
  ; d <- newTyVar Star Nothing
  ; let tuple3_instance =
          polyExplicitInstance [b, c, d] [passable $ ConTy b, passable $ ConTy c, passable $ ConTy d] cls
          (TupleTy 3 @@ ConTy b @@ ConTy c @@ ConTy d)
          (SystemF.pyonTupleReprCon 3)
          []
  ; e <- newTyVar Star Nothing
  ; let tuple4_instance =
          polyExplicitInstance [b, c, d, e] [passable $ ConTy b, passable $ ConTy c, passable $ ConTy d, passable $ ConTy e] cls
          (TupleTy 4 @@ ConTy b @@ ConTy c @@ ConTy d @@ ConTy e)
          (SystemF.pyonTupleReprCon 4)
          []
  }
  
  return cls

-------------------------------------------------------------------------------
-- Global function initialization

passable t = t `IsInst` tiBuiltin the_c_Repr

mkMapType = forallType [Star :-> Star, Star, Star] $ \ [t, a, b] ->
  let tT = ConTy t
      aT = ConTy a
      bT = ConTy b
  in ([ tT `IsInst` tiBuiltin the_c_Traversable
      , shapeType tT `IsInst` tiBuiltin the_c_Shape
      , passable aT
      , passable bT
      ],
      functionType [functionType [aT] bT, tT @@ aT] (tT @@ bT))

mkReduceType = forallType [Star :-> Star, Star] $ \ [t, a] ->
  let tT = ConTy t
      aT = ConTy a
  in ([tT `IsInst` tiBuiltin the_c_Traversable
      , shapeType tT `IsInst` tiBuiltin the_c_Shape
      , passable aT],
      functionType [functionType [aT, aT] aT, aT, tT @@ aT] aT)

mkReduce1Type = forallType [Star :-> Star, Star] $ \ [t, a] ->
  let tT = ConTy t
      aT = ConTy a
  in ([tT `IsInst` tiBuiltin the_c_Traversable
      , shapeType tT `IsInst` tiBuiltin the_c_Shape
      , passable aT],
      functionType [functionType [aT, aT] aT, tT @@ aT] aT)

mkZipType =
  forallType [ Star :-> Star
             , Star :-> Star
             , Star
             , Star] $ \ [t1, t2, a, b] ->
  let t1T = ConTy t1
      t2T = ConTy t2
      aT = ConTy a
      bT = ConTy b
  in ([ t1T `IsInst` tiBuiltin the_c_Traversable
      , t2T `IsInst` tiBuiltin the_c_Traversable
      , shapeType t1T `IsEqual` shapeType t2T
      , shapeType t1T `IsInst` tiBuiltin the_c_Shape
      , passable aT
      , passable bT]
     , functionType [t1T @@ aT, t2T @@ bT]
       (iterType t1T (TupleTy 2 @@ aT @@ bT)))

mkZip3Type =
  forallType [ Star :-> Star
             , Star :-> Star
             , Star :-> Star
             , Star
             , Star
             , Star] $ \ [t1, t2, t3, a, b, c] ->
  let t1T = ConTy t1
      t2T = ConTy t2
      t3T = ConTy t3
      aT = ConTy a
      bT = ConTy b
      cT = ConTy c
  in ([ t1T `IsInst` tiBuiltin the_c_Traversable
      , t2T `IsInst` tiBuiltin the_c_Traversable
      , t3T `IsInst` tiBuiltin the_c_Traversable
      , shapeType t1T `IsEqual` shapeType t2T
      , shapeType t2T `IsEqual` shapeType t3T
      , shapeType t1T `IsInst` tiBuiltin the_c_Shape
      , passable aT
      , passable bT
      , passable cT]
     , functionType [t1T @@ aT, t2T @@ bT, t3T @@ cT]
       (iterType t1T (TupleTy 3 @@ aT @@ bT @@ cT)))

mkZip4Type =
  forallType [ Star :-> Star
             , Star :-> Star
             , Star :-> Star
             , Star :-> Star
             , Star
             , Star
             , Star
             , Star] $ \ [t1, t2, t3, t4, a, b, c, d] ->
  let t1T = ConTy t1
      t2T = ConTy t2
      t3T = ConTy t3
      t4T = ConTy t4
      aT = ConTy a
      bT = ConTy b
      cT = ConTy c
      dT = ConTy d
  in ([ t1T `IsInst` tiBuiltin the_c_Traversable
      , t2T `IsInst` tiBuiltin the_c_Traversable
      , t3T `IsInst` tiBuiltin the_c_Traversable
      , t4T `IsInst` tiBuiltin the_c_Traversable
      , shapeType t1T `IsEqual` shapeType t2T
      , shapeType t2T `IsEqual` shapeType t3T
      , shapeType t3T `IsEqual` shapeType t4T
      , shapeType t1T `IsInst` tiBuiltin the_c_Shape
      , passable aT
      , passable bT
      , passable cT
      , passable dT]
     , functionType [t1T @@ aT, t2T @@ bT, t3T @@ cT, t4T @@ dT]
       (iterType t1T (TupleTy 4 @@ aT @@ bT @@ cT @@ dT)))

mkCountType =
  return $ monomorphic $
  iterType (ConTy $ tiBuiltin the_con_list) (ConTy $ tiBuiltin the_con_int)

mkRangeType =
  let int_type = ConTy $ tiBuiltin the_con_int
  in return $ monomorphic $
     functionType [int_type] (listIterType int_type)

mkLenType =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      int_type = ConTy $ tiBuiltin the_con_int
  in ([shapeType tT `IsEqual` ConTy (tiBuiltin the_con_dim1), 
       tT `IsInst` tiBuiltin the_c_Indexable],
      functionType [tT @@ aT] int_type)

mkWidthHeightType =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      int_type = ConTy $ tiBuiltin the_con_int
  in ([shapeType tT `IsEqual` ConTy (tiBuiltin the_con_dim2),
       tT `IsInst` tiBuiltin the_c_Indexable],
      functionType [tT @@ aT] int_type)

mkOuterProductType =
  forallType [Star, Star, Star] $ \[a, b, c] ->
  let aT = ConTy a
      bT = ConTy b
      cT = ConTy c
  in ([passable aT, passable bT, passable cT],
      functionType [functionType [aT, bT] cT,
                    iterType (ConTy $ tiBuiltin the_con_list) aT,
                    iterType (ConTy $ tiBuiltin the_con_list) bT]
      (iterType (ConTy $ tiBuiltin the_con_array2) cT))

mkView2Type =
  forallType [Star] $ \[a] ->
  let aT = ConTy a
      int_type = ConTy $ tiBuiltin the_con_int
      ints_type = TupleTy 2 @@ int_type @@ int_type
  in ([passable aT],
      functionType [ints_type, ints_type, functionType [ints_type] aT]
      (ConTy (tiBuiltin the_con_view2) @@ aT))

mkStencil2DType =
  forallType [Star :-> Star, Star, Star] $ \[t, a, b] ->
  let tT = ConTy t
      aT = ConTy a
      bT = ConTy b
      int_type = ConTy $ tiBuiltin the_con_int
  in ([tT `IsInst` tiBuiltin the_c_Indexable,
       shapeType tT `IsEqual` ConTy (tiBuiltin the_con_dim2),
       passable aT, passable bT],
      functionType [int_type, int_type, int_type, int_type,
                    functionType [ConTy (tiBuiltin the_con_view2) @@ aT] bT,
                    tT @@ aT]
      (ConTy (tiBuiltin the_con_array2) @@ bT))

mkRange2DType =
  return $ monomorphic $
  let int_type = ConTy $ tiBuiltin the_con_int
      int2_type = TupleTy 2 @@ int_type @@ int_type
  in functionType [int2_type] (ConTy (tiBuiltin the_con_iter) @@ ConTy (tiBuiltin the_con_dim2) @@ int2_type)

mkShift2DType =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      int_type = ConTy $ tiBuiltin the_con_int
      int2_type = TupleTy 2 @@ int_type @@ int_type
  in ([tT `IsInst` tiBuiltin the_c_Indexable,
       shapeType tT `IsEqual` ConTy (tiBuiltin the_con_dim2),
       passable aT],
      functionType [int2_type, tT @@ aT]
      (ConTy (tiBuiltin the_con_view2) @@ aT))

mkExtend2DType =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      int_type = ConTy $ tiBuiltin the_con_int
      int2_type = TupleTy 2 @@ int_type @@ int_type
  in ([tT `IsInst` tiBuiltin the_c_Indexable,
       shapeType tT `IsEqual` ConTy (tiBuiltin the_con_dim2),
       passable aT],
      functionType [int2_type, int2_type, tT @@ aT]
      (ConTy (tiBuiltin the_con_view2) @@ aT))

mkRowsColsType =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      listview a = ConTy (tiBuiltin the_con_view1) @@ a
  in ([tT `IsInst` tiBuiltin the_c_Indexable,
       shapeType tT `IsEqual` ConTy (tiBuiltin the_con_dim2),
       passable aT],
      functionType [tT @@ aT] (listview $ listview aT))

mkSafeIndexType =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      index_type = TFunAppTy (tiBuiltin the_con_index) [shapeType tT]
  in ([tT `IsInst` tiBuiltin the_c_Indexable,
       shapeType tT `IsInst` tiBuiltin the_c_Shape,
       passable aT], functionType [tT @@ aT, index_type] aT)

mkSafeSliceType =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      int_type = ConTy $ tiBuiltin the_con_int
      t_shape = TFunAppTy (tiBuiltin the_con_shape) [ConTy t]
      slice_type = TFunAppTy (tiBuiltin the_con_slice) [t_shape]
      view_type = TFunAppTy (tiBuiltin the_con_view) [t_shape]
  in ([tT `IsInst` tiBuiltin the_c_Indexable,
       shapeType tT `IsInst` tiBuiltin the_c_Shape,
       passable aT], functionType [tT @@ aT, slice_type]
                     (view_type @@ aT))

{-
mkSafeIndex2Type =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      int_type = ConTy $ tiBuiltin the_con_int
  in ([tT `IsInst` tiBuiltin the_c_Indexable2,
       passable aT], functionType [tT @@ aT, int_type, int_type] aT)

mkSafeSlice2Type =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      int_type = ConTy $ tiBuiltin the_con_int
  in ([tT `IsInst` tiBuiltin the_c_Indexable2,
       passable aT], functionType [tT @@ aT, int_type, int_type, int_type, int_type, int_type, int_type]
                     (ConTy (tiBuiltin the_con_view2) @@ aT))
-}

mkHistogramType =
  forallType [Star] $ \[sh] ->
  let int_type = ConTy $ tiBuiltin the_con_int
  in ([ConTy sh `IsInst` tiBuiltin the_c_Shape],
      functionType [int_type, int_type,
                    ConTy (tiBuiltin the_con_iter) @@ ConTy sh @@ int_type]
      (ConTy (tiBuiltin the_con_array1) @@ int_type))

mkFloorType =
  return $ monomorphic $
  functionType [ConTy $ tiBuiltin the_con_float] (ConTy $ tiBuiltin the_con_int)

mkUndefinedType =
  forallType [Star] $ \[a] -> ([], ConTy a)

mkMakelistType =
  forallType [Star] $ \[a] ->
  let aT = ConTy a
      sT = listIterType aT
      lT = ConTy (tiBuiltin the_con_list) @@ aT
  in ([passable aT], functionType [sT] lT)

mkReturnType =
  forallType [Star] $ \[a] ->
  ([passable (ConTy a)],
   functionType [ConTy a] (listIterType $ ConTy a))

mkGuardType =
  forallType [Star] $ \[a] ->
  ([passable (ConTy a)],
   functionType [ ConTy (tiBuiltin the_con_bool)
                , listIterType (ConTy a)]
   (listIterType (ConTy a)))

mkMapStreamType =
  forallType [Star :-> Star, Star, Star] $ \[t, a, b] ->
  let tT = ConTy t
      aT = ConTy a
      bT = ConTy b
  in ([shapeType tT `IsInst` tiBuiltin the_c_Shape,
       passable aT, passable bT],
      functionType [functionType [aT] bT, iterType tT aT] (iterType tT bT))

mkListIterType =
  forallType [Star, Star] $ \[sh, a] ->
  let shT = ConTy sh
      aT = ConTy a
  in ([shT `IsInst` tiBuiltin the_c_Shape],
      functionType [ConTy (tiBuiltin the_con_iter) @@ shT @@ aT]
      (iterType (ConTy $ tiBuiltin the_con_list) aT))

mkMatrixIterType =
  forallType [Star] $ \[a] ->
  let aT = ConTy a
  in ([],
      functionType [iterType (ConTy $ tiBuiltin the_con_view2) aT]
      (iterType (ConTy $ tiBuiltin the_con_array2) aT))

mkIterBindType =
  forallType [Star, Star] $ \[a, b] ->
  let aT = ConTy a
      bT = ConTy b
  in ([passable aT, passable bT],
      functionType [listIterType aT, functionType [aT] (listIterType bT)]
      (listIterType bT))

mkMakeComplexType =
  forallType [Star] $ \[a] ->
  ([], functionType [ConTy a, ConTy a]
       (ConTy (tiBuiltin the_con_Complex) @@ ConTy a))

mkJustValType =
  forallType [Star] $ \[a] ->
  ([], functionType [ConTy a] (ConTy (tiBuiltin the_con_MaybeVal) @@ ConTy a))

mkNothingValType =
  forallType [Star] $ \[a] ->
  ([], ConTy (tiBuiltin the_con_MaybeVal) @@ ConTy a)

mkSliceObjectType =
  return $ monomorphic $
  functionType [just_int, just_int, just_just_int]
  (ConTy (tiBuiltin the_con_SliceObject))
  where
    int_type = ConTy (tiBuiltin the_con_int)
    just_int = ConTy (tiBuiltin the_con_MaybeVal) @@ int_type
    just_just_int = ConTy (tiBuiltin the_con_MaybeVal) @@ just_int

mkBinaryOpType =
  forallType [Star] $ \[a] ->
  ([passable (ConTy a)], functionType [ConTy a, ConTy a] (ConTy a))

mkBinaryIntType =
  let int = ConTy (tiBuiltin the_con_int)
  in return $ monomorphic $ functionType [int, int] int

mkGlobalVar name typ con = do
  scm <- typ
  let exp pos = VarTE (SystemF.mkExpInfo pos) con
  let ass = polymorphicAssignment scm exp
  predefinedVariable (Just $ builtinLabel name) ass

mkGlobalCon name typ con = do
  scm <- typ
  let ass = constructorAssignment scm con
  predefinedVariable (Just $ builtinLabel name) ass

getClassVar name cls index = clmVariable $ getClassMethod cls index

-------------------------------------------------------------------------------
-- Main function

-- | Initialize the data structure containing all the builtin global variables 
-- and types.  The Gluon builtins and the System F builtins are used here, so 
-- they should be initialized before calling this function.
initializeTIBuiltins :: IO ()
initializeTIBuiltins = do
  is_empty <- isEmptyMVar the_TIBuiltins
  unless is_empty $ fail "TI builtins are already initialized"

  -- Create the builtins object
  bi <-
    $(let types =
            -- All types that can be referred to by name in source code.
            -- Type functions are initialized separately.
            -- The tuple structure contains:
            -- 1. Source code name
            -- 2. kind
            -- 3. system F constructor
            [ ("int", Star, [| pyonBuiltin SystemF.The_int |])
            , ("float", Star, [| pyonBuiltin SystemF.The_float |])
            , ("Complex", Star :-> Star, [| pyonBuiltin SystemF.The_Complex |])
            , ("bool", Star, [| pyonBuiltin SystemF.The_bool |])
            , ("NoneType", Star, [| pyonBuiltin SystemF.The_NoneType |])
            , ("Maybe", Star :-> Star, [| pyonBuiltin SystemF.The_Maybe |])
            , ("MaybeVal", Star :-> Star, [| pyonBuiltin SystemF.The_MaybeVal |])
            , ("SliceObject", Star, [| pyonBuiltin SystemF.The_SliceObject |])
            , ("iter", Star :-> Star :-> Star,
               [| pyonBuiltin SystemF.The_Stream |])
            , ("list", Star :-> Star, [| pyonBuiltin SystemF.The_list |])
            , ("array0", Star :-> Star, [| pyonBuiltin SystemF.The_array0 |])
            , ("array1", Star :-> Star, [| pyonBuiltin SystemF.The_array1 |])
            , ("array2", Star :-> Star, [| pyonBuiltin SystemF.The_array2 |])
            , ("view0", Star :-> Star, [| pyonBuiltin SystemF.The_view0 |])
            , ("view1", Star :-> Star, [| pyonBuiltin SystemF.The_view1 |])
            , ("view2", Star :-> Star, [| pyonBuiltin SystemF.The_view2 |])
            , ("Any", Star, [| pyonBuiltin SystemF.The_Any |])
            , ("dim0", Star, [| pyonBuiltin SystemF.The_dim0 |])
            , ("dim1", Star, [| pyonBuiltin SystemF.The_dim1 |])
            , ("dim2", Star, [| pyonBuiltin SystemF.The_dim2 |])
            ]

          type_functions =
            [ ("shape", [| pyonBuiltin SystemF.The_shape |], [| mkShapeTyFun |])
            , ("index", [| pyonBuiltin SystemF.The_index |], [| mkIndexTyFun |])
            , ("slice", [| pyonBuiltin SystemF.The_slice |], [| mkSliceTyFun |])
            , ("view", [| pyonBuiltin SystemF.The_view |], [| mkViewTyFun |])
            , ("array", [| pyonBuiltin SystemF.The_array |], [| mkArrayTyFun |])
            ]
            
          classes =
            [ ("Eq", [| mkEqClass |])
            , ("Ord", [| mkOrdClass |])
            , ("Traversable", [| mkTraversableClass |])
            , ("Shape", [| mkShapeClass |])
            , ("Indexable", [| mkIndexableClass |])
            , ("Additive", [| mkAdditiveClass |])
            , ("Multiplicative", [| mkMultiplicativeClass |])
            , ("Remainder", [| mkRemainderClass |])
            , ("Fractional", [| mkFractionalClass |])
            , ("Floating", [| mkFloatingClass |])
            , ("Vector", [| mkVectorClass |])
            , ("Repr", [| mkPassableClass |])
            ]

          globals =
            -- All global variables
            -- Their Hindley-Milner type schemes and System F translations.
            [ ("map", [| mkMapType |]
              , [| pyonBuiltin SystemF.The_fun_map |]
              ),
              ("reduce", [| mkReduceType |]
              , [| pyonBuiltin SystemF.The_fun_reduce |]
              ),
              ("reduce1", [| mkReduce1Type |]
              , [| pyonBuiltin SystemF.The_fun_reduce1 |]
              ),
              ("zip", [| mkZipType |]
              , [| pyonBuiltin SystemF.The_fun_zip |]
              ),
              ("zip3", [| mkZip3Type |]
              , [| pyonBuiltin SystemF.The_fun_zip3 |]
              ),
              ("zip4", [| mkZip4Type |]
              , [| pyonBuiltin SystemF.The_fun_zip4 |]
              ),
              ("count", [| mkCountType |]
              , [| pyonBuiltin SystemF.The_count |]
              ),
              ("range", [| mkRangeType |]
              , [| pyonBuiltin SystemF.The_range |]
              ),
              ("len", [| mkLenType |]
              , [| pyonBuiltin SystemF.The_len |]
              ),
              ("width", [| mkWidthHeightType |]
              , [| pyonBuiltin SystemF.The_width |]
              ),
              ("height", [| mkWidthHeightType |]
              , [| pyonBuiltin SystemF.The_height |]
              ),
              ("outerproduct", [| mkOuterProductType |]
              , [| pyonBuiltin SystemF.The_outerproduct |]
              ),
              ("view2", [| mkView2Type |]
              , [| pyonBuiltin SystemF.The_create_view2 |]
              ),
              ("stencil2D", [| mkStencil2DType |]
              , [| pyonBuiltin SystemF.The_stencil2D |]
              ),              
              ("extend2D", [| mkExtend2DType |]
              , [| pyonBuiltin SystemF.The_extend2D |]
              ),              
              ("shift2D", [| mkShift2DType |]
              , [| pyonBuiltin SystemF.The_shift2D |]
              ),              
              ("range2D", [| mkRange2DType |]
              , [| pyonBuiltin SystemF.The_range2D |]
              ),              
              ("rows", [| mkRowsColsType |]
              , [| pyonBuiltin SystemF.The_rows |]
              ),
              ("cols", [| mkRowsColsType |]
              , [| pyonBuiltin SystemF.The_cols |]
              ),
              ("safeIndex", [| mkSafeIndexType |]
              , [| pyonBuiltin SystemF.The_safeIndex |]
              ),
              ("safeSlice", [| mkSafeSliceType |]
              , [| pyonBuiltin SystemF.The_safeSlice |]
              ),
              ("histogram", [| mkHistogramType |]
              , [| pyonBuiltin SystemF.The_histogram |]
              ),
              ("floor", [| mkFloorType |]
              , [| pyonBuiltin SystemF.The_floor |]
              ),
              ("listiter", [| mkListIterType |]
              , [| pyonBuiltin SystemF.The_fun_asList_Stream |]
              ),
              ("matrixiter", [| mkMatrixIterType |]
              , [| pyonBuiltin SystemF.The_fun_from_MatrixView_Stream |]
              ),
              ("__undefined__", [| mkUndefinedType |]
              , [| pyonBuiltin SystemF.The_fun_undefined |]
              ),
              ("do", [| mkReturnType |]
              , [| pyonBuiltin SystemF.The_Stream1_return |]
              ),
              ("guard", [| mkGuardType |]
              , [| pyonBuiltin SystemF.The_Stream1_guard |]
              ),
              ("iterBind", [| mkIterBindType |]
              , [| pyonBuiltin SystemF.The_Stream1_bind |]
              ),
              ("__and__", [| mkBinaryIntType |]
              , [| pyonBuiltin SystemF.The_oper_BITWISEAND |]
              ),
              ("__or__", [| mkBinaryIntType |]
              , [| pyonBuiltin SystemF.The_oper_BITWISEOR |]
              ),
              ("__xor__", [| mkBinaryIntType |]
              , [| pyonBuiltin SystemF.The_oper_BITWISEXOR |]
              )
            ]
          datacons =
            [ ("complex", [| mkMakeComplexType |]
              , [| pyonBuiltin SystemF.The_complex |]
              ),
              ("justVal", [| mkJustValType |]
              , [| pyonBuiltin SystemF.The_justVal |]
              ),
              ("nothingVal", [| mkNothingValType |]
              , [| pyonBuiltin SystemF.The_nothingVal |]
              ),
              ("sliceObject", [| mkSliceObjectType |]
              , [| pyonBuiltin SystemF.The_sliceObject |]
              )
            ]
          cls_members =
            [ ([| the_c_Eq |], ["__eq__", "__ne__"])
            , ([| the_c_Ord |], ["__lt__", "__le__", "__gt__", "__ge__"])
            , ([| the_c_Traversable |], ["domain", "__iter__", "__build__"])
            , ([| the_c_Shape |], ["indices", "flattenStream", "mapStream", 
                                 "zipWithStream", "zipWith3Stream",
                                 "zipWith4Stream", "inRange", "getSlice"])
            , ([| the_c_Indexable |], ["at_point", "get_shape"])
            , ([| the_c_Additive |], ["__add__", "__sub__", "__negate__", "zero"])
            , ([| the_c_Multiplicative |], ["__mul__", "__fromint__", "one"])
            , ([| the_c_Remainder |], ["__floordiv__", "__mod__"])
            , ([| the_c_Fractional |], ["__div__"])
            , ([| the_c_Floating |], ["__fromfloat__", "__power__",
                                    "exp", "log", "sqrt",
                                    "sin", "cos", "tan", "pi"])
            , ([| the_c_Vector |], ["scale", "magnitude", "dot"])
            ]

          -- Construct initializers
          typ_initializer (name, _, con) =
            ('t':'_':name, [| return $(con) |])
          tycon_initializer (name, kind, con) =
            ("con_" ++ name, [| builtinTyCon name kind $(con) |])
          tyfun_initializer (name, con, _) =
            ('t':'_':name, [| return $(con) |])
          tyfun_con_initializer (name, _, mk_function) =
            ("con_" ++ name, mk_function)
          cls_initializer (name, mk) =
            ('c':'_':name, mk)
          global_initializer (name, typ, con) =
            ('v':'_':name, [| mkGlobalVar name $(typ) $(con) |])
          datacon_initializer (name, typ, con) =
            ('v':'_':name, [| mkGlobalCon name $(typ) $(con) |])
          cls_member_initializer (cls, members) = zipWith mb members [0..]
            where
              mb member_name index =
                ('v':'_':member_name,
                 [| -- Verify the method's name
                    let v = clmVariable $
                            getClassMethod (tiBuiltin $(cls)) index
                    in return $ if varName v /= Just (builtinLabel member_name)
                                then internalError "Inconsistent class method name"
                                else v |])

          initializers = map typ_initializer types ++
                         map tyfun_initializer type_functions ++
                         map tycon_initializer types ++
                         map tyfun_con_initializer type_functions ++
                         map cls_initializer classes ++
                         map global_initializer globals ++
                         map datacon_initializer datacons ++
                         concatMap cls_member_initializer cls_members
      in initializeRecordM tiBuiltinSpecification initializers)
  
  -- Save it
  putMVar the_TIBuiltins bi

-- | Print the names and types of all built-in variables
printTIBuiltinGlobals = do
  forM_ $(TH.listE [TH.tupE [TH.varE $ TH.mkName $ 'v':'_':name, TH.litE (TH.stringL name)]
                    | name <- pyonSourceGlobals]) $ \(x, name) -> do
    ass <- readMVar $ varTranslation $ tiBuiltin x
    putStrLn name
    print =<< runPpr (pprTyScheme $ _typeAssignmentScheme ass)
