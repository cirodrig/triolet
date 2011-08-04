-- | This module exports one function, which is called to initialize the
-- untyped built-in constants.  It inhabits a separate file due to module 
-- dependences.

{-# LANGUAGE TemplateHaskell, DoRec #-}
module Untyped.InitializeBuiltins
       (initializeTIBuiltins)
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
  let y = SystemF.TypSF (Type.Type.VarT sf_con)
  in mkTyCon (builtinLabel name) kind y

-- | Create the type of an iterator/stream.
--   The first argument is the stream shape, the second is the element type.
iterType :: HMType -> HMType -> HMType
iterType shp ty =
  let shape_type = ConTy (tiBuiltin the_con_shape) @@ shp
  in ConTy (tiBuiltin the_con_iter) @@ shape_type @@ ty

listIterType = iterType (ConTy (tiBuiltin the_con_list))
matrixIterType = iterType (ConTy (tiBuiltin the_con_matrix))

-------------------------------------------------------------------------------
-- Class initialization

-- | Create a class method variable's signature from the class method's
-- signature.
mkMethodType :: Class -> TyScheme -> TyScheme
mkMethodType cls (TyScheme qvars cst fot) =
  let qvars' = clsParam cls : qvars
      cst' = (ConTy (clsParam cls) `IsInst` cls) : cst
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

monomorphicInstance cls ty mcon methods =
  Instance { insQVars = []
           , insConstraint = []
           , insClass = cls
           , insType = ty
           , insCon = mcon
           , insMethods = methods
           }

mkEqClass = do
  rec { a <- newTyVar Star Nothing
        ; let compareScheme = monomorphic $ functionType [ConTy a, ConTy a] (ConTy $ tiBuiltin the_con_bool)

        ; let cls = Class { clsParam = a
                          , clsConstraint = []
                          , clsMethods = [eq, ne]
                          , clsName = "Eq"
                          , clsInstances = [int_instance, float_instance,
                                           tuple2_instance]
                          , clsTypeCon = pyonBuiltin SystemF.the_EqDict
                          , clsDictCon = pyonBuiltin SystemF.the_eqDict
                          }
  
        ; eq <- mkClassMethod cls 0 "__eq__" compareScheme
        ; ne <- mkClassMethod cls 1 "__ne__" compareScheme

        ; let int_instance =
               monomorphicInstance cls
               (ConTy $ tiBuiltin the_con_int)
               Nothing
               [ InstanceMethod $
                 pyonBuiltin SystemF.the_EqDict_int_eq
               , InstanceMethod $
                 pyonBuiltin SystemF.the_EqDict_int_ne]
              float_instance =
               monomorphicInstance cls
               (ConTy $ tiBuiltin the_con_float)
               Nothing
               [ InstanceMethod $
                 pyonBuiltin SystemF.the_EqDict_float_eq
               , InstanceMethod $
                 pyonBuiltin SystemF.the_EqDict_float_ne]
        ; tuple2_instance <- do
          a <- newTyVar Star Nothing
          b <- newTyVar Star Nothing
          return $ Instance { insQVars = [a, b]
                            , insConstraint = [ ConTy a `IsInst` cls
                                              , ConTy b `IsInst` cls
                                              ]
                            , insClass = cls
                            , insType = TupleTy 2 @@ ConTy a @@ ConTy b
                            , insCon = Nothing
                            , insMethods = [ InstanceMethod $
                                             pyonBuiltin SystemF.the_EqDict_Tuple2_eq 
                                           , InstanceMethod $
                                             pyonBuiltin SystemF.the_EqDict_Tuple2_ne]
                            } }
  return cls

mkOrdClass = do
  rec { a <- newTyVar Star Nothing
        ; let compareScheme = monomorphic $ functionType [ConTy a, ConTy a] (ConTy $ tiBuiltin the_con_bool)

        ; let cls = Class { clsParam = a
                          , clsConstraint = [ConTy a `IsInst` tiBuiltin the_Eq]
                          , clsMethods = [lt, le, gt, ge]
                          , clsName = "Ord"
                          , clsInstances = [int_instance, float_instance,
                                            tuple2_instance]
                          , clsTypeCon = pyonBuiltin SystemF.the_OrdDict
                          , clsDictCon = pyonBuiltin SystemF.the_ordDict
                          }

        ; lt <- mkClassMethod cls 0 "__lt__" compareScheme
        ; le <- mkClassMethod cls 1 "__le__" compareScheme
        ; gt <- mkClassMethod cls 2 "__gt__" compareScheme
        ; ge <- mkClassMethod cls 3 "__ge__" compareScheme

        ; let int_instance =
                monomorphicInstance cls
                (ConTy $ tiBuiltin the_con_int)
                Nothing
                [ InstanceMethod $
                  pyonBuiltin SystemF.the_OrdDict_int_lt
                , InstanceMethod $
                  pyonBuiltin SystemF.the_OrdDict_int_le
                , InstanceMethod $
                  pyonBuiltin SystemF.the_OrdDict_int_gt
                , InstanceMethod $
                  pyonBuiltin SystemF.the_OrdDict_int_ge]
              float_instance =
                monomorphicInstance cls
                (ConTy $ tiBuiltin the_con_float)
                Nothing
                [ InstanceMethod $
                  pyonBuiltin SystemF.the_OrdDict_float_lt
                , InstanceMethod $
                  pyonBuiltin SystemF.the_OrdDict_float_le
                , InstanceMethod $
                  pyonBuiltin SystemF.the_OrdDict_float_gt
                , InstanceMethod $
                  pyonBuiltin SystemF.the_OrdDict_float_ge]

        ; tuple2_instance <- do
            a <- newTyVar Star Nothing
            b <- newTyVar Star Nothing
            return $ Instance { insQVars = [a, b]
                              , insConstraint = [ ConTy a `IsInst` cls
                                                , ConTy b `IsInst` cls
                                                ]
                              , insClass = cls
                              , insType = TupleTy 2 @@ ConTy a @@ ConTy b
                              , insCon = Nothing
                              , insMethods = [ InstanceMethod $
                                               pyonBuiltin SystemF.the_OrdDict_Tuple2_lt
                                             , InstanceMethod $
                                               pyonBuiltin SystemF.the_OrdDict_Tuple2_le
                                             , InstanceMethod $
                                               pyonBuiltin SystemF.the_OrdDict_Tuple2_gt
                                             , InstanceMethod $
                                               pyonBuiltin SystemF.the_OrdDict_Tuple2_ge] 
                              } }
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

  rec { let cls = Class { clsParam = t
                        , clsConstraint = []
                        , clsMethods = [iter, build]
                        , clsName = "Traversable"
                        , clsInstances = [list_instance, matrix_instance,
                                          listView_instance, matrixView_instance,
                                          iter_instance]
                        , clsTypeCon = pyonBuiltin SystemF.the_TraversableDict
                        , clsDictCon = pyonBuiltin SystemF.the_traversableDict
                        }

      ; iter <- mkClassMethod cls 0 "__iter__" iter_scheme
      ; build <- mkClassMethod cls 1 "__build__" build_scheme
  
      ; t2 <- newTyVar (Star :-> Star) Nothing

      ; let list_instance =
                monomorphicInstance cls
                (ConTy $ tiBuiltin the_con_list)
                Nothing
                [ InstanceMethod $
                  pyonBuiltin SystemF.the_TraversableDict_list_traverse
                , InstanceMethod $
                  pyonBuiltin SystemF.the_TraversableDict_list_build]

            matrix_instance =
                monomorphicInstance cls
                (ConTy $ tiBuiltin the_con_matrix)
                Nothing
                [ InstanceMethod $
                  pyonBuiltin SystemF.the_TraversableDict_matrix_traverse
                , InstanceMethod $
                  pyonBuiltin SystemF.the_TraversableDict_matrix_build]

            listView_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_ListView)
              Nothing
              [ InstanceMethod $
                pyonBuiltin SystemF.the_TraversableDict_ListView_traverse
              , InstanceMethod $
                pyonBuiltin SystemF.the_TraversableDict_ListView_build]

            matrixView_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_MatrixView)
              Nothing
              [ InstanceMethod $
                pyonBuiltin SystemF.the_TraversableDict_MatrixView_traverse
              , InstanceMethod $
                pyonBuiltin SystemF.the_TraversableDict_MatrixView_build]

            iter_instance =
              -- A stream of anything is iterable
              Instance
              { insQVars = [t2]
              , insConstraint = []
              , insClass = cls
              , insType = ConTy (tiBuiltin the_con_iter) @@
                          (ConTy (tiBuiltin the_con_shape) @@ ConTy t2)
              , insCon = Nothing
              , insMethods =
                [ InstanceMethod $
                  pyonBuiltin SystemF.the_TraversableDict_Stream_traverse
                , InstanceMethod $
                  pyonBuiltin SystemF.the_TraversableDict_Stream_build] } }

  return cls

mkShapeClass = do
  sh <- newTyVar Star Nothing
  flattenStreamScheme <- forallType [Star] $ \[a] ->
    let aT = ConTy a
        shT = ConTy sh
    in ([], functionType [ConTy (tiBuiltin the_con_iter) @@ shT @@ aT]
            (iterType (ConTy $ tiBuiltin the_con_list) aT))

  map_scheme <- zipWithN_scheme (ConTy sh) 1
  zip_scheme <- zipWithN_scheme (ConTy sh) 2
  zip3_scheme <- zipWithN_scheme (ConTy sh) 3
  zip4_scheme <- zipWithN_scheme (ConTy sh) 4

  rec let cls = Class { clsParam = sh
                      , clsConstraint = []
                      , clsMethods = [flattenStream, mapStream,
                                      zipWithStream, zipWith3Stream, zipWith4Stream]
                      , clsName = "Shape"
                      , clsInstances = [list_instance, matrix_instance,
                                        listView_instance, matrixView_instance,
                                        stream_instance]
                      , clsTypeCon = pyonBuiltin SystemF.the_ShapeDict
                      , clsDictCon = pyonBuiltin SystemF.the_shapeDict
                      }
      flattenStream <- mkClassMethod cls 0 "flattenStream" flattenStreamScheme
      mapStream <- mkClassMethod cls 1 "mapStream" map_scheme
      zipWithStream <- mkClassMethod cls 2 "zipWithStream" zip_scheme
      zipWith3Stream <- mkClassMethod cls 3 "zipWith3Stream" zip3_scheme
      zipWith4Stream <- mkClassMethod cls 4 "zipWith4Stream" zip4_scheme

      let list_instance =
            monomorphicInstance cls
            (ConTy (tiBuiltin the_con_shape) @@ ConTy (tiBuiltin the_con_list))
            Nothing
            [ InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_list_flatten,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_list_map,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_list_zipWith,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_list_zipWith3,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_list_zipWith4]
          matrix_instance =
            monomorphicInstance cls
            (ConTy (tiBuiltin the_con_shape) @@ ConTy (tiBuiltin the_con_matrix))
            Nothing
            [ InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_matrix_flatten,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_matrix_map,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_matrix_zipWith,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_matrix_zipWith3,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_matrix_zipWith4]
          -- These methods are exactly the same as for list.
          -- It's actually the same instance: shape list == shape ListView.
          listView_instance =
            monomorphicInstance cls
            (ConTy (tiBuiltin the_con_shape) @@ ConTy (tiBuiltin the_con_ListView))
            Nothing
            [ InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_list_flatten,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_list_map,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_list_zipWith,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_list_zipWith3,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_list_zipWith4]
          -- These methods are exactly the same as for matrix.
          -- It's actually the same instance: shape matrix == shape MatrixView.
          matrixView_instance =
            monomorphicInstance cls
            (ConTy (tiBuiltin the_con_shape) @@ ConTy (tiBuiltin the_con_MatrixView))
            Nothing
            [ InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_matrix_flatten,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_matrix_map,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_matrix_zipWith,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_matrix_zipWith3,
              InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_matrix_zipWith4]
      t <- newTyVar (Star :-> Star) Nothing
      let stream_instance =
            Instance { insQVars = [sh]
                     , insConstraint = [ConTy sh `IsInst` cls]
                     , insClass = cls
                     , insType = ConTy (tiBuiltin the_con_shape) @@ (ConTy (tiBuiltin the_con_iter) @@ ConTy sh)
                     , insCon = Nothing
                     , insMethods =
                       [ InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_Stream_flatten,
                         InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_Stream_map,
                         InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_Stream_zipWith,
                         InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_Stream_zipWith3,
                         InstanceMethod $ pyonBuiltin SystemF.the_ShapeDict_Stream_zipWith4
                       ] }
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
  at_scheme <- forallType [Star] $ \[a] ->
    ([passable (ConTy a)],
     functionType [ConTy t @@ ConTy a, int_type] (ConTy a))
  slice_scheme <- forallType [Star] $ \[a] ->
    ([passable (ConTy a)],
     functionType [ConTy t @@ ConTy a, int_type, int_type, int_type]
     (ConTy (tiBuiltin the_con_ListView) @@ ConTy a))
  with_shape_scheme <- forallType [Star, Star] $ \[a, b] ->
    ([], functionType [ConTy t @@ ConTy a,
                       ConTy (tiBuiltin the_con_ListShapeEliminator) @@ ConTy b] (ConTy b))
  rec { let cls = Class { clsParam = t
                        , clsConstraint = []
                        , clsMethods = [at, slice, with_shape]
                        , clsName = "Indexable"
                        , clsInstances = [list_instance, listview_instance]
                        , clsTypeCon = pyonBuiltin SystemF.the_IndexableDict
                        , clsDictCon = pyonBuiltin SystemF.the_indexableDict
                        }
      ; at <- mkClassMethod cls 0 "at_point" at_scheme
      ; slice <- mkClassMethod cls 1 "at_slice" slice_scheme
      ; with_shape <- mkClassMethod cls 2 "with_shape" with_shape_scheme
      ; let list_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_list)
              Nothing
              [ InstanceMethod $ pyonBuiltin SystemF.the_IndexableDict_list_at_point
              , InstanceMethod $ pyonBuiltin SystemF.the_IndexableDict_list_at_slice
              , InstanceMethod $ pyonBuiltin SystemF.the_IndexableDict_list_with_shape]
      ; let listview_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_ListView)
              Nothing
              [ InstanceMethod $ pyonBuiltin SystemF.the_IndexableDict_ListView_at_point
              , InstanceMethod $ pyonBuiltin SystemF.the_IndexableDict_ListView_at_slice
              , InstanceMethod $ pyonBuiltin SystemF.the_IndexableDict_ListView_with_shape]
      }
  return cls

mkIndexable2Class = do
  t <- newTyVar (Star :-> Star) Nothing
  let int_type = ConTy $ tiBuiltin the_con_int
  at_scheme <- forallType [Star] $ \[a] ->
    ([passable (ConTy a)],
     functionType [ConTy t @@ ConTy a, int_type, int_type] (ConTy a))
  -- slice takes 6 int parameters
  slice_scheme <- forallType [Star] $ \[a] ->
    ([passable (ConTy a)],
     functionType [ConTy t @@ ConTy a, int_type, int_type, int_type, int_type, int_type, int_type]
     (ConTy (tiBuiltin the_con_ListView) @@ ConTy a))
  with_shape_scheme <- forallType [Star, Star] $ \[a, b] ->
    ([], functionType [ConTy t @@ ConTy a,
                       ConTy (tiBuiltin the_con_MatrixShapeEliminator) @@ ConTy b] (ConTy b))
  rec { let cls = Class { clsParam = t
                        , clsConstraint = []
                        , clsMethods = [at, slice, with_shape]
                        , clsName = "Indexable2"
                        , clsInstances = [matrix_instance, matrixview_instance]
                        , clsTypeCon = pyonBuiltin SystemF.the_Indexable2Dict
                        , clsDictCon = pyonBuiltin SystemF.the_indexable2Dict
                        }
      ; at <- mkClassMethod cls 0 "at_point2" at_scheme
      ; slice <- mkClassMethod cls 1 "at_slice2" slice_scheme
      ; with_shape <- mkClassMethod cls 2 "with_shape2" with_shape_scheme
      ; let matrix_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_matrix)
              Nothing
              [ InstanceMethod $ pyonBuiltin SystemF.the_Indexable2Dict_matrix_at_point2
              , InstanceMethod $ pyonBuiltin SystemF.the_Indexable2Dict_matrix_at_slice2
              , InstanceMethod $ pyonBuiltin SystemF.the_Indexable2Dict_matrix_with_shape2]
      ; let matrixview_instance =
              monomorphicInstance cls
              (ConTy $ tiBuiltin the_con_MatrixView)
              Nothing
              [ InstanceMethod $ pyonBuiltin SystemF.the_Indexable2Dict_MatrixView_at_point2
              , InstanceMethod $ pyonBuiltin SystemF.the_Indexable2Dict_MatrixView_at_slice2
              , InstanceMethod $ pyonBuiltin SystemF.the_Indexable2Dict_MatrixView_with_shape2]
      }
  return cls

mkAdditiveClass = do 
  rec {
  a <- newTyVar Star Nothing
  ; let binScheme = monomorphic $ functionType [ConTy a, ConTy a] (ConTy a)
        negScheme = monomorphic $ functionType [ConTy a] (ConTy a)

  ; let cls = Class { clsParam = a
                    , clsConstraint = []
                    , clsMethods = [add, sub, negate, zero]
                    , clsName = "Additive"
                    , clsInstances = [int_instance, float_instance,
                                      complex_instance]
                    , clsTypeCon = pyonBuiltin SystemF.the_AdditiveDict
                    , clsDictCon = pyonBuiltin SystemF.the_additiveDict
                    }

  ; add <- mkClassMethod cls 0 "__add__" binScheme
  ; sub <- mkClassMethod cls 1 "__sub__" binScheme
  ; negate <- mkClassMethod cls 2 "__negate__" negScheme
  ; zero <- mkClassMethod cls 3 "zero" $ monomorphic $ ConTy a

  ; let int_instance =
          monomorphicInstance cls
          (ConTy $ tiBuiltin the_con_int)
          Nothing
          [ InstanceMethod $ pyonBuiltin SystemF.the_AdditiveDict_int_add
          , InstanceMethod $ pyonBuiltin SystemF.the_AdditiveDict_int_sub
          , InstanceMethod $ pyonBuiltin SystemF.the_AdditiveDict_int_negate
          , InstanceMethod $ pyonBuiltin SystemF.the_AdditiveDict_int_zero]
        float_instance =
          monomorphicInstance cls
          (ConTy $ tiBuiltin the_con_float)
          Nothing
          [ InstanceMethod $ pyonBuiltin SystemF.the_AdditiveDict_float_add
          , InstanceMethod $ pyonBuiltin SystemF.the_AdditiveDict_float_sub
          , InstanceMethod $ pyonBuiltin SystemF.the_AdditiveDict_float_negate
          , InstanceMethod $ pyonBuiltin SystemF.the_AdditiveDict_float_zero]
  
  ; b <- newTyVar Star Nothing
  ; let complex_instance =
          Instance { insQVars = [b]
                   , insConstraint = [passable (ConTy b),
                                      ConTy b `IsInst` cls]
                   , insClass = cls
                   , insType = ConTy (tiBuiltin the_con_Complex) @@ ConTy b
                   , insCon = Nothing
                   , insMethods =
                     [ InstanceMethod (pyonBuiltin SystemF.the_AdditiveDict_Complex_add)
                     , InstanceMethod (pyonBuiltin SystemF.the_AdditiveDict_Complex_sub)
                     , InstanceMethod (pyonBuiltin SystemF.the_AdditiveDict_Complex_negate)
                     , InstanceMethod (pyonBuiltin SystemF.the_AdditiveDict_Complex_zero)]
                   } }
  return cls

mkMultiplicativeClass = do
  rec {
  a <- newTyVar Star Nothing
  ; let binScheme = monomorphic $ functionType [ConTy a, ConTy a] (ConTy a)
        fromIntScheme = monomorphic $
                        functionType [ConTy (tiBuiltin the_con_int)] (ConTy a)
  ; let cls = Class { clsParam = a
                    , clsConstraint = [ConTy a `IsInst` tiBuiltin the_Additive]
                    , clsMethods = [times, fromInt, one]
                    , clsName = "Multiplicative"
                    , clsInstances = [int_instance, float_instance,
                                      complex_instance]
                    , clsTypeCon = pyonBuiltin SystemF.the_MultiplicativeDict
                    , clsDictCon = pyonBuiltin SystemF.the_multiplicativeDict
                    }

  ; times <- mkClassMethod cls 0 "__mul__" binScheme
  ; fromInt <- mkClassMethod cls 1 "__fromint__" fromIntScheme
  ; one <- mkClassMethod cls 2 "one" (monomorphic (ConTy a))
  
  ; let int_instance =
          monomorphicInstance cls
          (ConTy $ tiBuiltin the_con_int)
          Nothing
          [ InstanceMethod $
            pyonBuiltin $ SystemF.the_MultiplicativeDict_int_mul
          , InstanceMethod $
            pyonBuiltin $ SystemF.the_MultiplicativeDict_int_fromInt
          , InstanceMethod $
            pyonBuiltin $ SystemF.the_MultiplicativeDict_int_one]
        float_instance =
          monomorphicInstance cls
          (ConTy $ tiBuiltin the_con_float)
          Nothing
          [ InstanceMethod $
            pyonBuiltin $ SystemF.the_MultiplicativeDict_float_mul
          , InstanceMethod $
            pyonBuiltin $ SystemF.the_MultiplicativeDict_float_fromInt
          , InstanceMethod $
            pyonBuiltin $ SystemF.the_MultiplicativeDict_float_one]
  ; b <- newTyVar Star Nothing
  ; let complex_instance =
          Instance { insQVars = [b]
                   , insConstraint = [passable (ConTy b),
                                      ConTy b `IsInst` cls]
                   , insClass = cls
                   , insType = ConTy (tiBuiltin the_con_Complex) @@ ConTy b
                   , insCon = Nothing
                   , insMethods =
                     [ InstanceMethod (pyonBuiltin SystemF.the_MultiplicativeDict_Complex_mul)
                     , InstanceMethod (pyonBuiltin SystemF.the_MultiplicativeDict_Complex_fromInt)
                     , InstanceMethod (pyonBuiltin SystemF.the_MultiplicativeDict_Complex_one)]
                   } }
  
  return cls
  
mkFloatingClass = do
  rec a <- newTyVar Star Nothing
      let binScheme = monomorphic $ functionType [ConTy a, ConTy a] (ConTy a)
          unScheme  = monomorphic $ functionType [ConTy a] (ConTy a)
          fromFloatScheme = monomorphic $
                            functionType [ConTy $ tiBuiltin the_con_float] (ConTy a)
      let cls = Class { clsParam = a
                      , clsConstraint = []
                      , clsMethods = [fromfloat, power, expfn, logfn, sqrtfn,
                                      sinfn, cosfn, tanfn, pi]
                      , clsName = "Floating"
                      , clsInstances = [float_instance, complex_instance]
                      , clsTypeCon = pyonBuiltin SystemF.the_FloatingDict
                      , clsDictCon = pyonBuiltin SystemF.the_floatingDict
                      }

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
            Nothing
            [ InstanceMethod $
              pyonBuiltin $ SystemF.the_FloatingDict_float_fromfloat
            , InstanceMethod $
              pyonBuiltin $ SystemF.the_FloatingDict_float_power
            , InstanceMethod $
              pyonBuiltin $ SystemF.the_FloatingDict_float_exp
            , InstanceMethod $
              pyonBuiltin $ SystemF.the_FloatingDict_float_log
            , InstanceMethod $
              pyonBuiltin $ SystemF.the_FloatingDict_float_sqrt
            , InstanceMethod $
              pyonBuiltin $ SystemF.the_FloatingDict_float_sin
            , InstanceMethod $
              pyonBuiltin $ SystemF.the_FloatingDict_float_cos
            , InstanceMethod $
              pyonBuiltin $ SystemF.the_FloatingDict_float_tan
            , InstanceMethod $
              pyonBuiltin $ SystemF.the_FloatingDict_float_pi]

      b <- newTyVar Star Nothing
      let complex_instance =
             Instance { insQVars = [b]
                      , insConstraint = [passable (ConTy b),
                                         ConTy b `IsInst` tiBuiltin the_Multiplicative,
                                         ConTy b `IsInst` tiBuiltin the_Fractional,
                                         ConTy b `IsInst` cls]
                      , insClass = cls
                      , insType = ConTy (tiBuiltin the_con_Complex) @@ ConTy b
                      , insCon = Nothing
                      , insMethods =
                        [ InstanceMethod $
                          pyonBuiltin SystemF.the_FloatingDict_Complex_fromfloat
                        , InstanceMethod $
                          pyonBuiltin SystemF.the_FloatingDict_Complex_power
                        , InstanceMethod $
                          pyonBuiltin SystemF.the_FloatingDict_Complex_exp
                        , InstanceMethod $
                          pyonBuiltin SystemF.the_FloatingDict_Complex_log
                        , InstanceMethod $
                          pyonBuiltin SystemF.the_FloatingDict_Complex_sqrt
                        , InstanceMethod $
                          pyonBuiltin SystemF.the_FloatingDict_Complex_sin
                        , InstanceMethod $
                          pyonBuiltin SystemF.the_FloatingDict_Complex_cos
                        , InstanceMethod $
                          pyonBuiltin SystemF.the_FloatingDict_Complex_tan
                        , InstanceMethod $
                          pyonBuiltin SystemF.the_FloatingDict_Complex_pi]}
  
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
            Class { clsParam = a
                  , clsConstraint = [ConTy a `IsInst` tiBuiltin the_Additive]
                  , clsMethods = [scale, magnitude, dot]
                  , clsName = "Vector"
                  , clsInstances = [float_instance, complex_instance]
                  , clsTypeCon = pyonBuiltin SystemF.the_VectorDict
                  , clsDictCon = pyonBuiltin SystemF.the_vectorDict
                  }

      scale <- mkClassMethod cls 0 "scale" scaleScheme
      magnitude <- mkClassMethod cls 1 "magnitude" normScheme
      dot <- mkClassMethod cls 2 "dot" dotScheme

      let float_instance =
            monomorphicInstance cls
            (ConTy $ tiBuiltin the_con_float)
            Nothing
            [ InstanceMethod $
              pyonBuiltin SystemF.the_VectorDict_float_scale
            , InstanceMethod $
              pyonBuiltin SystemF.the_VectorDict_float_magnitude
            , InstanceMethod $
              pyonBuiltin SystemF.the_VectorDict_float_dot]

      b <- newTyVar Star Nothing
      let complex_instance =
            Instance { insQVars = [b]
                     , insConstraint = [passable (ConTy b),
                                        ConTy b `IsInst` cls]
                     , insClass = cls
                     , insType = ConTy (tiBuiltin the_con_Complex) @@ ConTy b
                     , insCon = Nothing
                     , insMethods =
                         [ InstanceMethod $
                           pyonBuiltin SystemF.the_VectorDict_Complex_scale
                         , InstanceMethod $
                           pyonBuiltin SystemF.the_VectorDict_Complex_magnitude
                         , InstanceMethod $
                           pyonBuiltin SystemF.the_VectorDict_Complex_dot]}

  return cls

mkRemainderClass = do
  a <- newTyVar Star Nothing
  let divScheme = monomorphic $
                  functionType [ConTy a, ConTy a] (ConTy (tiBuiltin the_con_int))
      remScheme = monomorphic $
                  functionType [ConTy a, ConTy a] (ConTy a)
  rec let cls =
            Class { clsParam = a
                  , clsConstraint = [ConTy a `IsInst` tiBuiltin the_Multiplicative]
                  , clsMethods = [divide, remainder]
                  , clsName = "Remainder"
                  , clsInstances = [int_instance, float_instance]
                  , clsTypeCon = pyonBuiltin SystemF.the_RemainderDict
                  , clsDictCon = pyonBuiltin SystemF.the_remainderDict
                  }
      divide <- mkClassMethod cls 0 "__floordiv__" divScheme
      remainder <- mkClassMethod cls 1 "__mod__" remScheme
      let int_instance =
            monomorphicInstance cls
            (ConTy $ tiBuiltin the_con_int)
            Nothing
            [ InstanceMethod $
              pyonBuiltin $ SystemF.the_RemainderDict_int_floordiv
            , InstanceMethod $
              pyonBuiltin $ SystemF.the_RemainderDict_int_mod]
          float_instance =
            monomorphicInstance cls
            (ConTy $ tiBuiltin the_con_float)
            Nothing
            [ InstanceMethod $
              pyonBuiltin $ SystemF.the_RemainderDict_float_floordiv
            , InstanceMethod $
              pyonBuiltin $ SystemF.the_RemainderDict_float_mod]

  return cls

mkFractionalClass = do
  a <- newTyVar Star Nothing
  let divScheme = monomorphic $
                  functionType [ConTy a, ConTy a] (ConTy a)
  rec let cls =
            Class { clsParam = a
                  , clsConstraint = [ConTy a `IsInst` tiBuiltin the_Multiplicative]
                  , clsMethods = [divide]
                  , clsName = "Fractional"
                  , clsInstances = [float_instance, complex_instance]
                  , clsTypeCon = pyonBuiltin SystemF.the_FractionalDict
                  , clsDictCon = pyonBuiltin SystemF.the_fractionalDict
                  }
      divide <- mkClassMethod cls 0 "__div__" divScheme
      let float_instance =
            monomorphicInstance cls
            (ConTy $ tiBuiltin the_con_float)
            Nothing
            [ InstanceMethod $
              pyonBuiltin $ SystemF.the_FractionalDict_float_div]

      b <- newTyVar Star Nothing
      let complex_instance =
            Instance { insQVars = [b]
                     , insConstraint = [passable (ConTy b),
                                        ConTy b `IsInst` cls]
                     , insClass = cls
                     , insType = ConTy (tiBuiltin the_con_Complex) @@ ConTy b
                     , insCon = Nothing
                     , insMethods =
                         [ InstanceMethod $
                           pyonBuiltin SystemF.the_FractionalDict_Complex_div]}

  return cls

mkPassableClass = do
  rec {
  a <- newTyVar Star Nothing
  ; let cls = Class { clsParam = a
                    , clsConstraint = []
                    , clsMethods = []
                    , clsName = "Repr"
                    , clsInstances = [int_instance, float_instance,
                                      bool_instance, none_instance,
                                      complex_instance,
                                      any_instance,
                                      list_instance, matrix_instance,
                                      listView_instance, matrixView_instance,
                                      iter_instance,
                                      tuple2_instance, tuple3_instance,
                                      tuple4_instance]
                    , clsTypeCon = pyonBuiltin SystemF.the_Repr
                    , clsDictCon =
                      internalError "Class 'Repr' has no dictionary constructor"
                    }
  
  ; let int_instance =
          monomorphicInstance cls (ConTy $ tiBuiltin the_con_int)
          (Just $ pyonBuiltin SystemF.the_repr_int) []
  ; let float_instance =
          monomorphicInstance cls (ConTy $ tiBuiltin the_con_float)
          (Just $ pyonBuiltin SystemF.the_repr_float) []
  ; let bool_instance =
          monomorphicInstance cls (ConTy $ tiBuiltin the_con_bool)
          (Just $ pyonBuiltin SystemF.the_repr_bool) []
  ; let none_instance =
          monomorphicInstance cls (ConTy $ tiBuiltin the_con_NoneType)
          (Just $ pyonBuiltin SystemF.the_repr_NoneType) []
  ; let any_instance =
          monomorphicInstance cls (ConTy $ tiBuiltin the_con_Any)
          (Just $ pyonBuiltin SystemF.the_repr_Any) []
        
  ; b <- newTyVar Star Nothing
  ; t <- newTyVar (Star :-> Star) Nothing
  ; let list_instance =
          Instance
          { insQVars = [b]
          , insConstraint = [passable $ ConTy b]
          , insClass = cls
          , insType = ConTy (tiBuiltin the_con_list) @@ ConTy b
          , insCon = Just $ pyonBuiltin SystemF.the_repr_list
          , insMethods = []
          }
  ; let matrix_instance =
          Instance
          { insQVars = [b]
          , insConstraint = [passable $ ConTy b]
          , insClass = cls
          , insType = ConTy (tiBuiltin the_con_matrix) @@ ConTy b
          , insCon = Just $ pyonBuiltin SystemF.the_repr_matrix
          , insMethods = []
          }
  ; let listView_instance =
          Instance
          { insQVars = [b]
          , insConstraint = []
          , insClass = cls
          , insType = ConTy (tiBuiltin the_con_ListView) @@ ConTy b
          , insCon = Just $ pyonBuiltin SystemF.the_repr_ListView
          , insMethods = []
          }
  ; let matrixView_instance =
          Instance
          { insQVars = [b]
          , insConstraint = []
          , insClass = cls
          , insType = ConTy (tiBuiltin the_con_MatrixView) @@ ConTy b
          , insCon = Just $ pyonBuiltin SystemF.the_repr_MatrixView
          , insMethods = []
          }
  ; let iter_instance =
          Instance
          { insQVars = [t, b]
          , insConstraint = []
          , insClass = cls
          , insType = iterType (ConTy t) (ConTy b)
          , insCon = Just $ pyonBuiltin SystemF.the_repr_Stream
          , insMethods = []
          }
  ; let complex_instance =
          Instance
          { insQVars = [b]
          , insConstraint = [passable $ ConTy b]
          , insClass = cls
          , insType = ConTy (tiBuiltin the_con_Complex) @@ ConTy b
          , insCon = Just $ pyonBuiltin SystemF.the_repr_Complex
          , insMethods = []
          }
  ; c <- newTyVar Star Nothing
  ; let tuple2_instance =
          Instance
          { insQVars = [b, c]
          , insConstraint = [passable $ ConTy b, passable $ ConTy c]
          , insClass = cls
          , insType = TupleTy 2 @@ ConTy b @@ ConTy c
          , insCon = Just $ SystemF.pyonTupleReprCon 2
          , insMethods = []
          }
  ; d <- newTyVar Star Nothing
  ; let tuple3_instance =
          Instance
          { insQVars = [b, c, d]
          , insConstraint = [passable $ ConTy b, passable $ ConTy c,
                             passable $ ConTy d]
          , insClass = cls
          , insType = TupleTy 3 @@ ConTy b @@ ConTy c @@ ConTy d
          , insCon = Just $ SystemF.pyonTupleReprCon 3
          , insMethods = []
          }
  ; e <- newTyVar Star Nothing
  ; let tuple4_instance =
          Instance
          { insQVars = [b, c, d, e]
          , insConstraint = [passable $ ConTy b, passable $ ConTy c,
                             passable $ ConTy d, passable $ ConTy e]
          , insClass = cls
          , insType = TupleTy 4 @@ ConTy b @@ ConTy c @@ ConTy d @@ ConTy e
          , insCon = Just $ SystemF.pyonTupleReprCon 4
          , insMethods = []
          }
  }
  
  return cls

-------------------------------------------------------------------------------
-- Global function initialization

passable t = t `IsInst` tiBuiltin the_Repr

mkMapType = forallType [Star :-> Star, Star, Star] $ \ [t, a, b] ->
  let tT = ConTy t
      aT = ConTy a
      bT = ConTy b
  in ([ tT `IsInst` tiBuiltin the_Traversable
      , ConTy (tiBuiltin the_con_shape) @@ tT `IsInst` tiBuiltin the_Shape
      , passable aT
      , passable bT
      ],
      functionType [functionType [aT] bT, tT @@ aT] (tT @@ bT))

mkReduceType = forallType [Star :-> Star, Star] $ \ [t, a] ->
  let tT = ConTy t
      aT = ConTy a
  in ([tT `IsInst` tiBuiltin the_Traversable
      , ConTy (tiBuiltin the_con_shape) @@ tT `IsInst` tiBuiltin the_Shape
      , passable aT],
      functionType [functionType [aT, aT] aT, aT, tT @@ aT] aT)

mkReduce1Type = forallType [Star :-> Star, Star] $ \ [t, a] ->
  let tT = ConTy t
      aT = ConTy a
  in ([tT `IsInst` tiBuiltin the_Traversable
      , ConTy (tiBuiltin the_con_shape) @@ tT `IsInst` tiBuiltin the_Shape
      , passable aT],
      functionType [functionType [aT, aT] aT, tT @@ aT] aT)

mkZipType =
  forallType [ Star :-> Star
             , Star
             , Star] $ \ [t, a, b] ->
  let tT = ConTy t
      aT = ConTy a
      bT = ConTy b
  in ([ tT `IsInst` tiBuiltin the_Traversable
      , ConTy (tiBuiltin the_con_shape) @@ tT `IsInst` tiBuiltin the_Shape
      , passable aT
      , passable bT]
     , functionType [tT @@ aT, tT @@ bT]
       (tT @@ (TupleTy 2 @@ aT @@ bT)))

mkZip3Type =
  forallType [ Star :-> Star
             , Star
             , Star
             , Star] $ \ [t, a, b, c] ->
  let tT = ConTy t
      aT = ConTy a
      bT = ConTy b
      cT = ConTy c
  in ([ tT `IsInst` tiBuiltin the_Traversable
      , ConTy (tiBuiltin the_con_shape) @@ tT `IsInst` tiBuiltin the_Shape
      , passable aT
      , passable bT
      , passable cT]
     , functionType [tT @@ aT, tT @@ bT, tT @@ cT]
       (tT @@ (TupleTy 3 @@ aT @@ bT @@ cT)))

mkZip4Type =
  forallType [ Star :-> Star
             , Star
             , Star
             , Star
             , Star] $ \ [t, a, b, c, d] ->
  let tT = ConTy t
      aT = ConTy a
      bT = ConTy b
      cT = ConTy c
      dT = ConTy d
  in ([ tT `IsInst` tiBuiltin the_Traversable
      , ConTy (tiBuiltin the_con_shape) @@ tT `IsInst` tiBuiltin the_Shape
      , passable aT
      , passable bT
      , passable cT
      , passable dT]
     , functionType [tT @@ aT, tT @@ bT, tT @@ cT, tT @@ dT]
       (tT @@ (TupleTy 4 @@ aT @@ bT @@ cT @@ dT)))

mkCountType =
  return $ monomorphic $
  iterType (ConTy $ tiBuiltin the_con_list) (ConTy $ tiBuiltin the_con_int)

mkRangeType =
  let int_type = ConTy $ tiBuiltin the_con_int
  in return $ monomorphic $
     functionType [int_type] (iterType (ConTy $ tiBuiltin the_con_list) int_type)

mkLenType =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      int_type = ConTy $ tiBuiltin the_con_int
  in ([tT `IsInst` tiBuiltin the_Indexable], functionType [tT @@ aT] int_type)

mkWidthHeightType =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      int_type = ConTy $ tiBuiltin the_con_int
  in ([tT `IsInst` tiBuiltin the_Indexable2], functionType [tT @@ aT] int_type)

mkOuterProductType =
  forallType [Star, Star, Star] $ \[a, b, c] ->
  let aT = ConTy a
      bT = ConTy b
      cT = ConTy c
  in ([passable aT, passable bT, passable cT],
      functionType [functionType [aT, bT] cT,
                    iterType (ConTy $ tiBuiltin the_con_list) aT,
                    iterType (ConTy $ tiBuiltin the_con_list) bT]
      (iterType (ConTy $ tiBuiltin the_con_matrix) cT))

mkStencil2DType =
  forallType [Star :-> Star, Star, Star] $ \[t, a, b] ->
  let tT = ConTy t
      aT = ConTy a
      bT = ConTy b
      int_type = ConTy $ tiBuiltin the_con_int
  in ([tT `IsInst` tiBuiltin the_Indexable2, passable aT, passable bT],
      functionType [int_type, int_type, int_type, int_type,
                    functionType [ConTy (tiBuiltin the_con_MatrixView) @@ aT] bT,
                    tT @@ aT]
      (ConTy (tiBuiltin the_con_matrix) @@ bT))

mkRowsColsType =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      listview a = ConTy (tiBuiltin the_con_ListView) @@ a
  in ([tT `IsInst` tiBuiltin the_Indexable2, passable aT],
      functionType [tT @@ aT] (listview $ listview aT))

mkSafeIndexType =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      int_type = ConTy $ tiBuiltin the_con_int
  in ([tT `IsInst` tiBuiltin the_Indexable,
       passable aT], functionType [tT @@ aT, int_type] aT)

mkSafeSliceType =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      int_type = ConTy $ tiBuiltin the_con_int
  in ([tT `IsInst` tiBuiltin the_Indexable,
       passable aT], functionType [tT @@ aT, int_type, int_type, int_type]
                     (ConTy (tiBuiltin the_con_ListView) @@ aT))

mkSafeIndex2Type =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      int_type = ConTy $ tiBuiltin the_con_int
  in ([tT `IsInst` tiBuiltin the_Indexable2,
       passable aT], functionType [tT @@ aT, int_type, int_type] aT)

mkSafeSlice2Type =
  forallType [Star :-> Star, Star] $ \[t, a] ->
  let tT = ConTy t
      aT = ConTy a
      int_type = ConTy $ tiBuiltin the_con_int
  in ([tT `IsInst` tiBuiltin the_Indexable2,
       passable aT], functionType [tT @@ aT, int_type, int_type, int_type, int_type, int_type, int_type]
                     (ConTy (tiBuiltin the_con_MatrixView) @@ aT))

mkHistogramType =
  forallType [Star :-> Star] $ \[t] ->
  let int_type = ConTy $ tiBuiltin the_con_int
  in ([], functionType [int_type, iterType (ConTy t) int_type]
          (ConTy (tiBuiltin the_con_list) @@ int_type))

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

mkDoType =
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
  in ([ConTy (tiBuiltin the_con_shape) @@ tT `IsInst` tiBuiltin the_Shape,
       passable aT, passable bT],
      functionType [functionType [aT] bT, iterType tT aT] (iterType tT bT))

mkListIterType =
  forallType [Star, Star] $ \[sh, a] ->
  let shT = ConTy sh
      aT = ConTy a
  in ([shT `IsInst` tiBuiltin the_Shape],
      functionType [ConTy (tiBuiltin the_con_iter) @@ shT @@ aT]
      (iterType (ConTy $ tiBuiltin the_con_list) aT))

mkMatrixIterType =
  forallType [Star] $ \[a] ->
  let aT = ConTy a
  in ([],
      functionType [iterType (ConTy $ tiBuiltin the_con_MatrixView) aT]
      (iterType (ConTy $ tiBuiltin the_con_matrix) aT))

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

mkBinaryOpType =
  forallType [Star] $ \[a] ->
  ([passable (ConTy a)], functionType [ConTy a, ConTy a] (ConTy a))

mkBinaryIntType =
  let int = ConTy (tiBuiltin the_con_int)
  in return $ monomorphic $ functionType [int, int] int

mkGlobalVar name typ con = do
  scm <- typ
  let exp pos = TIRecExp $ SystemF.ExpSF $
                SystemF.VarE (SystemF.mkExpInfo pos) con
  let ass = polymorphicAssignment scm exp
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
            -- The tuple structure contains:
            -- 1. Source code name
            -- 2. kind
            -- 3. system F constructor
            [ ("int", Star, [| pyonBuiltin SystemF.the_int |])
            , ("float", Star, [| pyonBuiltin SystemF.the_float |])
            , ("Complex", Star :-> Star, [| pyonBuiltin SystemF.the_Complex |])
            , ("bool", Star, [| pyonBuiltin SystemF.the_bool |])
            , ("NoneType", Star, [| pyonBuiltin SystemF.the_NoneType |])
            , ("iter", Star :-> Star :-> Star,
               [| pyonBuiltin SystemF.the_Stream |])
            , ("list", Star :-> Star, [| pyonBuiltin SystemF.the_list |])
            , ("matrix", Star :-> Star, [| pyonBuiltin SystemF.the_matrix |])
            , ("ListView", Star :-> Star, [| pyonBuiltin SystemF.the_ListView |])
            , ("MatrixView", Star :-> Star, [| pyonBuiltin SystemF.the_MatrixView |])
            , ("ListShapeEliminator", Star :-> Star, [| pyonBuiltin SystemF.the_ListShapeEliminator |])
            , ("MatrixShapeEliminator", Star :-> Star, [| pyonBuiltin SystemF.the_MatrixShapeEliminator |])
            , ("Any", Star, [| pyonBuiltin SystemF.the_Any |])
            , ("shape", (Star :-> Star) :-> Star,
               [| pyonBuiltin SystemF.the_shape |])
            ]
            
          classes =
            [ ("Eq", [| mkEqClass |])
            , ("Ord", [| mkOrdClass |])
            , ("Traversable", [| mkTraversableClass |])
            , ("Shape", [| mkShapeClass |])
            , ("Indexable", [| mkIndexableClass |])
            , ("Indexable2", [| mkIndexable2Class |])
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
              , [| pyonBuiltin SystemF.the_fun_map |]
              ),
              ("reduce", [| mkReduceType |]
              , [| pyonBuiltin SystemF.the_fun_reduce |]
              ),
              ("reduce1", [| mkReduce1Type |]
              , [| pyonBuiltin SystemF.the_fun_reduce1 |]
              ),
              ("zip", [| mkZipType |]
              , [| pyonBuiltin SystemF.the_fun_zip |]
              ),
              ("zip3", [| mkZip3Type |]
              , [| pyonBuiltin SystemF.the_fun_zip3 |]
              ),
              ("zip4", [| mkZip4Type |]
              , [| pyonBuiltin SystemF.the_fun_zip4 |]
              ),
              ("count", [| mkCountType |]
              , [| pyonBuiltin SystemF.the_count |]
              ),
              ("range", [| mkRangeType |]
              , [| pyonBuiltin SystemF.the_range |]
              ),
              ("len", [| mkLenType |]
              , [| pyonBuiltin SystemF.the_len |]
              ),
              ("width", [| mkWidthHeightType |]
              , [| pyonBuiltin SystemF.the_width |]
              ),
              ("height", [| mkWidthHeightType |]
              , [| pyonBuiltin SystemF.the_height |]
              ),
              ("outerproduct", [| mkOuterProductType |]
              , [| pyonBuiltin SystemF.the_outerproduct |]
              ),              
              ("stencil2D", [| mkStencil2DType |]
              , [| pyonBuiltin SystemF.the_stencil2D |]
              ),              
              ("rows", [| mkRowsColsType |]
              , [| pyonBuiltin SystemF.the_rows |]
              ),
              ("cols", [| mkRowsColsType |]
              , [| pyonBuiltin SystemF.the_cols |]
              ),
              ("safeIndex", [| mkSafeIndexType |]
              , [| pyonBuiltin SystemF.the_safeIndex |]
              ),
              ("safeSlice", [| mkSafeSliceType |]
              , [| pyonBuiltin SystemF.the_safeSlice |]
              ),
              ("safeIndex2", [| mkSafeIndex2Type |]
              , [| pyonBuiltin SystemF.the_safeIndex2 |]
              ),
              ("safeSlice2", [| mkSafeSlice2Type |]
              , [| pyonBuiltin SystemF.the_safeSlice2 |]
              ),
              ("histogram", [| mkHistogramType |]
              , [| pyonBuiltin SystemF.the_histogram |]
              ),
              ("floor", [| mkFloorType |]
              , [| pyonBuiltin SystemF.the_floor |]
              ),
              ("listiter", [| mkListIterType |]
              , [| pyonBuiltin SystemF.the_fun_asList_Stream |]
              ),
              ("matrixiter", [| mkMatrixIterType |]
              , [| pyonBuiltin SystemF.the_fun_from_MatrixView_Stream |]
              ),
              ("__undefined__", [| mkUndefinedType |]
              , [| pyonBuiltin SystemF.the_fun_undefined |]
              ),
              ("do", [| mkDoType |]
              , [| pyonBuiltin SystemF.the_oper_DO |]
              ),
              ("guard", [| mkGuardType |]
              , [| pyonBuiltin SystemF.the_oper_GUARD |]
              ),
              ("iterBind", [| mkIterBindType |]
              , [| pyonBuiltin SystemF.the_oper_CAT_MAP |]
              ),
              ("complex", [| mkMakeComplexType |]
              , [| pyonBuiltin SystemF.the_complex |]
              ),
              ("__and__", [| mkBinaryIntType |]
              , [| pyonBuiltin SystemF.the_oper_BITWISEAND |]
              ),
              ("__or__", [| mkBinaryIntType |]
              , [| pyonBuiltin SystemF.the_oper_BITWISEOR |]
              ),
              ("__xor__", [| mkBinaryIntType |]
              , [| pyonBuiltin SystemF.the_oper_BITWISEXOR |]
              )
            ]
          cls_members =
            [ ([| the_Eq |], ["__eq__", "__ne__"])
            , ([| the_Ord |], ["__lt__", "__le__", "__gt__", "__ge__"])
            , ([| the_Traversable |], ["__iter__", "__build__"])
            , ([| the_Shape |], ["flattenStream", "mapStream", "zipWithStream", "zipWith3Stream", "zipWith4Stream"])
            , ([| the_Indexable |], ["at_point", "at_slice", "with_shape"])
            , ([| the_Indexable2 |], ["at_point2", "at_slice2", "with_shape2"])
            , ([| the_Additive |], ["__add__", "__sub__", "__negate__", "zero"])
            , ([| the_Multiplicative |], ["__mul__", "__fromint__", "one"])
            , ([| the_Remainder |], ["__floordiv__", "__mod__"])
            , ([| the_Fractional |], ["__div__"])
            , ([| the_Floating |], ["__fromfloat__", "__power__",
                                    "exp", "log", "sqrt",
                                    "sin", "cos", "tan", "pi"])
            , ([| the_Vector |], ["scale", "magnitude", "dot"])
            ]

          -- Construct initializers
          typ_initializer (name, _, con) =
            ('_':name, [| return $(con) |])
          tycon_initializer (name, kind, con) =
            ("_con_" ++ name, [| builtinTyCon name kind $(con) |])
          cls_initializer (name, mk) =
            ('_':name, mk)
          global_initializer (name, typ, con) =
            ('_':name, [| mkGlobalVar name $(typ) $(con) |])
          cls_member_initializer (cls, members) = zipWith mb members [0..]
            where
              mb member_name index =
                ('_':member_name,
                 [| -- Verify the method's name
                    let v = clmVariable $
                            getClassMethod (tiBuiltin $(cls)) index
                    in return $ if varName v /= Just (builtinLabel member_name)
                                then internalError "Inconsistent class method name"
                                else v |])

          initializers = map typ_initializer types ++
                         map tycon_initializer types ++
                         map cls_initializer classes ++
                         map global_initializer globals ++
                         concatMap cls_member_initializer cls_members
      in initializeRecordM tiBuiltinSpecification initializers)
  
  -- Save it
  putMVar the_TIBuiltins bi

