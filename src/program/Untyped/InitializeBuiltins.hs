-- | This module exports one function, which is called to initialize the
-- untyped built-in constants.  It inhabits a separate file due to module 
-- dependences.

{-# LANGUAGE TemplateHaskell, RecursiveDo #-}
module Untyped.InitializeBuiltins
       (initializeTIBuiltins)
where

import Control.Concurrent.MVar
import Control.Monad
import qualified Language.Haskell.TH as TH

import Gluon.Common.Error
import Gluon.Common.Label
import Gluon.Common.THRecord
import qualified Gluon.Core as Gluon
import qualified SystemF.Builtins as SystemF
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

pyonBuiltin = SystemF.pyonBuiltin

f @@ g = appTy f g

-- | Create an 'untyped' type constructor that corresponds to the given
-- System F type constructor
builtinTyCon name kind sf_con =
  let y = Gluon.mkInternalConE sf_con
  in mkTyCon (builtinLabel name) kind y

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

-- | Look up a method of the given class and return its type scheme
classMethodType :: (TIBuiltins -> Class) -> Int -> TyScheme
classMethodType cls_field index =
  let cls = tiBuiltin cls_field
  in mkMethodType cls (clmSignature $ clsMethods cls !! index)

monomorphicInstance cls ty mcon methods =
  Instance { insQVars = []
           , insConstraint = []
           , insClass = cls
           , insType = ty
           , insCon = mcon
           , insMethods = methods
           }

mkEqClass = mdo
  a <- newTyVar Star Nothing
  let compareScheme = monomorphic $ functionType [ConTy a, ConTy a] (ConTy $ tiBuiltin the_con_bool)

  let cls = Class { clsParam = a
                  , clsConstraint = []
                  , clsMethods = [eq, ne]
                  , clsName = "Eq"
                  , clsInstances = [int_instance, float_instance,
                                    tuple2_instance]
                  , clsTypeCon = pyonBuiltin SystemF.the_EqDict
                  , clsDictCon = pyonBuiltin SystemF.the_eqDict
                  }
  
  eq <- mkClassMethod cls 0 "__eq__" compareScheme
  ne <- mkClassMethod cls 1 "__ne__" compareScheme

  let int_instance =
        monomorphicInstance cls
        (ConTy $ tiBuiltin the_con_int)
        Nothing
        (fromEqDict SystemF.the_EqDict_int)
      float_instance =
        monomorphicInstance cls
        (ConTy $ tiBuiltin the_con_float)
        Nothing
        (fromEqDict SystemF.the_EqDict_float)
  tuple2_instance <- do
    a <- newTyVar Star Nothing
    b <- newTyVar Star Nothing
    return $ Instance { insQVars = [a, b]
                      , insConstraint = [ ConTy a `IsInst` cls
                                        , ConTy b `IsInst` cls
                                        ]
                      , insClass = cls
                      , insType = TupleTy 2 @@ ConTy a @@ ConTy b
                      , insCon = Nothing
                      , insMethods = fromEqDict SystemF.the_EqDict_Tuple2
                      }
  return cls
  where
    fromEqDict field_name =
      case pyonBuiltin field_name
      of SystemF.EqDictMembers eq ne ->
           [ InstanceMethod eq
           , InstanceMethod ne
           ]

mkOrdClass = mdo
  a <- newTyVar Star Nothing
  let compareScheme = monomorphic $ functionType [ConTy a, ConTy a] (ConTy $ tiBuiltin the_con_bool)

  let cls = Class { clsParam = a
                  , clsConstraint = [ConTy a `IsInst` tiBuiltin the_Eq]
                  , clsMethods = [lt, le, gt, ge]
                  , clsName = "Ord"
                  , clsInstances = [int_instance, float_instance,
                                    tuple2_instance]
                  , clsTypeCon = pyonBuiltin SystemF.the_OrdDict
                  , clsDictCon = pyonBuiltin SystemF.the_ordDict
                  }

  lt <- mkClassMethod cls 0 "__lt__" compareScheme
  le <- mkClassMethod cls 1 "__le__" compareScheme
  gt <- mkClassMethod cls 2 "__gt__" compareScheme
  ge <- mkClassMethod cls 3 "__ge__" compareScheme

  let int_instance =
        monomorphicInstance cls
        (ConTy $ tiBuiltin the_con_int)
        Nothing
        (fromOrdDict SystemF.the_OrdDict_int)
      float_instance =
        monomorphicInstance cls
        (ConTy $ tiBuiltin the_con_float)
        Nothing
        (fromOrdDict SystemF.the_OrdDict_float)

  tuple2_instance <- do
    a <- newTyVar Star Nothing
    b <- newTyVar Star Nothing
    return $ Instance { insQVars = [a, b]
                      , insConstraint = [ ConTy a `IsInst` cls
                                        , ConTy b `IsInst` cls
                                        ]
                      , insClass = cls
                      , insType = TupleTy 2 @@ ConTy a @@ ConTy b
                      , insCon = Nothing
                      , insMethods = fromOrdDict SystemF.the_OrdDict_Tuple2
                      }
  return cls
  where
    fromOrdDict field_name =
      case pyonBuiltin field_name
      of SystemF.OrdDictMembers lt le gt ge ->
           [ InstanceMethod lt
           , InstanceMethod le
           , InstanceMethod gt
           , InstanceMethod ge
           ]

mkTraversableClass = mdo
  t <- newTyVar (Star :-> Star) Nothing
  iter_scheme <-
    forallType [Star] $ \[a] ->
    let aT = ConTy a
        tT = ConTy t
    in ( [passable aT]
       , functionType [tT @@ aT] (ConTy (tiBuiltin the_con_iter) @@ aT))

  build_scheme <-
    forallType [Star] $ \[a] ->
    let aT = ConTy a
        tT = ConTy t
    in ( [passable aT]
       , functionType [ConTy (tiBuiltin the_con_iter) @@ aT] (tT @@ aT))

  let cls = Class { clsParam = t
                  , clsConstraint = []
                  , clsMethods = [iter, build]
                  , clsName = "Traversable"
                  , clsInstances = [list_instance, iter_instance]
                  , clsTypeCon = pyonBuiltin SystemF.the_TraversableDict
                  , clsDictCon = pyonBuiltin SystemF.the_traversableDict
                  }

  iter <- mkClassMethod cls 0 "__iter__" iter_scheme
  build <- mkClassMethod cls 1 "__build__" build_scheme
  
  let list_instance =
        monomorphicInstance cls
        (ConTy $ tiBuiltin the_con_list)
        Nothing
        (fromTraversableDict SystemF.the_TraversableDict_list)
      iter_instance =
        monomorphicInstance cls
        (ConTy $ tiBuiltin the_con_iter)
        Nothing
        (fromTraversableDict SystemF.the_TraversableDict_Stream)

  return cls
  where
    fromTraversableDict field_name =
      case pyonBuiltin field_name
      of SystemF.TraversableDictMembers iter build -> [ InstanceMethod iter
                                                      , InstanceMethod build]

mkAdditiveClass = mdo
  a <- newTyVar Star Nothing
  let binScheme = monomorphic $ functionType [ConTy a, ConTy a] (ConTy a)
      negScheme = monomorphic $ functionType [ConTy a] (ConTy a)

  let cls = Class { clsParam = a
                  , clsConstraint = [passable (ConTy a)]
                  , clsMethods = [add, sub, negate, zero]
                  , clsName = "Additive"
                  , clsInstances = [int_instance, float_instance]
                  , clsTypeCon = pyonBuiltin SystemF.the_AdditiveDict
                  , clsDictCon = pyonBuiltin SystemF.the_additiveDict
                  }

  add <- mkClassMethod cls 0 "__add__" binScheme
  sub <- mkClassMethod cls 1 "__sub__" binScheme
  negate <- mkClassMethod cls 2 "__negate__" negScheme
  zero <- mkClassMethod cls 3 "zero" $ monomorphic $ ConTy a

  let int_instance =
        monomorphicInstance cls
        (ConTy $ tiBuiltin the_con_int)
        Nothing
        (fromAdditiveDict SystemF.the_AdditiveDict_int)
      float_instance =
        monomorphicInstance cls
        (ConTy $ tiBuiltin the_con_float)
        Nothing
        (fromAdditiveDict SystemF.the_AdditiveDict_float)
  
  return cls
  where
    fromAdditiveDict field_name =
      case pyonBuiltin field_name
      of SystemF.AdditiveDictMembers add sub neg zero ->
           [ InstanceMethod add
           , InstanceMethod sub
           , InstanceMethod neg
           , InstanceMethod zero
           ]

mkVectorClass = mdo
  a <- newTyVar Star Nothing
  let normScheme = monomorphic $
                   functionType [ConTy a] (ConTy $ tiBuiltin the_con_float)
      scaleScheme = monomorphic $
                    functionType [ConTy a, ConTy $ tiBuiltin the_con_int] (ConTy a)

  let cls = Class { clsParam = a
                  , clsConstraint = [ConTy a `IsInst` tiBuiltin the_Additive]
                  , clsMethods = [scale, norm]
                  , clsName = "Vector"
                  , clsInstances = []
                  , clsTypeCon = pyonBuiltin SystemF.the_VectorDict
                  , clsDictCon = pyonBuiltin SystemF.the_vectorDict
                  }

  scale <- mkClassMethod cls 0 "scale" scaleScheme
  norm <- mkClassMethod cls 1 "norm" normScheme

  return cls

mkPassableClass = mdo
  a <- newTyVar Star Nothing
  let cls = Class { clsParam = a
                  , clsConstraint = []
                  , clsMethods = []
                  , clsName = "Passable"
                  , clsInstances = [int_instance, float_instance,
                                    bool_instance, none_instance,
                                    any_instance,
                                    list_instance, iter_instance,
                                    tuple2_instance]
                  , clsTypeCon = pyonBuiltin SystemF.the_PassConv
                  , clsDictCon =
                    internalError "Class 'Passable' has no dictionary constructor"
                  }
  
  let int_instance =
        monomorphicInstance cls (ConTy $ tiBuiltin the_con_int)
        (Just $ pyonBuiltin SystemF.the_passConv_int) []
  let float_instance =
        monomorphicInstance cls (ConTy $ tiBuiltin the_con_float)
        (Just $ pyonBuiltin SystemF.the_passConv_float) []
  let bool_instance =
        monomorphicInstance cls (ConTy $ tiBuiltin the_con_bool)
        (Just $ pyonBuiltin SystemF.the_passConv_bool) []
  let none_instance =
        monomorphicInstance cls (ConTy $ tiBuiltin the_con_NoneType)
        (Just $ pyonBuiltin SystemF.the_passConv_NoneType) []
  let any_instance =
        monomorphicInstance cls (ConTy $ tiBuiltin the_con_Any)
        (Just $ pyonBuiltin SystemF.the_passConv_Any) []
        
  b <- newTyVar Star Nothing
  let list_instance =
        Instance
        { insQVars = [b]
        , insConstraint = [passable $ ConTy b]
        , insClass = cls
        , insType = ConTy (tiBuiltin the_con_list) @@ ConTy b
        , insCon = Just $ pyonBuiltin SystemF.the_passConv_list
        , insMethods = []
        }
  let iter_instance =
        Instance
        { insQVars = [b]
        , insConstraint = [passable $ ConTy b]
        , insClass = cls
        , insType = ConTy (tiBuiltin the_con_iter) @@ ConTy b
        , insCon = Just $ pyonBuiltin SystemF.the_passConv_iter
        , insMethods = []
        }
  
  c <- newTyVar Star Nothing
  let tuple2_instance =
        Instance
        { insQVars = [b, c]
        , insConstraint = [passable $ ConTy b, passable $ ConTy c]
        , insClass = cls
        , insType = TupleTy 2 @@ ConTy b @@ ConTy c
        , insCon = Just $ SystemF.getPyonTuplePassConv' 2
        , insMethods = []
        }
  
  return cls

-------------------------------------------------------------------------------
-- Global function initialization

passable t = t `IsInst` tiBuiltin the_Passable

mkMapType = forallType [Star :-> Star, Star, Star] $ \ [t, a, b] ->
  let tT = ConTy t
      aT = ConTy a
      bT = ConTy b
  in ([ tT `IsInst` tiBuiltin the_Traversable
      , passable (tT @@ aT)
      , passable (tT @@ bT)
      ],
      functionType [functionType [aT] bT, tT @@ aT] (tT @@ bT))

mkReduceType = forallType [Star :-> Star, Star] $ \ [t, a] ->
  let tT = ConTy t
      aT = ConTy a
  in ([tT `IsInst` tiBuiltin the_Traversable,
       passable aT, passable (tT @@ aT)],
      functionType [aT, functionType [aT, aT] aT, tT @@ aT] aT)

mkReduce1Type = forallType [Star :-> Star, Star] $ \ [t, a] ->
  let tT = ConTy t
      aT = ConTy a
  in ([tT `IsInst` tiBuiltin the_Traversable,
       passable aT, passable (tT @@ aT)],
      functionType [functionType [aT, aT] aT, tT @@ aT] aT)

mkZipType =
  forallType [Star :-> Star, Star :-> Star, Star, Star] $ \ [s, t, a, b] ->
  let sT = ConTy s
      tT = ConTy t
      aT = ConTy a
      bT = ConTy b
  in ([ sT `IsInst` tiBuiltin the_Traversable
      , tT `IsInst` tiBuiltin the_Traversable]
     , functionType [sT @@ aT, tT @@ bT]
       (ConTy (tiBuiltin the_con_iter) @@ (TupleTy 2 @@ aT @@ bT)))

mkIotaType =
  return $ monomorphic $
  functionType [ConTy (tiBuiltin the_con_NoneType)] (ConTy (tiBuiltin the_con_iter) @@ ConTy (tiBuiltin the_con_int))

mkUndefinedType =
  forallType [Star] $ \[a] -> ([], ConTy a)

mkMakelistType =
  forallType [Star] $ \[a] ->
  let aT = ConTy a
      sT = ConTy (tiBuiltin the_con_iter) @@ aT
      lT = ConTy (tiBuiltin the_con_list) @@ aT
  in ([passable aT], functionType [sT] lT)

mkDoType =
  forallType [Star] $ \[a] ->
  ([passable (ConTy a)], functionType [ConTy a] (ConTy (tiBuiltin the_con_iter) @@ ConTy a))

mkGuardType =
  forallType [Star] $ \[a] ->
  ([], functionType [ ConTy (tiBuiltin the_con_bool)
                    , ConTy (tiBuiltin the_con_iter) @@ ConTy a]
       (ConTy (tiBuiltin the_con_iter) @@ ConTy a))

mkIterBindType =
  forallType [Star, Star] $ \[a, b] ->
  let aT = ConTy a
      bT = ConTy b
  in ([passable aT, passable bT],
   functionType [ ConTy (tiBuiltin the_con_iter) @@ aT
                , functionType [aT] (ConTy (tiBuiltin the_con_iter) @@ bT)
                ]
   (ConTy (tiBuiltin the_con_iter) @@ ConTy b))

mkBinaryOpType =
  forallType [Star] $ \[a] ->
  ([passable (ConTy a)], functionType [ConTy a, ConTy a] (ConTy a))

mkBinaryIntType =
  let int = ConTy (tiBuiltin the_con_int)
  in return $ monomorphic $ functionType [int, int] int

mkGlobalVar name typ con = do
  scm <- typ
  let exp pos = TIRecExp $
                SystemF.ConE (Gluon.mkSynInfo pos Gluon.ObjectLevel) con
  let ass = polymorphicAssignment scm exp
  predefinedVariable (Just $ builtinLabel name) ass

getClassVar name cls index = clmVariable $ clsMethods cls !! index

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
            -- 1. Gluon name
            -- 2. kind
            -- 3. system F constructor
            [ ("int", Star, [| pyonBuiltin SystemF.the_int |])
            , ("float", Star, [| pyonBuiltin SystemF.the_float |])
            , ("bool", Star, [| pyonBuiltin SystemF.the_bool |])
            , ("NoneType", Star, [| pyonBuiltin SystemF.the_NoneType |])
            , ("iter", Star :-> Star, [| pyonBuiltin SystemF.the_Stream |])
            , ("list", Star :-> Star, [| pyonBuiltin SystemF.the_list |])
            , ("Any", Star, [| pyonBuiltin SystemF.the_Any |])
            ]
            
          classes =
            [ ("Eq", [| mkEqClass |])
            , ("Ord", [| mkOrdClass |])
            , ("Traversable", [| mkTraversableClass |])
            , ("Additive", [| mkAdditiveClass |])
            , ("Vector", [| mkVectorClass |])
            , ("Passable", [| mkPassableClass |])
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
              ("iota", [| mkIotaType |]
              , [| pyonBuiltin SystemF.the_fun_iota |]
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
              ("__mul__", [| mkBinaryOpType |]
              , [| pyonBuiltin SystemF.the_oper_MUL |]
              ),
              ("__div__", [| mkBinaryOpType |]
              , [| pyonBuiltin SystemF.the_oper_DIV |]
              ),
              ("__mod__", [| mkBinaryIntType |]
              , [| pyonBuiltin SystemF.the_oper_MOD |]
              ),
              ("__floordiv__", [| mkBinaryOpType |]
              , [| pyonBuiltin SystemF.the_oper_FLOORDIV |]
              ),
              ("__power__", [| mkBinaryOpType |]
              , [| pyonBuiltin SystemF.the_oper_POWER |]
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
            , ([| the_Additive |], ["__add__", "__sub__", "__negate__", "zero"])
            , ([| the_Vector |], ["scale", "norm"])
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
                            clsMethods (tiBuiltin $(cls)) !! index
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

