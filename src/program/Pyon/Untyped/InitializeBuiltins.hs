-- | This module exports one function, which is called to initialize the
-- untyped built-in constants.  It inhabits a separate file due to module 
-- dependences.

{-# LANGUAGE TemplateHaskell, RecursiveDo #-}
module Pyon.Untyped.InitializeBuiltins
       (initializeTIBuiltins)
where

import Control.Concurrent.MVar
import Control.Monad
import Debug.Trace
import qualified Language.Haskell.TH as TH
import System.IO.Unsafe

import Gluon.Common.Error
import Gluon.Common.Label
import Gluon.Common.THRecord
import qualified Gluon.Core as Gluon
import qualified Pyon.SystemF.Builtins as SystemF
import qualified Pyon.SystemF.Syntax as SystemF
import Pyon.Untyped.Data
import Pyon.Untyped.Kind
import Pyon.Untyped.Syntax
import Pyon.Untyped.HMType
import Pyon.Untyped.CallConv
import Pyon.Untyped.TypeAssignment
import Pyon.Untyped.GenSystemF
import Pyon.Untyped.Unification
import Pyon.Untyped.BuiltinsTH
import Pyon.Untyped.Builtins

pyonBuiltin = SystemF.pyonBuiltin

f @@ g = appTy f g

-- | Create an 'untyped' type constructor that corresponds to the given
-- System F type constructor
builtinTyCon name kind sf_con pass_conv pass_conv_con pass_conv_args exec_mode =
  let y = Gluon.mkInternalConE sf_con
  in mkTyCon (builtinLabel name) kind y pass_conv pass_conv_con pass_conv_args exec_mode

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

monomorphicInstance cls ty methods =
  Instance { insQVars = []
           , insConstraint = []
           , insClass = cls
           , insType = ty
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
        (fromEqDict SystemF.the_EqDict_Int)
      float_instance =
        monomorphicInstance cls
        (ConTy $ tiBuiltin the_con_float)
        (fromEqDict SystemF.the_EqDict_Float)
  tuple2_instance <- do
    a <- newTyVar Star Nothing
    b <- newTyVar Star Nothing
    return $ Instance { insQVars = [a, b]
                      , insConstraint = [ ConTy a `IsInst` cls
                                        , ConTy b `IsInst` cls
                                        ]
                      , insClass = cls
                      , insType = TupleTy 2 @@ ConTy a @@ ConTy b
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
        (fromOrdDict SystemF.the_OrdDict_Int)
      float_instance =
        monomorphicInstance cls
        (ConTy $ tiBuiltin the_con_float)
        (fromOrdDict SystemF.the_OrdDict_Float)

  tuple2_instance <- do
    a <- newTyVar Star Nothing
    b <- newTyVar Star Nothing
    return $ Instance { insQVars = [a, b]
                      , insConstraint = [ ConTy a `IsInst` cls
                                        , ConTy b `IsInst` cls
                                        ]
                      , insClass = cls
                      , insType = TupleTy 2 @@ ConTy a @@ ConTy b
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

  let cls = Class { clsParam = t
                  , clsConstraint = []
                  , clsMethods = [iter]
                  , clsName = "Traversable"
                  , clsInstances = [list_instance, iter_instance]
                  , clsTypeCon = pyonBuiltin SystemF.the_TraversableDict
                  , clsDictCon = pyonBuiltin SystemF.the_traversableDict
                  }

  iter <- mkClassMethod cls 0 "__iter__" iter_scheme
  
  let list_instance =
        monomorphicInstance cls
        (ConTy $ tiBuiltin the_con_list)
        (fromTraversableDict SystemF.the_TraversableDict_list)
      iter_instance =
        monomorphicInstance cls
        (ConTy $ tiBuiltin the_con_iter)
        (fromTraversableDict SystemF.the_TraversableDict_Stream)

  return cls
  where
    fromTraversableDict field_name =
      case pyonBuiltin field_name
      of SystemF.TraversableDictMembers iter -> [InstanceMethod iter]

mkAdditiveClass = mdo
  a <- newTyVar Star Nothing
  let binScheme = monomorphic $ functionType [ConTy a, ConTy a] (ConTy a)

  let cls = Class { clsParam = a
                  , clsConstraint = []
                  , clsMethods = [zero, add, sub]
                  , clsName = "Additive"
                  , clsInstances = [int_instance, float_instance]
                  , clsTypeCon = pyonBuiltin SystemF.the_AdditiveDict
                  , clsDictCon = pyonBuiltin SystemF.the_additiveDict
                  }

  zero <- mkClassMethod cls 0 "zero" $ monomorphic (ConTy a)
  add <- mkClassMethod cls 1 "__add__" binScheme
  sub <- mkClassMethod cls 2 "__sub__" binScheme

  let int_instance =
        monomorphicInstance cls
        (ConTy $ tiBuiltin the_con_int)
        (fromAdditiveDict SystemF.the_AdditiveDict_Int)
      float_instance =
        monomorphicInstance cls
        (ConTy $ tiBuiltin the_con_float)
        (fromAdditiveDict SystemF.the_AdditiveDict_Float)
  
  return cls
  where
    fromAdditiveDict field_name =
      case pyonBuiltin field_name
      of SystemF.AdditiveDictMembers zero add sub ->
           [ InstanceMethod zero
           , InstanceMethod add
           , InstanceMethod sub
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

-------------------------------------------------------------------------------
-- Global function initialization

passable t = t `HasPassConv` TypePassConv t

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
  in ([tT `IsInst` tiBuiltin the_Traversable],
      functionType [aT, functionType [aT, aT] aT, tT @@ aT] aT)

mkReduce1Type = forallType [Star :-> Star, Star] $ \ [t, a] ->
  let tT = ConTy t
      aT = ConTy a
  in ([tT `IsInst` tiBuiltin the_Traversable],
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
  functionType [] (ConTy (tiBuiltin the_con_iter) @@ ConTy (tiBuiltin the_con_int))

mkUndefinedType =
  forallType [Star] $ \[a] -> ([], ConTy a)

mkMakelistType =
  forallType [Star] $ \[a] ->
  ([], functionType [ConTy (tiBuiltin the_con_iter) @@ ConTy a]
       (ConTy (tiBuiltin the_con_list) @@ ConTy a))

mkDoType =
  forallType [Star] $ \[a] ->
  ([], functionType [ConTy a] (ConTy (tiBuiltin the_con_iter) @@ ConTy a))

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

mkNegateType =
  forallType [Star] $ \[a] ->
  ([], functionType [ConTy a] (ConTy a))

mkBinaryOpType =
  forallType [Star] $ \[a] ->
  ([], functionType [ConTy a, ConTy a] (ConTy a))

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
            -- 4. parameter-passing convention
            -- 5. parameter-passing constructor Gluon name
            -- 6. parameter-passing constructor arguments needed
            -- 6. execution mode
            [ ("int", Star, [| Gluon.builtin Gluon.the_Int |],
               [| PassConvVal ByVal |],
               "passConv_Int", [],
               [| AsAction |])
            , ("float", Star, [| Gluon.builtin Gluon.the_Float |],
               [| PassConvVal ByVal |],
               "passConv_Float", [],
               [| AsAction |])
            , ("bool", Star, [| pyonBuiltin SystemF.the_bool |], 
               [| PassConvVal ByVal |],
               "passConv_bool", [],
               [| AsAction |])
            , ("NoneType", Star, [| pyonBuiltin SystemF.the_NoneType |],
               [| PassConvVal ByVal |],
               "passConv_NoneType", [],
               [| AsAction |])
            , ("iter", Star :-> Star, [| pyonBuiltin SystemF.the_Stream |],
               [| PassConvFun $ \t ->
                  PassConvVal $ ByClosure (Return AsStream (TypePassConv t)) |],
               "passConv_iter", [True],
               [| AsStream |])
            , ("list", Star :-> Star, [| pyonBuiltin SystemF.the_list |],
               [| PassConvFun $ \_ -> PassConvVal ByRef |],
               "passConv_list", [False],
               [| AsAction |])
            , ("Any", Star, [| pyonBuiltin SystemF.the_Any |],
               [| PassConvVal ByVal |],
               "passConv_Any", [],
               [| AsAction |])
            ]
            
          classes =
            [ ("Eq", [| mkEqClass |])
            , ("Ord", [| mkOrdClass |])
            , ("Traversable", [| mkTraversableClass |])
            , ("Additive", [| mkAdditiveClass |])
            , ("Vector", [| mkVectorClass |])
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
              ("makelist", [| mkMakelistType |]
              , [| pyonBuiltin SystemF.the_fun_makelist |]
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
              ),
              ("__negate__", [| mkNegateType |]
              , [| pyonBuiltin SystemF.the_oper_NEGATE |]
              )
            ]
          cls_members =
            [ ([| the_Eq |], ["__eq__", "__ne__"])
            , ([| the_Ord |], ["__lt__", "__le__", "__gt__", "__ge__"])
            , ([| the_Traversable |], ["__iter__"])
            , ([| the_Additive |], ["zero", "__add__", "__sub__"])
            , ([| the_Vector |], ["scale", "norm"])
            ]

          -- Construct initializers
          typ_initializer (name, _, con, _, _, _, _) =
            ('_':name, [| return $(con) |])
          tycon_initializer (name, kind, con, pass_conv, pass_conv_name,
                             pass_conv_args, mode) =
            let pass_conv_field =
                  TH.varE $ TH.mkName ("SystemF.the_" ++ pass_conv_name)
            in ("_con_" ++ name,
                [| builtinTyCon name kind $(con) $(pass_conv) (pyonBuiltin $(pass_conv_field)) pass_conv_args $(mode) |])
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

