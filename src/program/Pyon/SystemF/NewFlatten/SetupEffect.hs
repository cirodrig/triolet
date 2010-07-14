
{-# LANGUAGE EmptyDataDecls, TypeFamilies, FlexibleInstances,
             FlexibleContexts, ViewPatterns, ScopedTypeVariables,
             Rank2Types #-}
module Pyon.SystemF.NewFlatten.SetupEffect
       (EI, EIExp,
        eiPassType,
        pprExp,
        EIBinder,
        ExpOf(EIType, fromEIType),
        SFExpOf(EIExp, eiType, eiEffect, eiRegion, eiReturnType, eiExp),
        EIExp'(..),
        AltOf(Alt, eialtConstructor, eialtTyArgs, eialtParams, eialtBody),
        FunOf(EIFun, funInfo, funEffectParams, funParams, funReturnType,
              funReturnPassType, funEffect, funBody),
        Def(Def),
        expReturnsNewValue,
        runEffectInference)
where

import Codec.Binary.UTF8.String
import Control.Monad
import Control.Monad.Trans
import Data.Either
import Data.Function
import Data.IORef
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import Debug.Trace
import System.IO.Unsafe
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.MonadLogic
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Gluon.Core.Level
import Gluon.Core(Structure, Rec, Whnf, Subst, SubstRec,
                  Var, varName, varID,
                  Con(..),
                  Binder(..), Binder'(..), RBinder, binderValue)
import qualified Gluon.Core as Gluon
import Gluon.Eval.Environment
import Gluon.Eval.Eval
import qualified Gluon.Eval.Typecheck

import Pyon.Globals
import qualified Pyon.SystemF.Builtins as SystemF
import qualified Pyon.SystemF.Syntax as SystemF
import qualified Pyon.SystemF.Print as SystemF
import Pyon.SystemF.Syntax(ExpInfo, SFRecExp, RExp, RType, RecType,
                           FunOf, Fun, AltOf, RecAlt, Lit(..), Def(..))
import Pyon.SystemF.Typecheck

import Pyon.SystemF.NewFlatten.PassConv

-- | Set this to 'True' to debug the effect subtyping tests
debugApply = False

whenM :: Monad m => m Bool -> m () -> m ()
whenM test m = do
  b <- test
  if b then m else return ()

withMany :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c
withMany f xs k = go xs k
  where
    go (x:xs) k = f x $ \y -> go xs $ \ys -> k (y:ys)
    go []     k = k []

-- True if the constructor 'c' is the type constructor of a dictionary type
isDictionaryTypeCon c =
  c `elem` [SystemF.pyonBuiltin SystemF.the_PassConv]

-------------------------------------------------------------------------------

data EI
instance Structure EI

newtype instance Gluon.ExpOf EI s = EIType {fromEIType :: RType}

type EIType = Gluon.ExpOf EI EI {- O -}

toEIType :: TRType -> EIType
toEIType (TypedSFType ty) = EIType ty

fromTypedType (TypedSFType ty) = ty

fromTypedExpression :: TRExp -> SFRecExp Rec
fromTypedExpression (TypedSFExp (TypeAnn _ e)) =
  SystemF.mapSFExp fromExp fromAlt fromFun fromType e
  where
    fromExp = fromTypedExpression
    fromAlt (TypedSFAlt (TypeAnn _ a)) = SystemF.mapAlt fromExp fromType a
    fromFun (TypedSFFun (TypeAnn _ f)) =
      SystemF.Fun { SystemF.funInfo = SystemF.funInfo f
                  , SystemF.funTyParams = map (\(SystemF.TyPat v ty) -> SystemF.TyPat v (fromType ty)) $ SystemF.funTyParams f
                  , SystemF.funParams = map (SystemF.mapPat fromType) $ SystemF.funParams f
                  , SystemF.funReturnType = fromType $ SystemF.funReturnType f
                  , SystemF.funBody = fromExp $ SystemF.funBody f
                  }
    fromType (TypedSFType t) = t
    
-- | During effect inference, variable binders are annotated with a region 
-- and a parameter passing convention
type EIBinder = Binder EI (Maybe RVar, PassType)

eiBinder :: Var -> EIType -> Maybe RVar -> PassType -> EIBinder
eiBinder v ty rgn pass_type = Binder v ty (rgn, pass_type)

eiBinderRegion :: EIBinder -> Maybe RVar
eiBinderRegion (Binder _ _ (rgn, _)) = rgn

eiBinderPassType :: EIBinder -> PassType
eiBinderPassType (Binder _ _ (_, pass_type)) = pass_type

data instance SFExpOf EI EI =
    EIExp
    { eiType     :: !RType   -- ^ Inferred System F type
    , eiDocument :: Doc      -- ^ Original expression; for debugging
    , eiEffect   :: Effect   -- ^ Effect of executing this expression.  Does
                             --   not include the effect of using the
                             --   expression's return value.
    , eiRegion :: !(Maybe RVar) -- ^ Result's region (if any).  Later steps
                                --   of compilation may involve coercing the
                                --   result from a representation that doesn't
                                --   have a region to one that does, or vice
                                --   versa; this is the result region before
                                --   coercion.
      -- | Result's parameter-passing convention
    , eiReturnType :: !PassTypeAssignment
    , eiExp    :: EIExp'
    }
type EIExp = SFExpOf EI EI

instance HasSourcePos (SFExpOf EI EI) where
  getSourcePos e = getSourcePos (eiExp e)
  setSourcePos e p = e {eiExp = setSourcePos (eiExp e) p}

eiPassType :: EIExp -> PassType
eiPassType e =
  case eiReturnType e
  of MonoAss pt -> pt
     _ -> internalError "eiPassType: Expression is polymorphic"

-- | Return the expression's return region, if it is not seen outside the
-- immediately consuming expression.
hiddenReturnRegion :: EIExp -> Maybe RVar
hiddenReturnRegion expression
  | expReturnsNewValue expression = eiRegion expression
  | otherwise = Nothing

hiddenReturnRegions :: [EIExp] -> [RVar]
hiddenReturnRegions expressions = mapMaybe hiddenReturnRegion expressions

data EIExp' =
    -- | A variable reference
    VarE
    { expInfo :: ExpInfo
    , expVar :: Var
    }
    -- | A constructor value
  | ConE
    { expInfo :: ExpInfo
    , expCon :: Gluon.Con
    }
    -- | A literal value
  | LitE
    { expInfo :: ExpInfo
    , expLit :: !Lit
    , expType :: RecType EI
    }
    -- | A type
  | TypeE
    { expInfo :: ExpInfo
    , expTypeValue :: RecType EI
    }
    -- | An effect-polymorphic instantiation.
  | InstanceE
    { expInfo :: ExpInfo
    , expOper :: EIExp
      -- | Effect arguments to the function call.  These arguments are
      -- initially not assigned.  They are filled in by effect inference.
    , expEffectArgs :: [Effect]
    }
    -- | A placeholder for a recursively defined function.
  | RecPlaceholderE
    { expInfo :: ExpInfo
      -- | The variable whose type will be used to complete this placeholder 
    , expVar :: !Var
      -- | The placeholder expression's actual value.  It starts out as 
      -- Nothing, and gets assigned later.
    , expPlaceholderValue :: !(IORef (Maybe EIExp))
    }
    -- | Function call
  | CallE
    { expInfo :: ExpInfo
    , expOper :: EIExp
    , expArgs :: [EIExp]
    }
    -- | Lambda expression
  | FunE
    { expInfo :: ExpInfo
    , expFun :: Fun EI
    }
    -- | Stream-building expression
  | DoE
    { expInfo :: ExpInfo
    , expTyArg :: RecType EI
    , expPassConv :: EIExp
    , expBody :: EIExp
    }
    -- | Let expression
  | LetE
    { expInfo :: ExpInfo
    , expBinder :: EIBinder
    , expValue :: EIExp
    , expBody :: EIExp
    }
    -- | Recursive definition group
  | LetrecE
    { expInfo :: ExpInfo
    , expDefs :: [Def EI]
    , expBody :: EIExp
    }
    -- | Case analysis 
  | CaseE
    { expInfo :: ExpInfo
    , expScrutinee :: EIExp
    , expAlternatives :: [RecAlt EI]
    }

instance HasSourcePos EIExp' where
  getSourcePos e = getSourcePos (expInfo e)
  setSourcePos e p = e {expInfo = setSourcePos (expInfo e) p}

-- | True if the expression (not a subexpression) creates a new value.
expCreatesNewValue :: EIExp -> Bool
expCreatesNewValue e = exp'CreatesNewValue (eiExp e)

exp'CreatesNewValue :: EIExp' -> Bool
exp'CreatesNewValue e =
  case e
  of VarE {} -> False
     ConE {} -> True
     LitE {} -> True
     TypeE {} -> True
     InstanceE {} -> True
     RecPlaceholderE {} -> False
     CallE {} -> True
     DoE {} -> True
     FunE {} -> True
     LetE {expBody = b} -> False
     LetrecE {expBody = b} -> False
     CaseE {} -> True

-- | True if the expression will be flattened into something that creates or
-- initializes a new value.  False otherwise.
--
-- An expression @e@ will share its return region with another
-- expression or variable iff @expReturnsNewValue e == False@.
expReturnsNewValue :: EIExp -> Bool
expReturnsNewValue e = exp'ReturnsNewValue (eiExp e)

-- | True if the expression will be flattened into something that creates or
-- initializes a new value.  False otherwise.
exp'ReturnsNewValue :: EIExp' -> Bool
exp'ReturnsNewValue e =
  case e
  of VarE {} -> False
     ConE {} -> True
     LitE {} -> True
     TypeE {} -> True
     InstanceE {} -> True
     RecPlaceholderE {} -> False
     CallE {} -> True
     DoE {} -> True
     FunE {} -> True
     LetE {expBody = b} -> expReturnsNewValue b
     LetrecE {expBody = b} -> expReturnsNewValue b
     CaseE {} -> True

data instance AltOf EI EI =
  Alt { eialtConstructor :: !Gluon.Con
      , eialtTyArgs :: [RecType EI]
      , eialtParams :: [EIBinder]
      , eialtBody :: EIExp
      }

data instance FunOf EI s =
  EIFun { funInfo       :: ExpInfo
          -- | Inferred effect parameters.
        , funEffectParams :: [EVar]
          -- | The list of function parameters.  Each parameter is annotated
          -- with a parameter-passing convention.
        , funParams     :: [EIBinder]
          -- | The System F return type
        , funReturnType :: EIType
          -- | The return value's parameter passing convention
        , funReturnPassType :: PassType
          -- | The function's side effect
        , funEffect     :: Effect
          -- | The function body
        , funBody       :: SFRecExp s
        }

-------------------------------------------------------------------------------
-- Pretty-printing

angles :: Doc -> Doc
angles d = text "<" <> d <> text ">"

pprBlock :: [Doc] -> Doc
pprBlock [] = text "{}"
pprBlock [x] = x
pprBlock (x:xs) = vcat $ (text "{" <+> x) : [semi <+> y | y <- xs] ++ [text "}"]

pprExp :: EIExp -> Doc
pprExp e =
  let eff_doc = angles $ pprEffect (eiEffect e)
      ret_doc = case eiReturnType e
                of MonoAss rt -> pprPassType rt
                   PolyAss pt -> pprPolyPassType pt
  in hang (sep [ret_doc, eff_doc]) 2 (pprExp' $ eiExp e)

pprExp' :: EIExp' -> Doc
pprExp' expression = 
  case expression
  of VarE {expVar = v} -> SystemF.pprVar v
     ConE {expCon = c} -> text (showLabel $ conName c)
     LitE {expLit = l} -> SystemF.pprLit l
     TypeE {expTypeValue = v} -> Gluon.pprExp $ fromEIType v
     InstanceE {expOper = op, expEffectArgs = args} ->
       sep $ map parens $ pprExp op : map pprEffect args
     RecPlaceholderE {expVar = v} -> parens $
                                     text "PLACEHOLDER" <+> SystemF.pprVar v
     CallE {expOper = op, expArgs = args} ->
       sep $ map parens $ pprExp op : map pprExp args
     DoE {expBody = body} -> text "do" <+> pprExp body
     FunE {expFun = f} -> pprFun f
     LetE {} -> pprSequence expression
     LetrecE {} -> pprSequence expression
     CaseE {expAlternatives = [_]} -> pprSequence expression
     CaseE {expScrutinee = scr, expAlternatives = alts} ->
       text "case" <+> pprExp scr $$
       text "of" <+> vcat (map pprAlt alts)

pprSequence :: EIExp' -> Doc
pprSequence expression = pprBlock $ lines expression
  where
    lines expression =
      case expression
      of LetE {expBinder = b, expValue = rhs, expBody = body} ->
           let binder_doc = pprBinder b
               rhs_doc = pprExp rhs
               line = hang (text "let" <+> binder_doc <+> text "=") 4 rhs_doc
           in line : lines (eiExp body)
         LetrecE {expDefs = defs, expBody = body} ->
           let defs_doc = pprDefGroup defs
               line = text "letrec" $$ nest 2 defs_doc
           in line : lines (eiExp body)
         CaseE {expScrutinee = scr, expAlternatives = [alt]} ->
           let scr_doc = pprExp scr
               alt_doc = pprAltPattern alt
               line = hang (alt_doc <+> text "<-") 4 scr_doc
           in line : lines (eiExp $ eialtBody alt)
         _ -> [pprExp' expression]

pprAltPattern :: RecAlt EI -> Doc
pprAltPattern alt =
  let con = text $ showLabel $ conName $ eialtConstructor alt
      ty_args = map (parens . Gluon.pprExp . fromEIType) $ eialtTyArgs alt
      params = map (parens . pprBinder) $ eialtParams alt
  in con <+> cat (ty_args ++ params)

pprAlt :: RecAlt EI -> Doc
pprAlt alt =
  let sig = pprAltPattern alt <> text "."
      body = pprExp $ eialtBody alt
  in hang sig 4 body

pprFun :: Fun EI -> Doc
pprFun fun =
  let char_lambda = text $ encodeString [toEnum 0x03bb]
      char_Lambda = text $ encodeString [toEnum 0x039b]
      binders = map (parens . pprEffectVar) (funEffectParams fun) ++
                map (parens . pprBinder) (funParams fun)
      ret = pprPassType $ funReturnPassType fun
      eff = pprEffect $ funEffect fun
      signature_components = binders ++ [nest (-3) $ text "->" <+> ret
                                        , nest (-2) $ text "|" <+> eff]
      signature = char_lambda <+> sep signature_components <> text "."
      body = pprExp $ funBody fun
  in hang signature 4 body

pprDef :: Def EI -> Doc
pprDef (Def v f) = hang (SystemF.pprVar v <+> text "=") 4 (pprFun f)

pprDefGroup :: [Def EI] -> Doc
pprDefGroup defs = pprBlock $ map pprDef defs

pprBinder :: EIBinder -> Doc
pprBinder (Binder v _ (rgn, pt)) =
  let region = case rgn
               of Nothing -> empty
                  Just r  -> text "@" <> pprEffectVar r
  in SystemF.pprVar v <> region <+> text ":" <+> pprPassType pt

-------------------------------------------------------------------------------
-- Creating initial effect inference information from types

funTypeToPassType :: Gluon.WSRExp -> RegionM PassType
funTypeToPassType expression = make_cc emptyEffect expression
  where
    -- Create the calling convention.  Accumulate function parameters into
    -- the function's side effect.
    make_cc effect expression =
      case Gluon.fromWhnf expression
      of Gluon.FunE { Gluon.expMParam = Binder' mv dom ()
                    , Gluon.expRange = rng} -> do
           param <- typeToFunParam mv =<< evalHead dom
           
           -- Include this parameter in the function's side effect
           let effect' = effect `effectUnion`
                         maybeVarEffect (paramRegion param)
                         
           rng_pc <- make_cc effect' =<< evalHead rng
           return (FunT param rng_pc)
         _ -> do
             unless (getLevel (Gluon.fromWhnf expression) == TypeLevel) $
               internalError "funTypeToPassType: Expecting a type"

             -- Create a variable to
             -- stand for this expression's free effect
             effect_var <- newEffectVar Nothing
             let effect' = effect `effectUnion` varEffect effect_var
             
             -- The function produces a side effect and returns its result
             pt <- typeToPassType expression
             return $ RetT effect' pt

-- | Convert a type expression to a parameter passing type
typeToPassType :: Gluon.WSRExp -> RegionM PassType
typeToPassType expression =
  case getLevel $ Gluon.fromWhnf expression
  of TypeLevel ->
       case Gluon.fromWhnf expression
       of Gluon.FunE {} -> funTypeToPassType expression
          _             -> typeToEType expression
     KindLevel -> return TypeT

typeToFunParam :: Maybe Var -> Gluon.WSRExp -> RegionM FunParam
typeToFunParam dependent_var ty = do
  pass_type <- typeToPassType ty
  rgn <- newRegionVarIfBorrowed (varName =<< dependent_var) pass_type
  return $ FunParam rgn dependent_var pass_type

-- | Called by 'typeToPassType' to handle some cases.
typeToEType :: Gluon.WSRExp -> RegionM PassType
typeToEType expression =
  case Gluon.fromWhnf expression
  of Gluon.AppE { Gluon.expOper = op@(Gluon.substHead ->
                                   Gluon.ConE {Gluon.expCon = con})
                , Gluon.expArgs = args}
       | con `SystemF.isPyonBuiltin` SystemF.the_Stream -> do
          let ![arg] = args
          output <- typeToPassType =<< evalHead arg
          
          -- Create an effect variable for the stream
          evar <- newEffectVar Nothing
          return $ StreamT (varEffect evar) output
          
       | isDictionaryTypeCon con -> do
           -- Dictionary types always involve empty effect types
           op' <- typeToPassType =<< evalHead op
           args' <- mapM (typeToPassType <=< evalHead) args
           
           -- Clear any effect type variables that were created
           clearFlexibleEffectVariables op'
           mapM_ clearFlexibleEffectVariables args'

           let pass_type = typePassConv expression
           return $ AppT pass_type op' args'

     Gluon.AppE {Gluon.expOper = op, Gluon.expArgs = args} -> do
       op' <- typeToPassType =<< evalHead op
       args' <- mapM (typeToPassType <=< evalHead) args
       let pass_type = typePassConv expression
       return $ AppT pass_type op' args'

     Gluon.VarE {Gluon.expVar = v} ->
       return $ VarT Borrowed v
       
     Gluon.ConE {} ->
       return $ ConstT Borrowed (Gluon.substFullyUnder $ Gluon.fromWhnf expression)
     Gluon.LitE {} ->
       return $ ConstT Borrowed (Gluon.substFullyUnder $ Gluon.fromWhnf expression)
     _ -> traceShow (Gluon.pprExp $ Gluon.fromWhnf $ Gluon.substFullyUnderWhnf expression) $ internalError "typeToEType"
  where
    typePassConv expression =
      case Gluon.unpackRenamedWhnfAppE expression
      of Just (con, _) -> typeConstructorPassConv con
         _ | getLevel (Gluon.fromWhnf $ Gluon.substFullyUnderWhnf expression) == KindLevel -> ByValue
           | otherwise -> Borrowed

-- | Get the parameter-passing convention of values of the given type.  The
-- result describes values of the fully-applied type constructor.
typeConstructorPassConv :: Con -> PassConv
typeConstructorPassConv con =
  case IntMap.lookup (fromIdent $ conID con) table
  of Just x -> x
     Nothing -> internalError $
                "typeConstructorPassConv: No information for constructor " ++
                showLabel (conName con)
  where
    table = IntMap.fromList [(fromIdent $ conID $ SystemF.pyonBuiltin con,
                              pc)
                            | (con, pc) <- assocs]
    
    assocs =
      [ (SystemF.the_NoneType, borrowed)
      , (SystemF.the_Any, borrowed)
      , (SystemF.the_int, borrowed)
      , (SystemF.the_float, borrowed)
      , (SystemF.the_bool, borrowed)
      , (SystemF.the_list, borrowed)
      , (SystemF.the_Stream, Owned)
      , (\_ -> SystemF.getPyonTupleType' 0, borrowed)
      , (\_ -> SystemF.getPyonTupleType' 1, borrowed)
      , (\_ -> SystemF.getPyonTupleType' 2, borrowed)
      , (SystemF.the_PassConv, value)
      , (SystemF.the_EqDict, value)
      , (SystemF.the_OrdDict, value)
      , (SystemF.the_TraversableDict, value)
      , (SystemF.the_AdditiveDict, value)
      , (SystemF.the_VectorDict, value)
      ]
      
    borrowed = Borrowed
    value = ByValue

dataConstructorPassType :: Con -> RegionM PolyPassType
dataConstructorPassType con =
  case IntMap.lookup (fromIdent $ conID con) table
  of Just x -> x
     Nothing -> internalError $
                "dataConstructorPassConv: No information for constructor " ++
                showLabel (conName con)
  where
    table = IntMap.fromList [(fromIdent $ conID $ SystemF.pyonBuiltin con, pc)
                            | (con, pc) <- assocs]

    monomorphic_effect_type c = (c, mono_eff_type (SystemF.pyonBuiltin c))
      where
        -- Look up the constructor's type and convert it.
        -- Clear any flexible side effect variables.
        mono_eff_type c = do
          con_type <- liftPureTC $ Gluon.Eval.Typecheck.getConstructorType c
          pass_type <- typeToPassType =<< evalHead con_type
          clearFlexibleEffectVariables pass_type
          return $ PolyPassType [] pass_type
        
    assocs = monomorphic_assocs ++ polymorphic_assocs
    
    -- These functions have no free effect variables
    monomorphic_assocs =
      map monomorphic_effect_type
      [ SystemF.the_passConv_Any
      , SystemF.the_passConv_int
      , SystemF.the_passConv_float
      , SystemF.the_passConv_bool
      , SystemF.the_passConv_list
      , SystemF.the_passConv_iter
      , SystemF.the_passConv_NoneType
      , (\_ -> SystemF.getPyonTupleCon' 0)
      , (\_ -> SystemF.getPyonTupleCon' 1)
      , (\_ -> SystemF.getPyonTupleCon' 2)
      , (\_ -> SystemF.getPyonTuplePassConv' 0)
      , (\_ -> SystemF.getPyonTuplePassConv' 1)
      , (\_ -> SystemF.getPyonTuplePassConv' 2)
        
      , SystemF.the_eqDict
      , SystemF.the_ordDict
      , SystemF.the_additiveDict
        
      , SystemF.eqMember . SystemF.the_EqDict_int
      , SystemF.neMember . SystemF.the_EqDict_int
      , SystemF.eqMember . SystemF.the_EqDict_float
      , SystemF.neMember . SystemF.the_EqDict_float
      , SystemF.eqMember . SystemF.the_EqDict_Tuple2
      , SystemF.neMember . SystemF.the_EqDict_Tuple2
      , SystemF.gtMember . SystemF.the_OrdDict_int
      , SystemF.geMember . SystemF.the_OrdDict_int
      , SystemF.ltMember . SystemF.the_OrdDict_int
      , SystemF.leMember . SystemF.the_OrdDict_int
      , SystemF.gtMember . SystemF.the_OrdDict_float
      , SystemF.geMember . SystemF.the_OrdDict_float
      , SystemF.ltMember . SystemF.the_OrdDict_float
      , SystemF.leMember . SystemF.the_OrdDict_float
      , SystemF.addMember . SystemF.the_AdditiveDict_float
      , SystemF.subMember . SystemF.the_AdditiveDict_float
      , SystemF.zeroMember . SystemF.the_AdditiveDict_int
      , SystemF.addMember . SystemF.the_AdditiveDict_int
      , SystemF.subMember . SystemF.the_AdditiveDict_int
      , SystemF.zeroMember . SystemF.the_AdditiveDict_float
      , SystemF.addMember . SystemF.the_AdditiveDict_float
      , SystemF.subMember . SystemF.the_AdditiveDict_float
        
      , SystemF.the_oper_MUL
      , SystemF.the_oper_DIV
      , SystemF.the_oper_MOD
      , SystemF.the_oper_POWER
      , SystemF.the_oper_FLOORDIV
      , SystemF.the_oper_BITWISEAND
      , SystemF.the_oper_BITWISEOR
      , SystemF.the_oper_BITWISEXOR
      , SystemF.the_oper_NEGATE
      , SystemF.the_fun_undefined
      ]

    polymorphic_assocs =
      [ (SystemF.the_traversableDict,
         monoPassType traversableDictConstructorType)
      , (SystemF.traverseMember . SystemF.the_TraversableDict_list,
         monoPassType $ traverseFunctionType (constT Borrowed $ Gluon.mkInternalConE $ SystemF.pyonBuiltin SystemF.the_list))
      , (SystemF.traverseMember . SystemF.the_TraversableDict_Stream,
         polyPassType 1 $ \[eff] -> traverseStreamType eff)
      , (SystemF.the_oper_CAT_MAP, catMapType)
      , (SystemF.the_fun_makelist, makelistType)
      , (SystemF.the_fun_reduce1, reduce1Type)
      , (SystemF.the_fun_reduce1_Stream, reduce1StreamType)
      , (SystemF.the_fun_zip, zipType)
      , (SystemF.the_fun_zip_NS, zipNSType)
      , (SystemF.the_fun_zip_SN, zipSNType)
      , (SystemF.the_fun_zip_SS, zipSSType)
      , (SystemF.the_fun_iota, iotaType)
      , (SystemF.the_fun_map, mapType)
      , (SystemF.the_fun_map_Stream, mapStreamType)
      ]

-- The kind * -> *
dataConKind = typeT

traversableType ty = appT ByValue (constT Borrowed traversable) [ty]
  where
    traversable =
      Gluon.mkInternalConE $ SystemF.pyonBuiltin SystemF.the_TraversableDict

passconvType ty = appT ByValue (constT Borrowed passconv) [ty]
  where
    passconv = Gluon.mkInternalConE $ SystemF.pyonBuiltin SystemF.the_PassConv

streamPassType eff ty = streamT eff ty

-- | The type of a function that traverses an object of type @t@.
traverseFunctionType t = 
  funTDep typeT $ \a ->
  funT (passconvType $ varT a) $
  funTRgn (object_type a) $ \rgn ->
  retT emptyEffect (streamPassType (varEffect rgn) (varT a))
  where
    object_type a = appT Borrowed t [varT a]

-- | The type of the stream-traverse function.  Basically, take a stream
-- parameter and return the exact same thing.
traverseStreamType eff = 
  funTDep typeT $ \a ->
  funT (passconvType $ varT a) $
  funT (streamPassType (varEffect eff) (varT a)) $
  retT emptyEffect (streamPassType (varEffect eff) (varT a))

traversableDictConstructorType =
  funTDep dataConKind $ \t ->
  funT (traverseFunctionType (varT t)) $
  retT emptyEffect (traversableType (varT t))

catMapType =
  polyPassType 1 $ \[eff] ->
  funTDep typeT $ \a ->
  funTDep typeT $ \b ->
  funT (passconvType (varT a)) $
  funT (streamPassType (varEffect eff) (varT a)) $
  funT (consumer_type eff a b) $
  retT emptyEffect $ streamPassType (varEffect eff) (varT b)
  where
    consumer_type eff a b =
      funTRgn (varT a) $ \rgn ->
      retT (varEffect rgn) $
      streamPassType (varsEffect [rgn, eff]) (varT b)

makelistType =
  polyPassType 1 $ \[eff] ->
  funTDep typeT $ \a ->
  funT (passconvType (varT a)) $
  funT (streamPassType (varEffect eff) (varT a)) $
  retT (varEffect eff) $ list_type a
  where
    list_constructor =
      Gluon.mkInternalConE $ SystemF.pyonBuiltin SystemF.the_list
    list_type a = appT Borrowed (constT Borrowed list_constructor) [varT a]

reducerFunctionType a eff =
  funTRgn (varT a) $ \r1 ->
  funTRgn (varT a) $ \r2 ->
  retT (varsEffect [r1, r2, eff]) (varT a)

reduce1Type =
  polyPassType 1 $ \[eff] ->
  funTDep typeT $ \t ->
  funTDep typeT $ \a ->
  funT (passconvType (varT a)) $
  funT (passconvType (appT Borrowed (varT t) [varT a])) $
  funT (reducerFunctionType a eff) $
  funTRgn (appT Borrowed (varT t) [varT a]) $ \rgn ->
  retT (varsEffect [rgn, eff]) (varT a)

reduce1StreamType =
  polyPassType 1 $ \[eff] ->
  funTDep typeT $ \a ->
  funT (passconvType (varT a)) $
  funT (passconvType (streamT (varEffect eff) (varT a))) $
  funT (reducerFunctionType a eff) $
  funT (streamPassType (varEffect eff) (varT a)) $
  retT (varEffect eff) (varT a)

zipType =
  polyPassType 1 $ \[eff] ->
  funTDep dataConKind $ \s ->
  funTDep dataConKind $ \t ->
  funTDep typeT $ \a ->
  funTDep typeT $ \b ->
  funT (traversableType (varT s)) $
  funT (traversableType (varT t)) $
  funTRgn (appT Borrowed (varT s) [varT a]) $ \r1 ->
  funTRgn (appT Borrowed (varT t) [varT b]) $ \r2 ->
  retT emptyEffect $ streamPassType (varsEffect [r1, r2, eff]) $ tuple_type a b
  where
    tuple_type a b =
      appT Borrowed (constT Borrowed $ Gluon.mkInternalConE (SystemF.getPyonTupleCon' 2)) [varT a, varT b]

zipNSType =
  polyPassType 1 $ \[eff] ->
  funTDep dataConKind $ \s ->
  funTDep typeT $ \a ->
  funTDep typeT $ \b ->
  funT (traversableType (varT s)) $
  funTRgn (appT Borrowed (varT s) [varT a]) $ \r1 ->
  funT (streamPassType (varEffect eff) (varT b)) $
  retT emptyEffect $ streamPassType (varsEffect [r1, eff]) $ tuple_type a b
  where
    tuple_type a b =
      appT Borrowed (constT Borrowed $ Gluon.mkInternalConE (SystemF.getPyonTupleCon' 2)) [varT a, varT b]

zipSNType =
  polyPassType 1 $ \[eff] ->
  funTDep dataConKind $ \t ->
  funTDep typeT $ \a ->
  funTDep typeT $ \b ->
  funT (traversableType (varT t)) $
  funT (streamPassType (varEffect eff) (varT a)) $
  funTRgn (appT Borrowed (varT t) [varT b]) $ \r2 ->
  retT emptyEffect $ streamPassType (varsEffect [r2, eff]) $ tuple_type a b
  where
    tuple_type a b =
      appT Borrowed (constT Borrowed $ Gluon.mkInternalConE (SystemF.getPyonTupleCon' 2)) [varT a, varT b]

zipSSType =
  polyPassType 1 $ \[eff] ->
  funTDep typeT $ \a ->
  funTDep typeT $ \b ->
  funT (streamPassType (varEffect eff) (varT a)) $
  funT (streamPassType (varEffect eff) (varT b)) $
  retT emptyEffect $ streamPassType (varEffect eff) $ tuple_type a b
  where
    tuple_type a b =
      appT Borrowed (constT Borrowed $ Gluon.mkInternalConE (SystemF.getPyonTupleCon' 2)) [varT a, varT b]

iotaType =
  monoPassType $
  funTRgn (constT Borrowed none_type) $ \rgn ->
  retT emptyEffect $ streamPassType emptyEffect $ constT Borrowed int_type
  where
    none_type = Gluon.mkInternalConE $ SystemF.pyonBuiltin SystemF.the_NoneType
    int_type = Gluon.mkInternalConE $ SystemF.pyonBuiltin SystemF.the_int

mapType =
  polyPassType 1 $ \[eff] ->
  funTDep dataConKind $ \t ->
  funTDep typeT $ \a ->
  funTDep typeT $ \b ->
  funT (traversableType (varT t)) $
  funT (passconvType (appT Borrowed (varT t) [varT a])) $
  funT (passconvType (appT Borrowed (varT t) [varT b])) $
  funT (transformer_type eff a b) $
  funTRgn (appT Borrowed (varT t) [varT a]) $ \rgn ->
  retT (varsEffect [rgn, eff]) (appT Borrowed (varT t) [varT b])
  where
    transformer_type eff a b =
      funTRgn (varT a) $ \rgn ->
      retT (varsEffect [rgn, eff]) $ varT b
  
mapStreamType =
  polyPassType 1 $ \[eff] ->
  funTDep typeT $ \a ->
  funTDep typeT $ \b ->
  funT (passconvType (streamT (varEffect eff) (varT a))) $
  funT (passconvType (streamT (varEffect eff) (varT b))) $
  funT (transformer_type eff a b) $
  funT (streamPassType (varEffect eff) (varT a)) $
  retT emptyEffect (streamPassType (varEffect eff) (varT b))
  where
    transformer_type eff a b =
      funTRgn (varT a) $ \rgn ->
      retT (varsEffect [rgn, eff]) $ varT b


-- | Apply a calling convention to some parameters.  Return the return value's
-- passing convention and the effect of executing the function.
applyCallConv :: SourcePos
                 -- | Operator parameter-passing convention
              -> PassType
                 -- | Argument regions, parameter-passing conventions, and
                 --   values
              -> [(Maybe RVar, PassType, Maybe PassType)]
              -> EffInf (PassType, Effect)
applyCallConv pos pass_type args
  | debugApply = traceShow message $ applyCallConv_worker pos pass_type args
  | otherwise = applyCallConv_worker pos pass_type args
  where    
    message = text "applyCallConv" $$ nest 2 (text (show pos) $$ oper_doc $$ text "--------" $$ vcat arg_docs)
    oper_doc = pprPassType pass_type
    arg_docs = map arg_doc args
    arg_doc (rgn, ty, val) = 
      let val_doc = case val
                    of Just v -> pprPassType v <+> text "="
                       Nothing -> empty
          rgn_doc = case rgn
                    of Just v -> text "@" <+> pprEffectVar v
                       Nothing -> empty
      in val_doc <+> pprPassType ty <+> rgn_doc
  
applyCallConv_worker pos pass_type args =
  case pass_type
  of FunT parameter range ->
       case args
       of (arg_region, arg_type, arg_mvalue) : args' -> do
            -- Argument must be a subtype of parameter
            assertParameterSubtype arg_type (paramType parameter)
            
            -- Instantiate the parameter variable to the argument's region
            range1 <- liftIO $ instantiate_region
                         (paramRegion parameter) arg_region range
            
            -- Instantiate the type parameter to the argument's value
            let range2 = instantiate_type
                         (paramTyVar parameter) arg_mvalue range1
            
            -- Continue processing the remaining arguments
            applyCallConv_worker pos range2 args'

          [] -> do
            -- Undersaturated application
            return (pass_type, emptyEffect)

     RetT eff return_type ->
       case args
       of [] -> return (return_type, eff)
          _ -> do
            -- This is a function that returns a function.  Pass the remaining 
            -- arguments to the returned function, and combine the effects from
            -- all function calls.
            (final_return_type, final_eff) <-
              applyCallConv_worker pos return_type args
            return (final_return_type, effectUnion eff final_eff)
     
     _ ->
       case args
       of [] -> return (pass_type, emptyEffect)
          _ ->
            -- Too many arguments to function.  This should have been
            -- detected by type inference.
            internalError "applyCallConv: Oversaturated application"
  where
    instantiate_region (Just param_rgn) (Just arg_rgn) range =
      expandAndRenameE param_rgn arg_rgn range
    instantiate_region (Just param_rgn) Nothing range =
      -- If the function expects its argument to have a region, the argument 
      -- must have a region
      internalError "applyCallConv: missing argument region"
    instantiate_region Nothing _ range = return range
    
    instantiate_type (Just param_tyvar) (Just arg_type) range =
      assignT param_tyvar arg_type range
    instantiate_type (Just param_tyvar) Nothing range = 
      -- If the function expects its argument to be a type, the argument 
      -- must be a type
      internalError "applyCallConv: missing argument type"
    instantiate_type Nothing _ range = range

-- | Assert that param_type is a subtype of arg_type.
-- As a special case, if arg_type is a dictionary type, then effect parameters
-- are ignored during the comparison.
assertParameterSubtype arg_type param_type
  | param_is_dictionary_type =
      assertSubtype (clear_stream_effects arg_type)
                    (clear_stream_effects param_type)
  | otherwise =
      assertSubtype arg_type param_type
  where
    clear_stream_effects pt =
      case pt
      of AppT pc op args -> AppT pc (clear_stream_effects op) (map clear_stream_effects args)
         FunT param rng -> FunT (param {paramType = clear_stream_effects $ paramType param}) (clear_stream_effects rng)
         RetT _ pt -> RetT emptyEffect $ clear_stream_effects pt
         StreamT _ pt -> StreamT emptyEffect $ clear_stream_effects pt
         VarT _ _ -> pt
         ConstT _ _ -> pt
         TypeT -> pt

    param_is_dictionary_type =
      case param_type
      of AppT _ (ConstT _ oper_ty) _ ->
           case oper_ty
           of Gluon.ConE {Gluon.expCon = c} -> isDictionaryTypeCon c
              _ -> False
         _ -> False

-------------------------------------------------------------------------------
-- Effect inference

-- | This function is used to ensure that local region variables do not
-- escape their scope through side effects or return values.  The regions
-- are removed from the side effect.  An error is thrown if any of
-- the regions are mentioned in the return parameter-passing convention.
maskOutLocalRegions :: [RVar]   -- ^ Regions to mask out
                    -> Effect   -- ^ Effect to modify
                    -> PassType -- ^ This type must not mention the regions
                    -> EffInf Effect -- ^ Modified effect
maskOutLocalRegions vars effect pass_type = do
  -- Remove local regions from effect
  let exposed_effect = deleteRegionsFromEffect vars effect

  -- Local regions must not be part of the return value
  liftIO $ whenM (pass_type `mentionsAnyE` Set.fromList vars) $
    fail "Effect produced on a variable outside of its scope"

  return exposed_effect

-- | Given a function's parameters, return convention, and side effect,
-- compute a monomorphic parameter-passing convention for it.
funMonoPassType :: [EIBinder] -> PassType -> Effect -> PassType
funMonoPassType params return_type effect =
  foldr add_param (RetT effect return_type) params
  where
    -- Add a parameter.  If mentioned in the range, make it dependent.
    add_param (Binder v _ (mrgn, pass_type)) range =
      let param = if range `passTypeMentionsTypeVar` v
                  then FunParam mrgn (Just v) pass_type
                  else FunParam mrgn Nothing pass_type
      in FunT param range

-- | Get the parameter passing convention from an effect-inferred function
funPassType :: Fun EI -> PolyPassType
funPassType f =
  let monotype =
        funMonoPassType (funParams f) (funReturnPassType f) (funEffect f)
  in PolyPassType (funEffectParams f) monotype

-- | Get a monomorphic parameter-passing convention from a System F function.
systemFFunPassType :: Fun TypedRec -> EffInf PassType
systemFFunPassType (TypedSFFun (TypeAnn ty _)) =
  liftRegionM $ typeToPassType =<< evalHead' (Gluon.fromWhnf ty)
{-  -- Convert parameters
  ty_params <- mapM tyPatAsBinder $ SystemF.funTyParams f
  params <- patternsAsBinders $ SystemF.funParams f

  -- Convert return type
  return_type <- typeToPassType =<< evalHead (SystemF.funReturnType f)
  
  -- Create an effect variable representing the function's free effect
  evar <- newEffectVar Nothing
  
  -- Assume the function reads all its parameters
  let effect = varsEffect (evar : mapMaybe eiBinderRegion params)
      
  return $ funMonoPassType (ty_params ++ params) return_type effect-}
  
-- | Create a new region variable if the parameter uses the 'Borrowed'
-- passing convention.
newRegionVarIfBorrowed :: RegionMonad m =>
                          Maybe Label -> PassType -> m (Maybe RVar) 
newRegionVarIfBorrowed lab pt =
  case typePassConv pt
  of Borrowed -> liftM Just $ newRegionVar lab
     _ -> return Nothing 

-- | Convert a type pattern to a binder.  Type patterns never have
-- free side effects.
tyPatAsBinder :: SystemF.TyPat TypedRec -> EffInf EIBinder
tyPatAsBinder (SystemF.TyPat v ty) = do
  pt <- liftRegionM $ typeToPassType =<< evalHead' (fromTypedType ty)
  return $ eiBinder v (toEIType ty) Nothing pt

patAsBinder :: SystemF.Pat TypedRec -> EffInf EIBinder
patAsBinder (SystemF.VarP v ty) = do
  pt <- liftRegionM $ typeToPassType =<< evalHead' (fromTypedType ty)
  rv <- newRegionVarIfBorrowed (varName v) pt
  return $ eiBinder v (toEIType ty) rv pt

patternsAsBinders :: [SystemF.Pat TypedRec] -> EffInf [EIBinder]
patternsAsBinders pats = mapM patAsBinder pats

initializeBinder :: Binder TypedRec () -> EffInf EIBinder
initializeBinder (Binder v ty ()) = do
  pt <- liftRegionM $ typeToPassType =<< evalHead' (fromTypedType ty)
  rv <- newRegionVarIfBorrowed (varName v) pt
  return $ eiBinder v (toEIType ty) rv pt

-- | Add the bound variable and region to the local environment.
-- Ensure that the bound region variable, if any, is not mentioned in some
-- expression (to ensure that the region doesn't escape).
withBinder :: Parametric a => EIBinder -> EffInf (a, b) -> EffInf b
withBinder (Binder v _ (rgn, pass_type)) m = do
  (check_val, x) <- assumePassType v (MonoAss pass_type) rgn m
  case rgn of
    Nothing -> return ()
    Just rv -> liftIO $ whenM (check_val `mentionsE` rv) $
               fail $ "withBinder: variable's region escapes " ++ show v
  return x

withBinders :: Parametric a => [EIBinder] -> EffInf (a, b) -> EffInf b
withBinders binders m = do
  (_, x) <- foldr with_binder m binders
  return x
  where
    with_binder b m = withBinder b (do (val, x) <- m
                                       return (val, (val, x)))

-- | Add the local function's calling convention to the local environment.
withDef :: Def EI -> EffInf a -> EffInf a
withDef (Def v f) m =
  let pass_type = funPassType f
      assignment = case pass_type
                   of PolyPassType [] mono_type -> MonoAss mono_type
                      _ -> PolyAss pass_type
      in assumePassType v assignment Nothing m

-- | Create or look up the region holding the expression's return value.
-- 'Nothing' is returned if the expression returns using the 'ByValue' or 
-- 'Owned' conventions.  A region is returned if the expression returns 
-- using the 'Borrowed' convention.
createReturnRegion :: EIExp'    -- ^ Expression whose region is returned
                   -> Maybe Label
                   -> PassTypeAssignment
                   -> EffInf (Maybe RVar)
createReturnRegion exp lab rt =
  case exp
  of VarE {expVar = v} -> do
       -- Look up the variable's region
       (_, rgn) <- lookupPassType v
       return rgn
     RecPlaceholderE {expVar = v} -> do
       -- Placeholder variables must be functions, so they don't have a region
       (_, rgn) <- lookupPassType v
       when (isJust rgn) $ internalError "createReturnRegion"
       return Nothing
     -- Use the body's return region
     LetE {expBody = b} -> return $ eiRegion b
     LetrecE {expBody = b} -> return $ eiRegion b
     
     -- All other expression types return a new value, so create a new
     -- region for them
     _ | not (exp'ReturnsNewValue exp) -> internalError "createReturnRegion"
     
     _ -> let pass_type = case rt
                          of MonoAss pass_type -> pass_type
                             PolyAss (PolyPassType _ pass_type) -> pass_type
          in newRegionVarIfBorrowed lab pass_type

-- | Create an expression representing effect-polymorphic instantiation.
-- It consists of an expression applied to effect parameters. 
createInstanceExpression :: EIExp -> PolyPassType -> EffInf EIExp
createInstanceExpression oper (PolyPassType [] mono_type) =
  return $ oper {eiReturnType = MonoAss mono_type}

createInstanceExpression oper poly_type = do
  (effect_args, mono_type) <- liftRegionM $ instantiatePassType poly_type

  let inst_exp1 = InstanceE { expInfo = expInfo $ eiExp oper
                            , expOper = oper
                            , expEffectArgs = map varEffect effect_args}

  ret_region <- createReturnRegion inst_exp1 Nothing (MonoAss mono_type)
  
  let inst_exp2 = EIExp { eiType = eiType oper 
                        , eiDocument = eiDocument oper
                        , eiEffect = eiEffect oper
                        , eiRegion = ret_region
                        , eiReturnType = MonoAss mono_type
                        , eiExp = inst_exp1}
      
  return inst_exp2

-- | Perform effect inference on an expression.  If it's polymorphic, then also
-- instantiate the expression.
effectInferExp :: TRExp -> EffInf EIExp
effectInferExp e = effectInferExpWithName Nothing e

effectInferExpWithName :: Maybe Label -> TRExp -> EffInf EIExp
effectInferExpWithName name
                      typed_expression@(TypedSFExp (TypeAnn ty expression)) = do
  let doc = SystemF.pprExp $ fromTypedExpression typed_expression

  (new_expr, pass_type, effect) <-
    case expression
    of SystemF.TyAppE {} -> effectInferCall name doc typed_expression
       SystemF.CallE {} -> effectInferCall name doc typed_expression
       _ -> effectInferOtherExp name doc ty expression

  -- Create the expression's return region information
  return_region <- createReturnRegion new_expr name pass_type
  
  let poly_expr = EIExp { eiType = Gluon.fromWhnf ty
                        , eiDocument = doc 
                        , eiEffect = effect 
                        , eiRegion = return_region 
                        , eiReturnType = pass_type
                        , eiExp = new_expr
                        }

  -- If the expression is polymorphic, instantiate it to a monomorphic type
  case pass_type of
    MonoAss _  -> return poly_expr
    PolyAss pt -> createInstanceExpression poly_expr pt
    
    -- Recursive assignments should already have been placeholdered
    _ -> internalError "effectInferExpWithName"

effectInferOtherExp :: Maybe Label -> Doc -> Gluon.WRExp
                    -> SFExpOf Rec TypedRec
                    -> EffInf (EIExp', PassTypeAssignment, Effect)
effectInferOtherExp name doc ty expression =
  case expression
  of SystemF.VarE {SystemF.expInfo = inf, SystemF.expVar = v} ->
       effectInferVar inf v
     SystemF.ConE {SystemF.expInfo = inf, SystemF.expCon = c} ->
       effectInferCon inf c
     SystemF.LitE { SystemF.expInfo = inf
                  , SystemF.expLit = l
                  , SystemF.expType = lit_ty} ->
       effectInferLit inf l (fromTypedType lit_ty)
     SystemF.FunE {SystemF.expInfo = inf, SystemF.expFun = f} -> do
       f' <- effectInferFun True f
       let new_expr = FunE {expInfo = inf, expFun = f'}
       return (new_expr, PolyAss $ funPassType f', emptyEffect)

     SystemF.LetE { SystemF.expInfo = inf
                  , SystemF.expBinder = pat
                  , SystemF.expValue = rhs
                  , SystemF.expBody = body} ->
       effectInferLet name inf pat rhs body

     SystemF.LetrecE { SystemF.expInfo = inf
                     , SystemF.expDefs = defs
                     , SystemF.expBody = body} ->
       effectInferLetrec name inf defs body

     SystemF.CaseE { SystemF.expInfo = inf
                   , SystemF.expScrutinee = scr
                   , SystemF.expAlternatives = alts} ->
       effectInferCase inf scr alts

-- | Perform effect inference on a call expression.  This function deconstructs
-- the function call, then calls another effect inference function.
effectInferCall :: Maybe Label -> Doc -> TRExp
                -> EffInf (EIExp', PassTypeAssignment, Effect)
effectInferCall name doc expression =
  -- Get all arguments to the function call
  let (op, args) = unpack [] expression
      (ty, info) = case expression
                   of TypedSFExp (TypeAnn ty e) -> (ty, SystemF.expInfo e)
  in case op
     of TypedSFExp (TypeAnn _ (SystemF.ConE {SystemF.expCon = c}))
          | c `SystemF.isPyonBuiltin` SystemF.the_oper_DO ->
              effectInferDo info (Gluon.fromWhnf ty) args
        _ -> effectInferFlattenedCall info op args
  where
    -- Expand and flatten nested call expressions
    unpack tl typed_expression@(TypedSFExp (TypeAnn ty expression)) =
      case expression
      of SystemF.TyAppE {SystemF.expOper = op, SystemF.expTyArg = arg} ->
           unpack (Left arg : tl) op
         SystemF.CallE {SystemF.expOper = op, SystemF.expArgs = args} ->
           unpack (map Right args ++ tl) op
         _ -> (typed_expression, tl)

effectInferVar :: ExpInfo -> Var -> EffInf (EIExp', PassTypeAssignment, Effect)
effectInferVar inf v = do
  (pt, mrgn) <- lookupPassType v

  -- This expression reads the variable as a side effect
  let effect = case mrgn
               of Just rgn -> varEffect rgn
                  Nothing -> emptyEffect
  
  -- If this is a recursively defined variable, then create a placeholder
  -- expression
  case pt of
    MonoAss _ -> return (VarE inf v, pt, effect)
    PolyAss _ -> assertNothing mrgn $ return (VarE inf v, pt, effect)

    -- For recursive variables, create a placeholder expression and
    -- "instantiate" a monomorphic type
    RecAss rec_var mono_type -> assertNothing mrgn $ do
        placeholder_value <- liftIO $ newIORef Nothing
        let placeholder = RecPlaceholderE inf rec_var placeholder_value
        return (placeholder, MonoAss mono_type, effect)
  where
    -- Only functions (which don't inhabit a region) should have polymorphic 
    -- types
    assertNothing Nothing  m = m
    assertNothing (Just r) _ = internalError "effectInferVar"

effectInferCon :: ExpInfo -> Con -> EffInf (EIExp', PassTypeAssignment, Effect)
effectInferCon inf c = do
  pass_type <- liftRegionM $ dataConstructorPassType c
  return (ConE inf c, PolyAss pass_type, emptyEffect)

effectInferLit :: ExpInfo -> Lit -> RType -> EffInf (EIExp', PassTypeAssignment, Effect)
effectInferLit inf lit ty = do
  let new_exp = LitE inf lit (EIType ty)
  ty' <- liftRegionM $ typeToPassType =<< evalHead' ty
  return (new_exp, MonoAss ty', emptyEffect)

effectInferLet name inf pat rhs body = do
  pat' <- patAsBinder pat
  let rhs_name = case pat' of Binder v _ _ -> Gluon.varName v
  let rhs_region = eiBinderRegion pat'
  rhs' <- effectInferExpWithName rhs_name rhs
  
  -- Infer the body's effect.  The local region must not escape from the body.
  body' <- withBinder pat' $ do
    body' <- effectInferExpWithName name body
    return (eiPassType body', body')
  
  -- Mask out the local variable from the body's effect
  let body_eff = maybeDeleteRegionFromEffect rhs_region (eiEffect body')

  -- Take the union of effects; mask out the local variable
  let eff = effectUnion body_eff (eiEffect rhs')
      new_expr = LetE { expInfo = inf
                      , expBinder = pat'
                      , expValue = rhs'
                      , expBody = body'}
  return (new_expr, eiReturnType body', eff)

effectInferLetrec name inf defs body = do
  (defs', body') <- effectInferDefGroup defs $
                    effectInferExpWithName name body
                         
  let new_expr = LetrecE { expInfo = inf
                         , expDefs = defs'
                         , expBody = body'
                         }
  return (new_expr, eiReturnType body', eiEffect body')

effectInferCase inf scr alts = do
  scr' <- effectInferExp scr
  (alts', alt_effects) <- mapAndUnzipM effectInferAlt alts

  -- Compute a common parameter passing convention
  let pc:pcs = map (eiPassType . eialtBody) alts'
  pass_conv <- foldM joinType pc pcs
  
  let new_expr = CaseE { expInfo = inf
                       , expScrutinee = scr'
                       , expAlternatives = alts'
                       }
  let effect = effectUnions (eiEffect scr' : alt_effects)

  return (new_expr, MonoAss pass_conv, effect)

effectInferAlt :: RecAlt TypedRec -> EffInf (RecAlt EI, Effect)
effectInferAlt (TypedSFAlt (TypeAnn _ alt)) = do
  let ty_args = map toEIType $ SystemF.altTyArgs alt
  patterns <- mapM initializeBinder $ SystemF.altParams alt
  
  -- Free variables aren't permitted in patterns
  liftRegionM $
    mapM_ (clearFlexibleEffectVariables . eiBinderPassType) patterns
  
  withBinders patterns $ do
    body <- effectInferExp $ SystemF.altBody alt
    
    -- Mask out effects on pattern-bound variables
    let local_regions = mapMaybe eiBinderRegion patterns
        exposed_effect = deleteRegionsFromEffect local_regions $ eiEffect body
    
    let new_alt = Alt { eialtConstructor = SystemF.altConstructor alt
                      , eialtTyArgs = ty_args
                      , eialtParams = patterns
                      , eialtBody = body
                      }
    let return_type = eiPassType $ eialtBody new_alt
    return (return_type, (new_alt, exposed_effect))


effectInferDo :: ExpInfo -> RType -> [Either TRType TRExp]
              -> EffInf (EIExp', PassTypeAssignment, Effect)
effectInferDo info result_type [Left ty_arg, Right pc_arg, Right val_arg] = do
  pc_arg' <- effectInferExp pc_arg
  val_arg' <- effectInferExp val_arg
  
  -- The body of the 'do' expression must return a borrowed value
  ret_type <- case typePassConv $ eiPassType val_arg'
              of Borrowed -> return $ eiPassType val_arg'
                 _ -> fail "effect inference failed in an iterator expression body"

  let new_expr = DoE { expInfo = info
                     , expTyArg = toEIType ty_arg
                     , expPassConv = pc_arg'
                     , expBody = val_arg'
                     }
      pass_type = StreamT (eiEffect val_arg') ret_type

  return (new_expr, MonoAss pass_type, eiEffect pc_arg')

effectInferFlattenedCall :: ExpInfo -> TRExp -> [Either TRType TRExp]
                            -> EffInf (EIExp', PassTypeAssignment, Effect)
effectInferFlattenedCall inf op args = do
  op' <- effectInferExp op
  args' <- mapM effectInferArgument args
  
  -- Get the return value's parameter passing convention.
  let args_conv = [ (eiRegion arg_exp, eiPassType arg_exp, arg_pc)
                  | (arg_exp, arg_pc) <- args']
  (return_pass_type, call_effect) <-
    applyCallConv (getSourcePos inf) (eiPassType op') args_conv

  let arg_exps = map fst args'

  -- Mask out effects involving the arguments' return regions.
  exposed_call_effect <-
    let local_regions = hiddenReturnRegions arg_exps
    in maskOutLocalRegions local_regions call_effect return_pass_type

  -- The overall effect is the effect of executing the operator, arguments,
  -- and the function call itself
  let eff = effectUnions $
            exposed_call_effect : eiEffect op' : map eiEffect arg_exps

  return (CallE inf op' arg_exps, MonoAss return_pass_type, eff)

-- | Perform effect inference on a function argument.  If the argument is a
-- type, the corresponding parameter-passing type is returned.
effectInferArgument :: Either TRType TRExp -> EffInf (EIExp, Maybe PassType)
effectInferArgument (Left ty_arg) = do
  let gluon_type = fromTypedType ty_arg
      info = Gluon.mkSynInfo (getSourcePos gluon_type) TypeLevel
      exp  = TypeE info (toEIType ty_arg)
      pass_type = TypeT
  type_as_value <- liftRegionM $ typeToPassType =<< evalHead' gluon_type

  let new_exp = EIExp { eiType = Gluon.pureKindE
                      , eiDocument = Gluon.pprExp gluon_type
                      , eiEffect = emptyEffect
                      , eiRegion = Nothing
                      , eiReturnType = MonoAss pass_type
                      , eiExp = exp
                      }
  return (new_exp, Just type_as_value)

effectInferArgument (Right val_arg) = do
  arg <- effectInferExp val_arg
  return (arg, Nothing)

-- | Print the constraints generated by a computation
debugPrintConstraints message m = do
  (x, cst) <- getConstraint m
  
  liftIO $ print (text message <+> pprConstraint cst)
                  
  addConstraint cst
  return x

-- | Perform effect inference on a function.  The resulting function is
-- not effect-polymorphic.
--
-- If the function will not be generalized (it's a lambda function), then 
-- pass True for the @is_lambda@ parameter; otherwise pass False.
effectInferFun :: Bool -> Fun TypedRec -> EffInf (Fun EI)
effectInferFun is_lambda (TypedSFFun (TypeAnn _ f)) = do
  -- Convert parameters
  ty_params <- mapM tyPatAsBinder $ SystemF.funTyParams f
  params <- patternsAsBinders $ SystemF.funParams f

  -- Eliminate constraints on flexible variables if this function is going 
  -- to be generalized.  Otherwise, don't because it creates more variables.
  let simplify = if is_lambda then id else makeFlexibleVariablesIndependent

  -- Convert body.  Parameter effects are permitted to escape.
  body <- withBinders params $ do
    (_, body) <- simplify $ do
      body <- effectInferExp $ SystemF.funBody f
    
      -- Generalize over the free variables mentioned in the function's type
      let generalize_pass_type =
            funMonoPassType params (eiPassType body) (eiEffect body)

      return (generalize_pass_type, body)
      
    -- Permit parameter effects to escape.
    let escape_pass_type = ()
    return (escape_pass_type, body)

  let new_fun = EIFun { funInfo = SystemF.funInfo f
                      , funEffectParams = []
                      , funParams = ty_params ++ params
                      , funReturnType = toEIType $ SystemF.funReturnType f
                      , funReturnPassType = eiPassType body
                      , funEffect = eiEffect body
                      , funBody = body
                      }
  -- DEBUG: Print the function's parameter passing type
  {- let mono_type = funMonoPassType (funParams new_fun) (funReturnPassType new_fun) (funEffect new_fun)
  liftIO $ print $ pprPassType mono_type
  liftIO $ print . pprPassType =<< expand mono_type
  free_vars <- liftIO $ freeEffectVars mono_type
  liftIO $ print $ text "Free vars" <+> sep (map pprEffectVar $ Set.toList free_vars)-}
  
  return new_fun

-- | Assume a monomorphic type for each function in the definition group.
assumeRecursiveDefGroup :: SystemF.DefGroup TypedRec
                        -> EffInf a
                        -> EffInf a
assumeRecursiveDefGroup defs m = do
  -- Compute non-effect-polymorphic types for each function
  def_types <- forM defs $ \(Def _ f) -> systemFFunPassType f

  -- Assume these types while processing the definition group
  foldr assume_monotype m (zip def_types defs)
  where
    assume_monotype (ty, Def v _) m =
      assumePassType v (RecAss v ty) Nothing m

-- | Perform generalization on a definition group.
--
-- NOTE: Each function is generalized over the effect variables in its own 
-- type only.  Is this always correct?
generalizeTypes :: [(PassType, SystemF.Def EI)]
                -> EffInf (SystemF.DefGroup EI)
generalizeTypes typed_defs = do
  forM typed_defs $ \(ty, Def v f) -> do
    -- Get all effect variables mentioned in the monotype
    (ftvs_pos, ftvs_neg) <- liftIO $ freeEffectVars ty

    -- These are the function paramters
    let ftvs = Set.union ftvs_pos ftvs_neg
        effect_params = Set.toList ftvs
    return $ Def v (f {funEffectParams = effect_params})

-- | Infer types in a definition group.
effectInferDefGroup :: SystemF.DefGroup TypedRec
                    -> EffInf a
                    -> EffInf (SystemF.DefGroup EI, a)
effectInferDefGroup defs m = do
  -- Infer effects in the locally defined functions; generalize over effect
  -- variables
  defs' <- generalizeTypes =<<
           assumeRecursiveDefGroup defs (mapM effect_infer_def defs)

  -- Continue with the body of the definition group
  x <- foldr withDef m defs'
  return (defs', x)
  where
      -- Infer the function type.  Eliminate constraints on effect variables 
      -- that were generated from the function body.
    effect_infer_def :: SystemF.Def TypedRec
                     -> EffInf (PassType, SystemF.Def EI)
    effect_infer_def (Def v f) = do
      f' <- effectInferFun False f
      return (funMonoPassType (funParams f') (funReturnPassType f') (funEffect f'), Def v f')

effectInferTopLevel :: [SystemF.DefGroup TypedRec]
                    -> EffInf [SystemF.DefGroup EI]
effectInferTopLevel (dg:dgs) = do
  (dg', dgs') <- effectInferDefGroup dg $ effectInferTopLevel dgs
  return (dg' : dgs')

effectInferTopLevel [] = return []

effectInferModule :: SystemF.Module TypedRec -> EffInf [[Def EI]]
effectInferModule (SystemF.Module defss _) = do
  (defss', cst) <- getConstraint $ effectInferTopLevel defss
  
  -- No constraints should remain
  liftRegionM $ solveGlobalConstraint cst

  -- DEBUG: print the module
  liftIO $ print $ vcat $ map pprDefGroup defss'
  return defss'
  
runEffectInference :: SystemF.Module TypedRec -> IO [[Def EI]]
runEffectInference mod = do
  -- Create effect variable IDs
  evar_ids <- newIdentSupply

  -- Run effect inference
  withTheVarIdentSupply $ \var_ids ->
    runEffInf evar_ids var_ids $ effectInferModule mod