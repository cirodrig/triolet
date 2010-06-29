{-| Expression flattening prior to ANF generation.
--
-- This module uses the result of effect inference to generate code that is
-- in the form required for ANF generation.  Effect variables are converted  
-- to type parameters.  However, the code is not converted to state-passing
-- form here: pass-by-reference variables are not expanded, and state
-- variables are not created.
-}

{-# LANGUAGE TypeFamilies, FlexibleInstances, EmptyDataDecls, ScopedTypeVariables, GeneralizedNewtypeDeriving, DeriveDataTypeable #-}
module Pyon.SystemF.NewFlatten.Flatten(flatten)
where

import Control.Monad
import Control.Monad.Reader
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Gluon.Core.Builtins
import qualified Gluon.Core.Builtins.Effect
import Gluon.Common.Error
import Gluon.Common.Label
import Gluon.Common.Supply
import Gluon.Common.Identifier
import Gluon.Common.SourcePos
import Gluon.Core
import Gluon.Core.RenameBase
import Pyon.Globals
import qualified Pyon.SystemF.Syntax as SystemF
import qualified Pyon.SystemF.Print as SystemF
import qualified Pyon.SystemF.Typecheck as SystemF
import Pyon.SystemF.Builtins
import Pyon.SystemF.NewFlatten.PassConv
import qualified Pyon.SystemF.NewFlatten.SetupEffect as Effect

withMany :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c
withMany f xs k = go xs k
  where
    go (x:xs) k = f x $ \y -> go xs $ \ys -> k (y:ys)
    go []     k = k []

data family ATypeOf s :: * -> *
data family ValOf s :: * -> *
data family StmOf s :: * -> *
data family FunOf s :: * -> *
data family AltOf s :: * -> *
     
type RecAType s = ATypeOf s s
type RecVal s = ValOf s s
type RecStm s = StmOf s s
type RecFun s = FunOf s s
type RecAlt s = AltOf s s

type RAType = AType Rec
type RVal = Val Rec
type RStm = Stm Rec
type RAlt = Alt Rec

-- We also use types to represent effects
type EffectType s = RecAType s

emptyEffectType :: EffectType Rec
emptyEffectType = aExpT Gluon.Core.Builtins.Effect.empty

sconjEffectType :: EffectType Rec -> EffectType Rec -> EffectType Rec
sconjEffectType e1 e2 =
  let con = mkInternalConE $ builtin the_SconjE
  in AAppT (internalSynInfo TypeLevel) con [ passConvType ByValue e1
                                           , passConvType ByValue e2]

-- | The type of a read of an object of type 'ty' at 'rgn'
readEffectType :: RAType -> RExp -> EffectType Rec
readEffectType ty rgn =
  AAppT (internalSynInfo TypeLevel) (mkInternalConE (builtin the_AtE)) [passConvType ByValue ty, passConvType ByValue (aExpT rgn)]

-- | A type-level binder.
data ABinder' a s =
    -- | Bind a value
    ValB' !(Maybe Var) (RecAType s) a
    -- | Bind an owned reference
  | OwnB' (RecAType s) a
    -- | Bind a reference to data of the given type, at the given region
  | RefB' !Var (RecAType s) a
  deriving(Typeable)

abinder'Type :: ABinder' a s -> RecAType s
abinder'Type (ValB' _ ty _) = ty
abinder'Type (OwnB' ty _) = ty
abinder'Type (RefB' _ ty _) = ty

abinder'PassConv :: ABinder' a s -> PassConv
abinder'PassConv (ValB' _ _ _) = ByValue
abinder'PassConv (OwnB' _ _) = Owned
abinder'PassConv (RefB' _ _ _) = Borrowed

data ABinder a s =
    -- | Bind a value
    ValB !Var (RecAType s) a
    -- | Bind an owned reference
  | OwnB !Var (RecAType s) a
    -- | Bind a reference.  This takes an address variable and a pointer 
    -- variable.
  | RefB !Var !Var (RecAType s) a
    -- | Bind a state variable of state at the given address
  | StateB' !(RecExp s) !Var (RecAType s) a
  deriving(Typeable)
    
abinderType :: ABinder a s -> RecAType s
abinderType (ValB _ ty _) = ty
abinderType (OwnB _ ty _) = ty
abinderType (RefB _ _ ty _) = ty

abinderPassConv :: ABinder a s -> PassConv
abinderPassConv (ValB _ _ _) = ByValue
abinderPassConv (OwnB _ _ _) = Owned
abinderPassConv (RefB _ _ _ _) = Borrowed

abinderValue :: SourcePos -> ABinder a Rec -> RVal
abinderValue pos b =
  case b
  of ValB v ty _ ->
       let info = FlatInfo { finfSynInfo = mkSynInfo pos ObjectLevel 
                           , finfType = ty 
                           , finfReturnConv = ByValue
                           , finfEffect = emptyEffectType
                           }
       in ValV info v
     OwnB v ty _ ->
       let info = FlatInfo { finfSynInfo = mkSynInfo pos ObjectLevel 
                           , finfType = ty
                           , finfReturnConv = Owned
                           , finfEffect = emptyEffectType
                           }
       in OwnV info v
     RefB rgn v ty _ ->
       let info = FlatInfo { finfSynInfo = mkSynInfo pos ObjectLevel 
                           , finfType = ty
                           , finfReturnConv = Borrowed
                           , finfEffect = readEffectType ty (mkInternalVarE rgn)
                           }
       in RefV info (mkVarE pos rgn) v
       
substituteBinder' :: Substitution -> ABinder' () Rec -> ABinder' () Rec
substituteBinder' subst abinder =
  case abinder
  of ValB' mv ty () -> ValB' mv (substitute_type ty) ()
     OwnB' ty () -> OwnB' (substitute_type ty) ()
     RefB' v ty () -> RefB' v (substitute_type ty) ()
  where
    substitute_type ty = substFully $ joinSubst subst $ verbatim ty

type PassConvType s = (PassConv, RecAType s)

passConvType :: PassConv -> RecAType s -> PassConvType s
passConvType = (,)

mapPassConvType :: (RecAType s -> RecAType t)
                -> PassConvType s -> PassConvType t
mapPassConvType f (pc, t) = (pc, f t)

-- | An ANF type.  This is really an encoding of a more complex Gluon type.
data instance ATypeOf Rec s =
    AExpT
    { atypeInfo  :: {-# UNPACK #-} !SynInfo 
    , atypeValue :: RecExp s
    }
{-    -- | The type of an owned variable reference
  | AOwnedT
    { atypeInfo  :: {-# UNPACK #-} !SynInfo 
    , atypeType :: RecAType s
    }
    -- | The type of a borrowed variable reference
  | ABorrowedT
    { atypeInfo  :: {-# UNPACK #-} !SynInfo 
    , atypeType :: RecAType s
    }-}
  | AAppT
    { atypeInfo :: {-# UNPACK #-} !SynInfo 
    , atypeOper :: RecExp s
    , atypeArgs :: [PassConvType s]
    }
  | AFunT
    { atypeInfo :: {-# UNPACK #-} !SynInfo 
    , atypeMParam :: ABinder' () s
    , atypeRange :: PassConvType s
    }
  {- | ALamT
    { atypeInfo :: {-# UNPACK #-} !SynInfo 
    , atypeParam :: ABinder () s
    , atypeBody :: PassConvType s
    } -}
  | ARetT
    { atypeInfo :: {-# UNPACK #-} !SynInfo 
    , atypeEffect :: EffectType s
    , atypeRange :: PassConvType s
    }

instance HasLevel (ATypeOf Rec s) where
  getLevel ty = getLevel $ atypeInfo ty
  setLevel ty l = ty {atypeInfo = setLevel (atypeInfo ty) l}

aExpT :: RExp -> RAType
aExpT ty =
  let level = getLevel ty
      pos = getSourcePos ty
  in AExpT (mkSynInfo pos level) ty
     
-- | Deconstruct a function type into parameters and a return type.
-- The function must be a side-effecting function.
unpackFunT :: RAType -> ([ABinder' () Rec], EffectType Rec, PassConv, RAType)
unpackFunT t = unpack id t  
  where
    unpack hd (AFunT {atypeMParam = param, atypeRange = (conv, rng)}) =
      let conv_ok =
            -- Check that the convention is valid
            case rng
            of AFunT {} -> conv == Owned
               ARetT {} -> conv == Borrowed
               _ -> False
      in if conv_ok
         then unpack (hd . (param:)) rng
         else internalError "unpackFunT"

    unpack hd (ARetT {atypeEffect = eff, atypeRange = (conv, rng)}) =
      (hd [], eff, conv, rng)

-- | Given parameters and a return type, construct a function type
packFunT :: SourcePos -> [ABinder' () Rec] -> EffectType Rec
         -> PassConv -> RAType -> RAType
packFunT pos params eff rng_conv rng = pack params
  where
    inf = mkSynInfo pos TypeLevel

    pack (p:ps) = AFunT inf p (Owned, pack ps)
    pack [] = ARetT inf eff (rng_conv, rng)

type AType s = ATypeOf Rec s

newtype instance ATypeOf (Subst s) (Subst s) =
  SubstAType (SubstWrapped ATypeOf)

instance Substitutable ATypeOf where
  asSubst = SubstAType
  fromSubst (SubstAType x) = x
  
  mapSubstitutable f atype =
    case atype
    of AExpT {atypeInfo = inf, atypeValue = val} ->
         AExpT inf (f val)
       AAppT {atypeInfo = inf, atypeOper = op, atypeArgs = args} ->
         AAppT inf (f op) (map (mapPassConvType f) args)
       AFunT {atypeInfo = inf, atypeMParam = param, atypeRange = rng} ->
         AFunT inf (map_binder' f param) (mapPassConvType f rng)
       ARetT {atypeInfo = inf, atypeEffect = eff, atypeRange = rng} ->
         ARetT inf (f eff) (mapPassConvType f rng)
    where
      map_binder' f (ValB' mv ty x) = ValB' mv (f ty) x
      map_binder' f (OwnB' ty x) = OwnB' (f ty) x
      map_binder' f (RefB' v ty x) = RefB' v (f ty) x
  
  applySubstitution subst atype =
    mapSubstitutable (joinSubst subst) atype

instance Renameable ATypeOf where
  freshenHead atype = withSubstitutable atype f
    where
      f ty =
        case ty
        of AExpT inf val ->
             AExpT inf `liftM` joinSubstitution val
           AAppT inf op args ->
             AAppT inf `liftM`
             joinSubstitution op `ap`
             mapM join_pass_conv_type args
           AFunT inf binder rng -> do
             (binder', rng') <- with_fresh_binder binder $
                                join_pass_conv_type rng
             return $ AFunT inf binder' rng'
           ARetT inf eff rng ->
             ARetT inf `liftM`
             joinSubstitution eff `ap`
             join_pass_conv_type rng

      join_pass_conv_type (pc, ty) = do
        ty' <- joinSubstitution ty
        return (pc, ty')

      with_fresh_binder b m =
        case b
        of ValB' mv ty x -> do
             (mv', y) <- withFreshVarMaybe mv m
             ty' <- joinSubstitution ty
             return (ValB' mv' ty' x, y)
           OwnB' ty x -> do
             y <- m
             ty' <- joinSubstitution ty
             return (OwnB' ty' x, y)
           RefB' v ty x -> do
             (v', y) <- withFreshVar v m
             ty' <- joinSubstitution ty
             return (RefB' v' ty' x, y)

withFreshVarMaybe Nothing  m = liftM ((,) Nothing) m
withFreshVarMaybe (Just v) m = do (v', x) <- withFreshVar v m
                                  return (Just v', x)

-- | Information common to values and statements
data FlatInfo =
  FlatInfo
  { finfSynInfo :: !SynInfo
    -- | The expression's result value type, computed based on the result of
    -- effect inference
  , finfType :: RAType
    -- | The expression's return parameter-passing convention
  , finfReturnConv :: PassConv
    -- | The expression's side effect, given as a list of (type, region) pairs
  , finfEffect :: EffectType Rec
  }
  deriving(Typeable)

instance HasSourcePos FlatInfo where
  getSourcePos inf = getSourcePos $ finfSynInfo inf
  setSourcePos inf p = inf {finfSynInfo = setSourcePos (finfSynInfo inf) p}

data instance ValOf Rec s =
    -- | A value variable reference
    ValV
    { valInfo :: !FlatInfo
    , valVar :: !Var
    }
    -- | An owned variable reference
  | OwnV
    { valInfo :: !FlatInfo
    , valVar :: !Var
    }
    -- | A reference variable reference
  | RefV
    { valInfo :: !FlatInfo
    , valAddr :: RecExp s
    , valPtr  :: !Var
    }
  | ConV
    { valInfo :: !FlatInfo
    , valCon :: !Con
    }
  | LitV
    { valInfo :: !FlatInfo
    , valLit :: !SystemF.Lit
    }
  | TypeV
    { valInfo :: !FlatInfo
    , valType :: RecAType s
    }
  | FunV
    { valInfo :: !FlatInfo
    , valFun :: RecFun s
    }
  | AppV
    { valInfo :: !FlatInfo
    , valOper :: RecVal s
    , valArgs :: [RecVal s]
    }
    -- | A computation inside a stream
  | StreamV
    { valInfo :: !FlatInfo
    , valPassConv :: RecVal s
    , valBody :: RecStm s
    }

type Val s = ValOf Rec s

instance HasSourcePos (ValOf Rec a) where
  getSourcePos v = getSourcePos $ valInfo v
  setSourcePos v p = v {valInfo = setSourcePos (valInfo v) p}

data instance StmOf Rec s =
    ReturnS
    { stmInfo :: !FlatInfo
    , stmValue :: RecVal s
    }
  | DoS
    { stmInfo :: !FlatInfo
    , stmValue :: RecVal s
    }
  | LetS
    { stmInfo :: !FlatInfo
    , stmBinder :: !(ABinder () s)
    , stmRhs :: RecStm s
    , stmBody :: RecStm s
    }
  | EvalS
    { stmInfo :: !FlatInfo
    , stmRhs :: RecStm s
    , stmBody :: RecStm s
    }
  | LetrecS
    { stmInfo :: !FlatInfo
    , stmDefs :: [Def s]
    , stmBody :: RecStm s
    }
  | CaseS
    { stmInfo :: !FlatInfo
    , stmScrutinee :: RecVal s
    , stmAlts :: [RecAlt s]
    }

instance HasSourcePos (StmOf Rec a) where
  getSourcePos v = getSourcePos $ stmInfo v
  setSourcePos v p = v {stmInfo = setSourcePos (stmInfo v) p}

data instance AltOf Rec s =
  Alt
  { faltInfo :: !FlatInfo
  , faltConstructor :: !Con
  , faltTyArgs :: [Val s]
  , faltParams :: [ABinder () s]
  , faltBody :: Stm s
  }

type Alt s = AltOf Rec s

type Stm s = StmOf Rec s
    
data instance FunOf Rec s =
  Fun
  { ffunInfo :: SynInfo
  , ffunParams :: [ABinder () s]
  , ffunReturnConv :: PassConv
  , ffunReturnType :: RecAType s
  , ffunEffect :: RecAType s
  , ffunBody :: RecStm s
  }
  
type Fun s = FunOf Rec s

data Def s = Def Var (Fun s) deriving(Typeable)

-------------------------------------------------------------------------------
-- Pretty-printing

pprPassConvType :: PassConvType Rec -> Doc
pprPassConvType (pc, ty) =
  parens $ sep [pprPassConv pc, pprAType ty]

pprBinder' :: ABinder' () Rec -> Doc
pprBinder' (ValB' mv ty ()) =
  let ty_doc = pprAType ty
      v_doc = maybe (text "_") pprVar mv
  in parens $ text "val" <+> v_doc <+> text ":" <+> ty_doc 

pprBinder' (OwnB' ty ()) =
  let ty_doc = pprAType ty
      v_doc = text "_"
  in parens $ text "own" <+> text ":" <+> ty_doc 

pprBinder' (RefB' rgn ty ()) =
  let ty_doc = pprAType ty
      v_doc = text "_"
      rgn_doc = pprVar rgn
  in parens $ text "ref" <+> v_doc <> text "@" <> rgn_doc <+> text ":" <+> ty_doc 

pprBinder :: ABinder () Rec -> Doc
pprBinder (ValB v ty ()) =
  let ty_doc = pprAType ty
      v_doc = pprVar v
  in parens $ text "val" <+> v_doc <+> text ":" <+> ty_doc 

pprBinder (OwnB v ty ()) =
  let ty_doc = pprAType ty
      v_doc = pprVar v
  in parens $ text "own" <+> v_doc <+> text ":" <+> ty_doc 

pprBinder (RefB rgn v ty ()) =
  let ty_doc = pprAType ty
      v_doc = pprVar v
      rgn_doc = pprVar rgn
  in parens $ text "ref" <+> v_doc <> text "@" <> rgn_doc <+> text ":" <+> ty_doc 

-- Render each component of a function type.  Return a list of parameters
-- and the return value.
pprATypeArrows :: PassConv -> RAType -> [Doc]
pprATypeArrows pc expr =
  case expr
  of AFunT {atypeMParam = param, atypeRange = (rng_pc, rng)} ->
       pprBinder' param : pprATypeArrows rng_pc rng
     _ ->
       [pprPassConv pc <+> pprAType expr]

pprAType :: RAType -> Doc
pprAType expr =
  case expr
  of AExpT {atypeValue = e} -> pprExp e
     {-AOwnedT {atypeType = ty} -> text "own" <+> pprAType ty
     ABorrowedT {atypeType = ty} -> text "bor" <+> pprAType ty-}
     AAppT {atypeOper = op, atypeArgs = args} ->
       parens $ sep (pprExp op : map pprPassConvType args)
     AFunT {} ->
       let elements = pprATypeArrows Owned expr
       in sep (map (<+> text "->") (init elements) ++ [last elements])
     {-ALamT {atypeParam = param, atypeBody = body} ->
       hang (text "\\" <> pprBinder param <+> text ".") 4 $
       pprPassConvType body-}
     ARetT {atypeEffect = eff, atypeRange = rng} ->
       text "ret" <+> parens (pprAType eff) <+> pprPassConvType rng

pprVal :: RVal -> Doc
pprVal val =
  case val
  of ValV {valVar = v} -> text "var" <+> pprVar v
     OwnV {valVar = v} -> text "own" <+> pprVar v
     RefV {valAddr = a, valPtr = v} ->
       text "ref" <+> pprVar v <> text "@" <> pprExp a
     ConV {valCon = c} -> text "con" <+> text (showLabel $ conName c)
     LitV {valLit = l} -> SystemF.pprLit l 
     TypeV {valType = t} -> pprAType t
     FunV {valFun = f} -> pprFun f
     AppV {valOper = op, valArgs = args} ->
       sep (parens (pprVal op) : map (parens . pprVal) args)
     StreamV {valBody = body} ->
       text "stream" <+> parens (pprStm body)

pprStm :: RStm -> Doc
pprStm stm =
  case stm
  of ReturnS {stmValue = v} -> text "return" <+> pprVal v
     DoS {stmValue = v} -> pprVal v 
     LetS {stmBinder = b, stmRhs = r, stmBody = body} ->
       hang (pprBinder b <+> text "=") 4 (pprStm r) $$ pprStm body
     EvalS {stmRhs = r, stmBody = body} ->
       pprStm r $$ pprStm body
     LetrecS {stmDefs = defs, stmBody = body} ->
       text "letrec" $$ nest 2 (vcat $ map pprDef defs) $$ pprStm body
     CaseS {stmScrutinee = scr, stmAlts = alts} ->
       text "case" <+> pprVal scr $$
       text "of" <+> vcat (map pprAlt alts)

pprAlt alt =
  let con_doc = text $ showLabel $ conName $ faltConstructor alt
      args_doc = map pprVal $ faltTyArgs alt
      params_doc = map pprBinder $ faltParams alt
      body_doc = pprStm $ faltBody alt
  in hang (con_doc <+> sep (args_doc ++ params_doc) <> text ".") 4 body_doc

pprFun :: RecFun Rec -> Doc
pprFun f =
  let return_doc = pprPassConvType $
                   passConvType (ffunReturnConv f) (ffunReturnType f)
      params_doc = map pprBinder (ffunParams f)
      body_doc = pprStm $ ffunBody f
  in hang (text "lambda" <+> sep (params_doc ++ [nest (-3) $ text "->" <+> return_doc]) <> text ".") 4 body_doc

pprDef (Def v f) = hang (pprVar v <+> text "=") 4 (pprFun f)

-------------------------------------------------------------------------------

newtype EffEnv a = EffEnv {runEffEnv :: ReaderT Env IO a}
                 deriving(Monad, MonadIO)

data Env = Env { -- | Each region variable is mapped to a Gluon variable.
                 --   Also, each region holds a value of known type. 
                 regionEnv :: Map.Map RVar (Var, RAType)
               , effectEnv :: Map.Map EVar Var
               , varSupply :: {-# UNPACK #-}!(IdentSupply Var)
               }

instance Supplies EffEnv (Ident Var) where
  fresh = EffEnv $ ReaderT $ \env -> supplyValue $ varSupply env

withNewRegionVariable :: RVar -> RAType -> (Var -> EffEnv a) -> EffEnv a
withNewRegionVariable region_var region_ty f = assertRVar region_var $ do
  var <- newVar (effectVarName region_var) ObjectLevel
  EffEnv $ local (insert_var var) $ runEffEnv (f var)
  where
    insert_var var env =
      env {regionEnv = Map.insert region_var (var, region_ty) $ regionEnv env}

-- | If the region variable has not been mapped to a variable, then map it
-- using 'withNewRegionVariable'; otherwise, do nothing.
withRegionVariable :: RVar -> RAType -> EffEnv a -> EffEnv a
withRegionVariable region_var region_ty m = assertRVar region_var $ EffEnv $ do
  defined <- asks check_for_definition
  runEffEnv $ if defined
              then m
              else withNewRegionVariable region_var region_ty $ \_ -> m
  where
    check_for_definition env = region_var `Map.member` regionEnv env

withNewEffectVariable :: EVar -> (Var -> EffEnv a) -> EffEnv a
withNewEffectVariable effect_var f = assertEVar effect_var $ do
  var <- newVar (effectVarName effect_var) ObjectLevel
  EffEnv $ local (insert_var var) $ runEffEnv (f var)
  where
    insert_var var env =
      env {effectEnv = Map.insert effect_var var $ effectEnv env}

convertRegion :: RVar -> EffEnv Var
convertRegion rv = assertRVar rv $ EffEnv $ asks $ \env ->
  case Map.lookup rv $ regionEnv env
  of Just (v, _) -> v
     Nothing -> internalError "convertRegion: No region"

convertEffect :: Effect -> EffEnv (EffectType Rec)
convertEffect eff = do
  -- Get the variables mentioned by the effect
  effect_vars <- liftIO $ fromEffect eff

  -- Convert to a conjunction of region and effect variables.
  -- Look up each variable, then build a conjunction expression.
  env <- EffEnv ask
  
  let lookup v =
        if isRVar v
        then case Map.lookup v $ regionEnv env
             of Just (v, ty) -> readEffectType ty (mkInternalVarE v)
                Nothing -> internalError $ "convertEffect: No region variable " ++ show (pprEffectVar v)
        else case Map.lookup v $ effectEnv env
             of Just v -> aExpT $ mkInternalVarE v
                Nothing -> internalError $ "convertEffect: No effect variable " ++ show (pprEffectVar v)
  
  let effect = foldr sconjEffectType emptyEffectType $ map lookup effect_vars
  
  return effect

convertPassType :: PassTypeAssignment -> RExp -> EffEnv (PassConvType Rec)
convertPassType (MonoAss pt) sf_type = convertMonoPassType pt sf_type

convertPassType (PolyAss (PolyPassType eff_vars pt)) sf_type = do
  withMany withNewEffectVariable eff_vars $ \eff_vars' -> do
    mono_type <- convertMonoPassType pt sf_type
    return $ foldr add_effect_param mono_type eff_vars'
  where
    add_effect_param ev rng =
      (Owned, AFunT { atypeInfo = expInfo sf_type
                    , atypeMParam = ValB' (Just ev) effect_type ()
                    , atypeRange = rng
                    })

    effect_type = aExpT effectKindE

-- | Given a type produced by effect inference and the corresponding
-- original System F type, construct an ANF type.
convertMonoPassType :: PassType -> RExp -> EffEnv (PassConvType Rec)
convertMonoPassType pass_type sf_type =
  case pass_type
  of AtomT pc ty -> liftM (passConvType pc) $ convertEType ty sf_type
     FunT param pass_rng ->
       case sf_type
       of FunE {expMParam = binder, expRange = sf_rng} -> do
            convertPassTypeParam param binder $ \anf_binder -> do
              anf_rng <- convertMonoPassType pass_rng sf_rng
              
              return (Owned, AFunT { atypeInfo = expInfo sf_type
                                   , atypeMParam = anf_binder
                                   , atypeRange = anf_rng
                                   })
          _ -> internalError "convertMonoPassType"
     RetT eff pass_rng -> do
       anf_eff <- convertEffect eff
       anf_rng <- convertMonoPassType pass_rng sf_type
       return (Borrowed, ARetT { atypeInfo = expInfo sf_type
                               , atypeEffect = anf_eff
                               , atypeRange = anf_rng
                               })

convertPassTypeParam param (Binder' mv dom ()) k = do
  (dom_pc, dom_ty) <- convertMonoPassType (paramType param) dom

  case dom_pc of
    ByValue -> k $ ValB' mv dom_ty ()
    Owned -> k $ OwnB' dom_ty ()
    Borrowed ->
      -- Create a new region variable for the parameter's region
      case paramRegion param
      of Just rv -> withNewRegionVariable rv dom_ty $ \rv' ->
           k $ RefB' rv' dom_ty ()
         Nothing -> internalError "convertPassTypeParam"

convertEType :: EType -> RExp -> EffEnv RAType
convertEType etype sf_type =
  case etype
  of AppT op args ->
       case sf_type
       of AppE {expOper = sf_op, expArgs = sf_args}
            | length args /= length sf_args -> mismatch
            | otherwise -> do
                -- The type operator remains unchanged
                let anf_op = sf_op

                -- Convert type arguments
                anf_args <- zipWithM convertEType args sf_args

                -- Type arguments are not mangled
                return $ AAppT { atypeInfo = expInfo sf_type
                               , atypeOper = anf_op
                               , atypeArgs = map (passConvType ByValue) anf_args
                               }
     
     StreamT eff pass_rng ->
       case sf_type
       of AppE { expInfo = app_info
               , expOper = ConE {expInfo = stream_info, expCon = stream_con}
               , expArgs = args}
            | stream_con `isPyonBuiltin` the_Stream -> do
                -- This constructor takes one argument
                let arg = case args
                          of [arg] -> arg
                             _ -> mismatch

                -- Convert it to an effect-decorated stream type
                anf_eff <- convertEffect eff
                anf_rng <- convertEType pass_rng arg
                let output_type = passConvType Borrowed anf_rng
                return $ stream_type app_info stream_info anf_eff output_type
            
          _ -> mismatch

     VarT v ->
       case sf_type
       of VarE {} -> return_sf_type
          _ -> mismatch
     ConstT e -> return_sf_type
     TypeT -> return_sf_type
  where
    -- Inconsistency found between effect inference and System F types 
    mismatch = internalError "convertEType"
    
    -- Return the System F type unchanged
    return_sf_type = return $ AExpT { atypeInfo = expInfo sf_type
                                    , atypeValue = sf_type
                                    }
                     
    -- Build a stream type
    stream_type app_info op_info eff rng =
      let con = pyonBuiltin the_LazyStream
          op = mkConE (getSourcePos op_info) con
      in AAppT app_info op [passConvType ByValue eff, rng]

convertType :: Effect.ExpOf Effect.EI Effect.EI -> RAType
convertType ty =
  let ty1 = Effect.fromEIType ty
  in AExpT (expInfo ty1) ty1

-------------------------------------------------------------------------------

type StmContext = RStm -> RStm

type ContextVal = (StmContext, RVal)
type ContextStm = (StmContext, RStm)

idContext :: StmContext
idContext = id

genDoStatement :: RVal -> EffEnv RStm
genDoStatement val =
  -- Create a 'do' statement to execute this value
  let (effect, result_conv, result_type) =
        case finfType $ valInfo val
        of ARetT { atypeEffect = eff
                 , atypeRange = (pc, ty)} -> (eff, pc, ty)
           _ -> internalError "genDoStatement"
      eval_info = FlatInfo { finfSynInfo = finfSynInfo $ valInfo val
                           , finfType = result_type
                           , finfReturnConv = result_conv
                           , finfEffect = effect}
      eval_stm = DoS { stmInfo = eval_info
                     , stmValue = val}
  in return eval_stm
  
-- | Given a value, generate code to bind the value to a new temporary variable
-- using the specified parameter-passing convention.  The value must be a
-- runnable ('ARetT') value.
genLetStatement :: RStm -> EffEnv ContextVal
genLetStatement stm = do
  let result_conv = finfReturnConv $ stmInfo stm
  let result_type = finfType $ stmInfo stm

  -- Create a binder for the new temporary value 
  binder <- make_binder result_conv result_type
  
  -- Create a 'let' statement to bind the result
  -- FIXME: What about the body's effect? 
  -- Where do we mask the effect of using the binder?
  let letstm body =
        let pos = getSourcePos $ finfSynInfo $ stmInfo body
            info = (stmInfo body) {finfSynInfo = mkSynInfo pos ObjectLevel}
        in LetS { stmInfo = info
                , stmBinder = binder
                , stmRhs = stm
                , stmBody = body}
      
  return (letstm, abinderValue (getSourcePos stm) binder)
  where
    make_binder conv ty = do
      bound_var <- newAnonymousVariable ObjectLevel
      case conv
        of ByValue  -> return $ ValB bound_var ty ()
           Owned    -> return $ OwnB bound_var ty ()
           Borrowed -> do rgn <- newAnonymousVariable ObjectLevel
                          return $ RefB rgn bound_var ty ()
           _ -> internalError "genDoStatement"

-- | Generate a 'do' or 'return' statement around this value to get the result.
forceValue :: RVal -> EffEnv RStm
forceValue val =
  let given_type = finfType $ valInfo val
      given_conv = finfReturnConv $ valInfo val
  in case given_type
     of ARetT {atypeRange = (range_conv, range)} -> genDoStatement val
        _ -> return $ ReturnS (valInfo val) val

-- | Generate a 'do' or 'return' statement around this value to get the result.
forceValueVal :: RVal -> EffEnv ContextVal
forceValueVal val =
  let given_type = finfType $ valInfo val
      given_conv = finfReturnConv $ valInfo val
  in case given_type
     of ARetT {atypeRange = (range_conv, range)} -> genLetStatement =<< genDoStatement val
        _ -> return (idContext, val)

-- | Convert a value to match the given type and passing convention.
coerceValue :: RAType     -- ^ Target type
            -> PassConv   -- ^ Target passing convention
            -> RVal       -- ^ Value to coerce
            -> EffEnv ContextVal
coerceValue expect_type expect_conv val = do
  let given_type = finfType $ valInfo val
      given_conv = finfReturnConv $ valInfo val
  coercion <- coerceByPassType expect_type expect_conv given_type given_conv
  case coercion of
    Nothing -> return (idContext, val)
    Just f  -> f val

-- | Convert a value to match the given type and passing convention.
-- If the value already has the right type and convention, Nothing is
-- returned.  Otherwise, code that performs the conversion is returned,
-- along with the new value.
--
-- During coercion, we assume that the original System F data types
-- always match, and the only differences are those that arise due to
-- effect inference.  Specifically, any @ExpOf Rec@ types are assumed
-- to match, and type variables are assumed to match.
-- Parameter-passing conventions may not match, and side effects may 
-- need to be inserted or removed by lambda-abstracting or evaluating,
-- respectively.

-- The most common coercions are to evaluate 'Ret' types and to box or
-- unbox values.
-- Sometimes these coercions need to be performed on functions.  If so,
-- a lambda expression is created.
coerceByPassType :: RAType      -- ^ Expected type
                 -> PassConv    -- ^ Expected parameter-passing convention
                 -> RAType      -- ^ Given type
                 -> PassConv    -- ^ Given parameter-passing convention
                 -> EffEnv (Maybe (RVal -> EffEnv ContextVal))
coerceByPassType expect_type expect_conv given_type given_conv =
  case (expect_type, given_type)
  of (_, ARetT {atypeRange = (given_range_conv, given_range)}) -> 
       return $ Just $ \val -> do
         -- Evaluate the given expression; bind it to a temporary variable
         (ctx, new_val) <- genLetStatement =<< genDoStatement val
       
         -- Coerce the result
         (ctx', new_val') <-
           from_coercion new_val =<<
           coerceByPassType expect_type expect_conv
                            given_range given_range_conv
                          
         return (ctx . ctx', new_val')

     (ARetT {}, _) -> not_implemented
     (AFunT {}, AFunT {}) -> coerceFunctionType expect_type given_type
     (_, AFunT {}) -> not_implemented
     -- (_, ALamT {}) -> not_implemented
     (AFunT {}, _) -> not_implemented
     -- (ALamT {}, _) -> not_implemented
     
     -- AExpT or AAppT
     _ | expect_conv == given_conv -> id_coercion
       | otherwise -> not_implemented
  where
    id_coercion = return Nothing
    from_coercion v Nothing = return (idContext, v)
    from_coercion v (Just f) = f v
    not_implemented = internalError $ "coerceByPassType: not implemented\n" ++ show (nest 4 $ pprAType expect_type <> semi $$ pprAType given_type)

coerceFunctionType expect_type given_type =
  case unpackFunT expect_type
  of (expect_params, expect_eff, expect_conv, expect_rt) ->
       case unpackFunT given_type
       of (given_params, given_eff, given_conv, given_rt) ->
            if length expect_params /= length given_params
            then -- This is possible due to curring (one of the functions
                 -- returns a function).  We really should handle it properly.
                 internalError "coerceFunctionType: Parameter length mismatch"
            else coerce_function
                 expect_params expect_eff expect_conv expect_rt
                 given_params given_eff given_conv given_rt
  where
    coerce_function
      expect_params expect_eff expect_conv expect_rt
      given_params given_eff given_conv given_rt = do
        -- Coerce parameters from expected type to given type
        (s1, s2, lambda_binders, param_coercions) <-
          coerce_binders mempty mempty expect_params given_params

        let expect_rt' = substFully $ joinSubst s1 $ verbatim expect_rt
        -- Coerce the return value from given type to expected type
        return_coercion <-
          coerceByPassType expect_rt expect_conv given_rt given_conv

        -- If no coercions are required, then return Nothing
        if isNothing return_coercion && all isNothing param_coercions
          then return Nothing
          else internalError "coerceFunctionType: Not implemented"

    coerce_binders s1 s2 (b1 : bs1) (b2 : bs2) = do
      let b1' = substituteBinder' s1 b1
          b2' = substituteBinder' s2 b2
      (s1', s2', lambda_b, coercion) <- coerceBinder b1' b2'
      let s1'' = s1 `mappend` s1'
      let s2'' = s2 `mappend` s2'
          
      -- Recursive part
      (s1''', s2''', lambda_bs, coercions) <-
        coerce_binders s1'' s2'' bs1 bs2
      return (s1''', s2''', lambda_b : lambda_bs, coercion : coercions)

    coerce_binders s1 s2 [] [] = return (s1, s2, [], [])

-- | Create a coercion to convert a value of a given passing convention to 
-- a value of an expected passing convention.
--
-- Return substitution to apply to the first expression, substitution to apply
-- to the second expression, a value binder equivalent of the given
-- variable, and a coercion to the expected variable.
coerceBinder :: ABinder' () Rec -- ^ Expected binder
             -> ABinder' () Rec -- ^ Given binder
             -> EffEnv (Substitution,
                        Substitution,
                        ABinder () Rec,
                        Maybe (RVal -> EffEnv ContextVal))
coerceBinder expect_binder given_binder =
  -- In each branch, do the following.
  -- 1. Rename bound variables
  -- 2. Create a coercion for the value that the binder binds
  -- 3. Create a binder that may be used in a lambda expression  
  case (expect_binder, given_binder)
  of (ValB' expect_mv expect_ty (),
      ValB' given_mv given_ty ()) -> do
       (mv', subst1, subst2) <- renameMaybeVar given_mv expect_mv
       coercion <- coerceByPassType expect_ty ByValue given_ty ByValue

       v <- newAnonymousVariable (pred $ getLevel given_ty)
       let binder = ValB v given_ty ()
           
       return (subst1, subst2, binder, coercion)

     (OwnB' expect_ty (),
      OwnB' given_ty ()) -> do
       coercion <- coerceByPassType expect_ty Owned given_ty Owned

       v <- newAnonymousVariable (pred $ getLevel given_ty)
       let binder = OwnB v given_ty ()
           
       return (mempty, mempty, binder, coercion)
     
     (RefB' expect_v expect_ty (),
      RefB' given_v given_ty ()) -> do
       (v', subst1, subst2) <- renameVar given_v expect_v
       coercion <- coerceByPassType expect_ty Borrowed given_ty Borrowed

       ptr_v <- newAnonymousVariable (pred $ getLevel given_ty)
       let binder = RefB v' ptr_v given_ty ()
       return (subst1, subst2, binder, coercion)

renameVar :: Var -> Var -> EffEnv (Var, Substitution, Substitution)
renameVar v1 v2 = do
  new_v <- newVar (varName v1) (getLevel v1)
  return (new_v, renaming v1 new_v, renaming v2 new_v)

renameMaybeVar :: Maybe Var
               -> Maybe Var 
               -> EffEnv (Maybe Var, Substitution, Substitution)
renameMaybeVar Nothing Nothing = return (Nothing, mempty, mempty)
renameMaybeVar mv1 mv2 = do
  let old_var = fromJust $ mv1 `mplus` mv2
  new_v <- newVar (varName old_var) (getLevel old_var)
  
  -- Substitute for the old variables
  let rn Nothing  = mempty
      rn (Just old_v) = renaming old_v new_v
  return (Just new_v, rn mv1, rn mv2)

convertBinder :: Effect.EIBinder -> (ABinder () Rec -> EffEnv a) -> EffEnv a
convertBinder (Binder v ty (rgn, pass_type)) k = do
  (conv, ty') <- convertMonoPassType pass_type (Effect.fromEIType ty)
  case conv of
    ByValue  -> k $ ValB v ty' ()
    Owned    -> k $ OwnB v ty' ()
    Borrowed ->
      case rgn
      of Just rv -> withNewRegionVariable rv ty' $ \rv' -> k $ RefB rv' v ty' ()
         Nothing -> internalError "convertBinder"

-- | Create a 'FlatInfo' data structure for a flattened expression.
effectInferredInfo :: Effect.EIExp -> EffEnv FlatInfo
effectInferredInfo expr = do
  (new_conv, new_type) <-
    convertPassType (Effect.eiReturnType expr) (Effect.eiType expr)
  makeEffectInfo expr new_conv new_type

makeEffectInfo :: Effect.EIExp -> PassConv -> RAType -> EffEnv FlatInfo
makeEffectInfo expr pc ty = do
  effect <- convertEffect $ Effect.eiEffect expr
  return $ FlatInfo { finfSynInfo = Effect.expInfo $ Effect.eiExp expr
                    , finfType = ty
                    , finfReturnConv = pc
                    , finfEffect = effect
                    }

-- | Create information for an expression.  Use the same return type and
-- passing convention as the given info.
makeEffectInfoFrom :: Effect.EIExp -> FlatInfo -> EffEnv FlatInfo
makeEffectInfoFrom expr source_info =
  makeEffectInfo expr (finfReturnConv source_info) (finfType source_info)

-- | Convert an effect to the corresponding type
effectValue :: SourcePos -> Effect -> EffEnv RVal
effectValue pos eff = do
  ty <- convertEffect eff
  let info = FlatInfo { finfSynInfo = mkSynInfo pos TypeLevel
                      , finfType = AExpT (internalSynInfo KindLevel) $
                                   effectKindE
                      , finfReturnConv = ByValue
                      , finfEffect = emptyEffectType
                      }
  return $ TypeV info ty

-- | Set up to flatten an expression.
--
-- If the expression creates a new return region, the return region is
-- mapped to a new variable (if it hasn't been mapped already). 

{-
-- Rather than handle the extra bookkeeping to find the appropriate  
-- place to translate a region, we check whether it's been translated yet. 
-- The 'let' and 'letrec' expressions are the problematic cases, since they
-- use whatever return region 
setupToFlattenExp :: Effect.EIExp
                  -> EffEnv a
                  -> EffEnv a
setupToFlattenExp expression k =
  if Effect.expReturnsNewValue expression 
  then case Effect.eiRegion expression
       of Nothing -> k
          Just v  -> withRegionVariable v k
     else k
-}
-- | Flatten an expression as a statement that returns a value.
flattenExpAsStm :: Effect.EIExp -> EffEnv (StmContext, RStm)
flattenExpAsStm expression =
  case Effect.eiExp expression of
    Effect.LetE { Effect.expBinder = b
                , Effect.expValue = val
                , Effect.expBody = body} ->
      flattenLet expression b val body
    Effect.LetrecE {Effect.expDefs = defs, Effect.expBody = body} ->
      flattenLetrec expression defs body
    Effect.CaseE {Effect.expScrutinee = scr, Effect.expAlternatives = alts} ->
      flattenCase expression scr alts
    _ -> do
      (ctx, val) <- flattenExpAsVal expression
      val' <- forceValue val
      return (ctx, val')

-- | Flatten a value or owned expression.
flattenExpAsVal :: Effect.EIExp -> EffEnv (StmContext, RVal)
flattenExpAsVal expression =
  case Effect.eiExp expression
  of Effect.VarE {Effect.expVar = v} ->
       flattenVarExp expression v
     Effect.ConE {Effect.expCon = c} -> do 
       inf <- effectInferredInfo expression
       return_value $ ConV inf c
     Effect.LitE {Effect.expLit = l} -> do
       inf <- effectInferredInfo expression
       return_value $ LitV inf l
     Effect.TypeE {Effect.expTypeValue = ty} -> do
       inf <- effectInferredInfo expression
       return_value $ TypeV inf $ convertType ty
     Effect.InstanceE { Effect.expOper = op
                      , Effect.expEffectArgs = effects} ->
       flattenInstanceExp expression op effects
     Effect.RecPlaceholderE { Effect.expVar = v
                            , Effect.expPlaceholderValue = ph_val} ->
       internalError "Not implemented: flattening recursive placeholders"
     Effect.CallE {Effect.expOper = op, Effect.expArgs = args} ->
       flattenCall expression op args
     Effect.FunE {Effect.expFun = f} -> do
       inf <- effectInferredInfo expression
       f' <- flattenFun f
       return (idContext, FunV inf f')
     Effect.DoE { Effect.expTyArg = ty
                , Effect.expPassConv = pc
                , Effect.expBody = body} ->
       flattenDo expression ty pc body
     _ -> do (ctx, stm) <- flattenExpAsStm expression
             (ctx', val) <- genLetStatement stm
             return (ctx . ctx', val)
  where
    return_value val = return (idContext, val)

flattenVarExp expression v = do
  inf <- effectInferredInfo expression
    
  -- Dispatch based on the convention
  case finfReturnConv inf of
    ByValue  -> return (idContext, ValV inf v)
    Owned    -> return (idContext, OwnV inf v)
    Borrowed -> do
      -- Get the variable's region, which is the same as the expression's
      -- region.
      rv <- convertRegion $ case Effect.eiRegion expression
                            of Just rv -> rv
                               Nothing -> internalError "flattenExpAsVal"
      return (idContext, RefV inf (mkVarE (getSourcePos expression) rv) v)

    
-- Flatten an effect instantiation expression.
-- The result is an application term.
flattenInstanceExp expression op effects = do
  (op_context, op_val) <- flattenExpAsVal op
  effect_vals <- mapM (effectValue $ getSourcePos expression) effects

  -- Get the effect information for this instance of the operator
  inf <- effectInferredInfo expression
  return (op_context, AppV inf op_val effect_vals)

flattenCall :: Effect.EIExp -> Effect.EIExp -> [Effect.EIExp]
            -> EffEnv (StmContext, RVal)
flattenCall call_expression op args = do
  -- Flatten operator
  (op_context, op_val) <- flattenExpAsVal op

  -- Flatten arguments and create call expression
  (call_context, call_val) <- flatten_and_make_call op_val args
  return (op_context . call_context, call_val)
  where
    -- Take the flattened operator and flatten the arguments, generating one
    -- or more function call expressions
    flatten_and_make_call op_val args = do
      -- Flatten operands
      let fun_type = finfType $ valInfo op_val  
      (oprd_context, oprd_vals, return_type, return_conv, excess_args) <-
        flatten_operands fun_type undefined_pc args

      -- Create call expression
      inf <- makeEffectInfo call_expression return_conv return_type
      let val = AppV inf op_val oprd_vals

      -- If there are no more arguments, then return the call expression
      if null excess_args
        then return (oprd_context, val)
        else do 
        -- Produce a value from the first call (it will be a function value)
        (call_context, call_val) <- genLetStatement =<< forceValue val

        -- Make another call expression for the remaining arguments
        (sub_context, call_val') <- flatten_and_make_call call_val excess_args
    
        return (oprd_context . call_context . sub_context, call_val')

    -- Flatten operands to a function call.
    -- Return context, the flattened operands, the return type,
    -- the return passing convention, and unused arguments.
    flatten_operands :: RAType         -- ^ Operator type
                     -> PassConv       -- ^ Operator passing convention (if
                                       -- there are no more arguments, this
                                       -- is the return passing convention)
                     -> [Effect.EIExp] -- ^ Arguments, not yet flattened
                     -> EffEnv (StmContext, [RVal], RAType, PassConv, [Effect.EIExp])
    flatten_operands op_type op_conv args =
      case op_type
      of AFunT {atypeMParam = binder, atypeRange = (pc, rng)} ->
           case args
           of arg : args' -> do
                -- Flatten operand and add it to the App term
                (context, arg_val) <-
                  flattenCallOperand (abinder'Type binder) (abinder'PassConv binder) arg
                (context2, arg_vals, return_type, return_conv, excess_args) <-
                  flatten_operands rng pc args'
                return (context . context2,
                        arg_val : arg_vals,
                        return_type,
                        return_conv,
                        excess_args)
              [] ->
                -- Under-saturated application
                return (idContext, [], op_type, op_conv, [])
                
         ARetT {} ->
           -- Saturated application
           return (idContext, [], op_type, op_conv, args)

         _ ->
           internalError "flattenCall: Unexpected function type"
    
    -- Should be ignored: function calls will have at least one argument 
    undefined_pc = internalError "flattenCall"
    
flattenCallOperand :: RAType -> PassConv -> Effect.EIExp 
                   -> EffEnv (StmContext, RVal)
flattenCallOperand expect_type expect_conv arg = do
  let arg_region = Effect.eiRegion arg
      
  -- Flatten the argument
  (arg_context, arg_val) <- flattenExpAsVal arg
  
  -- Coerce it to the expected type
  (arg_context2, arg_val') <- coerceValue expect_type expect_conv arg_val
  return (arg_context . arg_context2, arg_val')

flattenDo expression ty pc body = do
  -- Convert operands
  (pc_context, pc_val) <- flattenExpAsVal pc
  (body_context, body_stm) <- flattenExpAsStm body
  
  -- Create call expression
  inf <- effectInferredInfo expression
  let val = StreamV inf pc_val body_stm
  return (pc_context . body_context, val)

flattenLet expression binder rhs body = do
  (rhs_context, rhs') <- flattenExpAsStm rhs
  convertBinder binder $ \binder' -> do
    (body_context, body') <- flattenExpAsStm body
    inf <- makeEffectInfoFrom expression (stmInfo body')
    let expr = LetS inf binder' rhs' body'

    -- Wrap the new 'let' expression with the RHS's context  
    return (body_context, rhs_context expr)

flattenLetrec expression defs body = do
  defs' <- mapM flattenDef defs
  (body_context, body') <- flattenExpAsStm body
  inf <- makeEffectInfoFrom expression (stmInfo body')
  let expr = LetrecS inf defs' body'
  return (body_context, expr)

flattenFun :: Effect.FunOf Effect.EI Effect.EI -> EffEnv (Fun Rec)
flattenFun fun =
  -- Add effect parameters to the environment
  assume_effects (Effect.funEffectParams fun) $ \effect_vars ->

  -- Convert binders and add parameter regions to environment
  withMany convertBinder (Effect.funParams fun) $ \binders -> do
    (body_context, body_stm) <- flattenExpAsStm $ Effect.funBody fun
    let body = body_context body_stm
    effect <- convertEffect $ Effect.funEffect fun
    (return_conv, return_type) <- convertMonoPassType
                   (Effect.funReturnPassType fun)
                   (Effect.fromEIType $ Effect.funReturnType fun)

    let effect_params = [ValB v effect_type () | v <- effect_vars]
          where effect_type = AExpT (internalSynInfo KindLevel) effectKindE
        
    let new_fun = Fun { ffunInfo = Effect.funInfo fun
                      , ffunParams = effect_params ++ binders
                      , ffunReturnConv = return_conv
                      , ffunReturnType = return_type
                      , ffunEffect = effect
                      , ffunBody = body
                      }
    return new_fun
  where
    assume_effects = withMany withNewEffectVariable

flattenCase :: Effect.EIExp 
            -> Effect.EIExp 
            -> [Effect.AltOf Effect.EI Effect.EI]
            -> EffEnv (StmContext, RStm)
flattenCase expression scr alts = do
  -- Flatten the scrutinee
  (scr_context, scr_val) <- flattenExpAsVal scr
  (scr_context', scr_val') <- forceValueVal scr_val
  let eff = finfEffect $ valInfo scr_val'
      
  -- Flatten alternatives
  alts' <- mapM (flattenAlt (getSourcePos expression) eff) alts
  inf <- makeEffectInfoFrom expression (faltInfo $ head alts')
  let stm = CaseS { stmInfo = inf
                  , stmScrutinee = scr_val'
                  , stmAlts = alts'
                  }
  return (scr_context . scr_context', stm)

flattenAlt :: SourcePos -> EffectType Rec -> Effect.AltOf Effect.EI Effect.EI 
           -> EffEnv RAlt
flattenAlt pos eff alt = do
  let ty_arg_info = FlatInfo { finfSynInfo = mkSynInfo pos TypeLevel
                             , finfType = AExpT (internalSynInfo KindLevel) pureKindE
                             , finfReturnConv = ByValue
                             , finfEffect = emptyEffectType
                             }
  let ty_args = map (TypeV ty_arg_info) $
                map convertType $
                Effect.eialtTyArgs alt
  withMany convertBinder (Effect.eialtParams alt) $ \params -> do
    (body_ctx, body_stm) <- flattenExpAsStm $ Effect.eialtBody alt
  
    let body = body_ctx body_stm
    let inf = FlatInfo { finfSynInfo = mkSynInfo pos ObjectLevel 
                       , finfType = finfType $ stmInfo body
                       , finfReturnConv = finfReturnConv $ stmInfo body
                       , finfEffect = eff
                       }
    return $ Alt { faltInfo = inf
                 , faltConstructor = Effect.eialtConstructor alt
                 , faltTyArgs = ty_args
                 , faltParams = params
                 , faltBody = body
                 }

flattenDef :: Effect.Def Effect.EI -> EffEnv (Def Rec)
flattenDef (Effect.Def v f) = do
  f' <- flattenFun f
  return $ Def v f'

flattenDefGroup = mapM flattenDef

flattenModule :: [[Effect.Def Effect.EI]] -> EffEnv [[Def Rec]]
flattenModule defss = mapM flattenDefGroup defss

flatten :: SystemF.Module SystemF.TypedRec -> IO [[Def Rec]]
flatten mod = do
  -- Run effect inference
  effect_defss <- Effect.runEffectInference mod
  
  -- Run flattening
  flattened <-
    withTheVarIdentSupply $ \var_supply ->
    let env = Env Map.empty Map.empty var_supply
    in runReaderT (runEffEnv $ flattenModule effect_defss) env

  -- DEBUG: print flattened code
  putStrLn "Flattened"
  print $ vcat $ concat $ map (map pprDef) flattened
  
  return flattened
