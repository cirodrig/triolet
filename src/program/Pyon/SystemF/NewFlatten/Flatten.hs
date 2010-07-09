{-| Expression flattening prior to ANF generation.
--
-- This module uses the result of effect inference to generate code that is
-- in the form required for ANF generation.  Effect variables are converted  
-- to type parameters.  However, the code is not converted to state-passing
-- form here: pass-by-reference variables are not expanded, and state
-- variables are not created.
-}

{-# LANGUAGE TypeFamilies, FlexibleInstances, EmptyDataDecls,
    ScopedTypeVariables, GeneralizedNewtypeDeriving, DeriveDataTypeable, 
    ViewPatterns #-}
module Pyon.SystemF.NewFlatten.Flatten(flatten)
where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.ST
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
import Gluon.Common.MonadLogic
import Gluon.Core
import Gluon.Core.RenameBase
import Pyon.Globals
import qualified Pyon.SystemF.Syntax as SystemF
import qualified Pyon.SystemF.Print as SystemF
import qualified Pyon.SystemF.Typecheck as SystemF
import Pyon.SystemF.Builtins
import Pyon.SystemF.NewFlatten.PassConv
import qualified Pyon.SystemF.NewFlatten.SetupEffect as Effect

-- | Set to true to print types in output
showTypes :: Bool
showTypes = False

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
data ABinder' s =
    -- | Bind a value
    ValB' !(Maybe Var) (RecAType s)
    -- | Bind an owned reference
  | OwnB' (RecAType s)
    -- | Bind a reference to data of the given type, at the given region
  | RefB' !Var (RecAType s)
  deriving(Typeable)

abinder'Region :: ABinder' s -> Maybe Var
abinder'Region (ValB' {}) = Nothing
abinder'Region (OwnB' {}) = Nothing
abinder'Region (RefB' rgn _) = Just rgn

abinder'Type :: ABinder' s -> RecAType s
abinder'Type (ValB' _ ty) = ty
abinder'Type (OwnB' ty) = ty
abinder'Type (RefB' _ ty) = ty

abinder'PassConv :: ABinder' s -> PassConv
abinder'PassConv (ValB' _ _) = ByValue
abinder'PassConv (OwnB' _) = Owned
abinder'PassConv (RefB' _ _) = Borrowed

data ABinder s =
    -- | Bind a value
    ValB !Var (RecAType s)
    -- | Bind an owned reference
  | OwnB !Var (RecAType s)
    -- | Borrow a reference to an object at an unknown address.
    -- Never used in 'let' expressions.
  | RefB !Var !Var (RecAType s)
    -- | Allocate a temporary local variable.  Only used in 'let' expressions.
  | LocalB !Var !Var (RecAType s)
    -- | Borrow a reference to an object at a known address.
  | BorB !(RecExp s) !Var (RecAType s)
  deriving(Typeable)

abinderRegion :: ABinder s -> Maybe Var
abinderRegion (ValB {}) = Nothing
abinderRegion (OwnB {}) = Nothing
abinderRegion (RefB rgn _ _) = Just rgn

abinderType :: ABinder s -> RecAType s
abinderType (ValB _ ty) = ty
abinderType (OwnB _ ty) = ty
abinderType (RefB _ _ ty) = ty

abinderPassConv :: ABinder s -> PassConv
abinderPassConv (ValB _ _) = ByValue
abinderPassConv (OwnB _ _) = Owned
abinderPassConv (RefB _ _ _) = Borrowed

abinderValue :: SourcePos -> ABinder Rec -> RVal
abinderValue pos b =
  case b
  of ValB v ty ->
       let info = mkSynInfo pos (getLevel v)
       in ValV info v
     OwnB v ty ->
       let info = mkSynInfo pos ObjectLevel
       in OwnV info v
     RefB rgn v ty ->
       let info = mkSynInfo pos ObjectLevel
       in RefV info (mkVarE pos rgn) v
     LocalB rgn v ty ->
       let info = mkSynInfo pos ObjectLevel
       in RefV info (mkVarE pos rgn) v
     BorB rgn v ty ->
       let info = mkSynInfo pos ObjectLevel
       in RefV info rgn v
       
substFullyBinder' :: ABinder' SubstRec -> ABinder' Rec
substFullyBinder' (ValB' mv ty) = ValB' mv (substFully ty)
substFullyBinder' (OwnB' ty) = OwnB' (substFully ty)
substFullyBinder' (RefB' v ty) = RefB' v (substFully ty)

substituteBinder' :: Substitution -> ABinder' Rec -> ABinder' Rec
substituteBinder' subst abinder =
  case abinder
  of ValB' mv ty -> ValB' mv (substitute_type ty)
     OwnB' ty -> OwnB' (substitute_type ty)
     RefB' v ty -> RefB' v (substitute_type ty)
  where
    substitute_type ty = substFully $ joinSubst subst $ verbatim ty

type PassConvType s = (PassConv, RecAType s)

passConvType :: PassConv -> RecAType s -> PassConvType s
passConvType = (,)

mapPassConvType :: (RecAType s -> RecAType t)
                -> PassConvType s -> PassConvType t
mapPassConvType f (pc, t) = (pc, f t)

-- | A function or stream return type.
data AReturn' s =
    ValR' (RecAType s)
  | OwnR' (RecAType s)
    -- | Return a reference to an address provided by the caller
  | RefR' !Var (RecAType s)
    -- | Return a reference to an address fixed by the callee
  | BorR' !(RecExp s) (RecAType s)

areturn'Region :: AReturn' s -> Maybe Var
areturn'Region (ValR' _) = Nothing
areturn'Region (OwnR' _) = Nothing
areturn'Region (RefR' v _) = Just v

areturn'PassConv :: AReturn' s -> PassConv
areturn'PassConv (ValR' {}) = ByValue
areturn'PassConv (OwnR' {}) = Owned
areturn'PassConv (RefR' {}) = Borrowed
areturn'PassConv (BorR' {}) = Borrowed

areturn'Type :: AReturn' s -> RecAType s
areturn'Type (ValR' t) = t
areturn'Type (OwnR' t) = t
areturn'Type (RefR' _ t) = t
areturn'Type (BorR' _ t) = t

-- | A function return binder.
data AReturn s =
    ValR (RecAType s)
  | OwnR (RecAType s)
    -- | Return into a given address and pointer variable
  | RefR !Var !Var (RecAType s)

areturnPassConv :: AReturn s -> PassConv
areturnPassConv (ValR {}) = ByValue
areturnPassConv (OwnR {}) = Owned
areturnPassConv (RefR {}) = Borrowed

areturnType :: AReturn s -> RecAType s
areturnType (ValR t) = t
areturnType (OwnR t) = t
areturnType (RefR _ _ t) = t

-- | An ANF type.  This is really an encoding of a more complex Gluon type.
data instance ATypeOf Rec s =
    AExpT
    { atypeInfo  :: {-# UNPACK #-} !SynInfo 
    , atypeValue :: RecExp s
    }
  | AAppT
    { atypeInfo :: {-# UNPACK #-} !SynInfo 
    , atypeOper :: RecExp s
    , atypeArgs :: [PassConvType s]
    }
  | AFunT
    { atypeInfo :: {-# UNPACK #-} !SynInfo 
    , atypeMParam :: ABinder' s
    , atypeRange :: PassConvType s
    }
  | ARetT
    { atypeInfo :: {-# UNPACK #-} !SynInfo 
    , atypeEffect :: EffectType s
    , atypeReturn :: AReturn' s
    }

instance HasLevel (ATypeOf Rec s) where
  getLevel ty = getLevel $ atypeInfo ty
  setLevel ty l = ty {atypeInfo = setLevel (atypeInfo ty) l}

aExpT :: RExp -> RAType
aExpT ty =
  let level = getLevel ty
      pos = getSourcePos ty
  in AExpT (mkSynInfo pos level) ty
     
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
         AFunT inf (map_binder' param) (mapPassConvType f rng)
       ARetT {atypeInfo = inf, atypeEffect = eff, atypeReturn = ret} ->
         ARetT inf (f eff) (map_return' ret)
    where
      map_binder' (ValB' mv ty) = ValB' mv (f ty)
      map_binder' (OwnB' ty) = OwnB' (f ty)
      map_binder' (RefB' v ty) = RefB' v (f ty)
      
      map_return' (ValR' ty) = ValR' (f ty)
      map_return' (OwnR' ty) = OwnR' (f ty)
      map_return' (RefR' v ty) = RefR' v (f ty)
  
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
             freshen_return rng

      join_pass_conv_type (pc, ty) = do
        ty' <- joinSubstitution ty
        return (pc, ty')
      
      freshen_return (ValR' ty) = ValR' `liftM` joinSubstitution ty
      freshen_return (OwnR' ty) = OwnR' `liftM` joinSubstitution ty
      freshen_return (RefR' v ty) = do 
        (v', ty') <- withFreshVar v $ joinSubstitution ty
        return $ RefR' v' ty'

      with_fresh_binder b m =
        case b
        of ValB' mv ty -> do
             (mv', y) <- withFreshVarMaybe mv m
             ty' <- joinSubstitution ty
             return (ValB' mv' ty', y)
           OwnB' ty -> do
             y <- m
             ty' <- joinSubstitution ty
             return (OwnB' ty', y)
           RefB' v ty -> do
             (v', y) <- withFreshVar v m
             ty' <- joinSubstitution ty
             return (RefB' v' ty', y)

withFreshVarMaybe Nothing  m = liftM ((,) Nothing) m
withFreshVarMaybe (Just v) m = do (v', x) <- withFreshVar v m
                                  return (Just v', x)

data instance ValOf Rec s =
    -- | A value variable reference
    ValV
    { valInfo :: !SynInfo
    , valVar :: !Var
    }
    -- | An owned variable reference
  | OwnV
    { valInfo :: !SynInfo
    , valVar :: !Var
    }
    -- | A reference variable reference
  | RefV
    { valInfo :: !SynInfo
    , valAddr :: RecExp s
    , valPtr  :: !Var
    }
  | ConV
    { valInfo :: !SynInfo
    , valCon :: !Con
    }
  | LitV
    { valInfo :: !SynInfo
    , valLit :: !SystemF.Lit
    }
  | TypeV
    { valInfo :: !SynInfo
    , valType :: RecAType s
    }
  | FunV
    { valInfo :: !SynInfo
    , valFun :: RecFun s
    }
  | AppV
    { valInfo :: !SynInfo
    , valOper :: RecVal s
    , valArgs :: [RecVal s]
    }
    -- | A computation inside a stream
  | StreamV
    { valInfo :: !SynInfo
    , valPassConv :: RecVal s
    , valBody :: RecStm s
    }

type Val s = ValOf Rec s

instance HasSourcePos (ValOf Rec a) where
  getSourcePos v = getSourcePos $ valInfo v
  setSourcePos v p = v {valInfo = setSourcePos (valInfo v) p}

newtype instance ValOf (Subst s) (Subst s) = SubstVal (SubstWrapped ValOf)

instance Substitutable ValOf where
  asSubst = SubstVal
  fromSubst (SubstVal x) = x
  
  mapSubstitutable f value =
    case value
    of ValV inf v -> ValV inf v
       OwnV inf v -> OwnV inf v
       RefV inf addr v -> RefV inf (f addr) v
       ConV inf c -> ConV inf c
       LitV inf l -> LitV inf l
       TypeV inf t -> TypeV inf (f t)
       FunV inf fun -> FunV inf (f fun)
       AppV inf op args -> AppV inf (f op) (map f args)
       StreamV inf pc body -> StreamV inf (f pc) (f body)

  applySubstitution subst value =
    case value
    of ValV info v ->
         case get_replacement info v
         of Nothing -> value
            Just v' -> ValV info v'
       OwnV info v ->
         case get_replacement info v
         of Nothing -> value
            Just v' -> OwnV info v'
       RefV info addr v ->
         let v' = fromMaybe v $ get_replacement info v
         in RefV info (joinSubst subst addr) v'
       _ -> mapSubstitutable (joinSubst subst) value
    where
      get_replacement info v =
        case lookupVar v subst
        of Nothing -> Nothing
           Just _  -> Just $! case lookupVarExp info v subst
                              of VarE {expVar = v'} -> v'
                                 _ -> internalError "ValOf.applySubstitution"

data instance StmOf Rec s =
    ReturnS
    { stmInfo :: !SynInfo
    , stmValue :: RecVal s
    }
  | DoS
    { stmInfo :: !SynInfo
    , stmValue :: RecVal s
    }
  | LetS
    { stmInfo :: !SynInfo
    , stmBinder :: !(ABinder s)
    , stmRhs :: RecStm s
    , stmBody :: RecStm s
    }
    -- | Store a value into a borrowed memory area
  | StoreS
    { stmInfo :: !SynInfo
    , stmValue :: RecVal s
    , stmDestination :: RecVal s
    }
  | EvalS
    { stmInfo :: !SynInfo
    , stmRhs :: RecStm s
    , stmBody :: RecStm s
    }
  | LetrecS
    { stmInfo :: !SynInfo
    , stmDefs :: [Def s]
    , stmBody :: RecStm s
    }
  | CaseS
    { stmInfo :: !SynInfo
    , stmScrutinee :: RecVal s
    , stmAlts :: [RecAlt s]
    }

instance HasSourcePos (StmOf Rec a) where
  getSourcePos v = getSourcePos $ stmInfo v
  setSourcePos v p = v {stmInfo = setSourcePos (stmInfo v) p}

newtype instance StmOf (Subst s) (Subst s) = SubstStm (SubstWrapped StmOf)

instance Substitutable StmOf where
  asSubst s = SubstStm s
  fromSubst (SubstStm s) = s
  
  mapSubstitutable f stm =
    case stm
    of ReturnS info val -> ReturnS info (f val)
       DoS info val -> DoS info (f val)
       LetS info binder rhs body ->
         LetS info (map_binder binder) (f rhs) (f body)
       StoreS info val dst ->
         StoreS info (f val) (f dst)
       LetrecS info defs body ->
         LetrecS info [Def v (f fun) | Def v fun <- defs] (f body)
       CaseS info scr alts ->
         CaseS info (f scr) (map f alts)
    where
      map_binder (ValB v ty) = ValB v (f ty)
      map_binder (OwnB v ty) = OwnB v (f ty)
      map_binder (RefB v ptr ty) = RefB v ptr (f ty)
      map_binder (LocalB v ptr ty) = LocalB v ptr (f ty)
      map_binder (BorB addr ptr ty) = BorB (f addr) ptr (f ty)

  applySubstitution subst stm = mapSubstitutable (joinSubst subst) stm

data instance AltOf Rec s =
  Alt
  { faltInfo :: !SynInfo
  , faltConstructor :: !Con
  , faltTyArgs :: [RecVal s]
  , faltParams :: [ABinder s]
  , faltBody :: RecStm s
  }

type Alt s = AltOf Rec s

newtype instance AltOf (Subst s) (Subst s) = SubstAlt (SubstWrapped AltOf)

instance Substitutable AltOf where
  asSubst a = SubstAlt a
  fromSubst (SubstAlt a) = a
  
  mapSubstitutable f (Alt inf con args params body) =
    Alt inf con (map f args) (map map_binder params) (f body)
    where
      map_binder (ValB v ty) = ValB v (f ty)
      map_binder (OwnB v ty) = OwnB v (f ty)
      map_binder (RefB v ptr ty) = RefB v ptr (f ty)
      map_binder (LocalB v ptr ty) = LocalB v ptr (f ty)
      map_binder (BorB addr ptr ty) = BorB (f addr) ptr (f ty)

  applySubstitution subst alt = mapSubstitutable (joinSubst subst) alt

type Stm s = StmOf Rec s
    
data instance FunOf Rec s =
  Fun
  { ffunInfo :: SynInfo
  , ffunParams :: [ABinder s]
  , ffunReturn :: AReturn s
  , ffunEffect :: RecAType s
  , ffunBody :: RecStm s
  }
  
type Fun s = FunOf Rec s

newtype instance FunOf (Subst s) (Subst s) = SubstFun (SubstWrapped FunOf)

instance Substitutable FunOf where
  asSubst f = SubstFun f
  fromSubst (SubstFun f) = f
  
  mapSubstitutable f fun =
    Fun { ffunInfo = ffunInfo fun
        , ffunParams = map map_binder $ ffunParams fun
        , ffunReturn = map_return $ ffunReturn fun
        , ffunEffect = f $ ffunEffect fun
        , ffunBody = f $ ffunBody fun
        }
    where
      map_binder (ValB v ty) = ValB v (f ty)
      map_binder (OwnB v ty) = OwnB v (f ty)
      map_binder (RefB v ptr ty) = RefB v ptr (f ty)
  
      map_return (ValR ty) = ValR (f ty)
      map_return (OwnR ty) = OwnR (f ty)
      map_return (RefR v p ty) = RefR v p (f ty)

  applySubstitution subst fun = mapSubstitutable (joinSubst subst) fun

data Def s = Def Var (RecFun s) deriving(Typeable)

-------------------------------------------------------------------------------
-- Pretty-printing

pprPassConvType :: PassConvType Rec -> Doc
pprPassConvType (pc, ty) =
  parens $ sep [pprPassConv pc, pprAType ty]
  
pprTypeAnn ty
  | showTypes = text ":" <+> pprAType ty
  | otherwise = empty

pprType ty
  | showTypes = pprAType ty
  | otherwise = empty

pprBinder' :: ABinder' Rec -> Doc
pprBinder' (ValB' mv ty) =
  let v_doc = maybe (text "_") pprVar mv
  in parens $ text "val" <+> v_doc <+> pprTypeAnn ty

pprBinder' (OwnB' ty) =
  parens $ text "own" <+> text "_" <+> pprTypeAnn ty

pprBinder' (RefB' rgn ty) =
  let v_doc = text "_"
      rgn_doc = pprVar rgn
  in parens $ text "ref" <+> v_doc <> text "@" <> rgn_doc <+> pprTypeAnn ty

pprBinder :: ABinder Rec -> Doc
pprBinder (ValB v ty) =
  let v_doc = pprVar v
  in parens $ text "val" <+> v_doc <+> pprTypeAnn ty

pprBinder (OwnB v ty) =
  let v_doc = pprVar v
  in parens $ text "own" <+> v_doc <+> pprTypeAnn ty

pprBinder (RefB rgn v ty) =
  let v_doc = pprVar v
      rgn_doc = pprVar rgn
  in parens $ text "ref" <+> v_doc <> text "@" <> rgn_doc <+> pprTypeAnn ty

pprBinder (LocalB rgn v ty) =
  let v_doc = pprVar v
      rgn_doc = pprVar rgn
  in parens $ text "lcl" <+> v_doc <> text "@" <> rgn_doc <+> pprTypeAnn ty

pprBinder (BorB rgn v ty) =
  let v_doc = pprVar v
      rgn_doc = pprExp rgn
  in parens $ text "bor" <+> v_doc <> text "@" <> rgn_doc <+> pprTypeAnn ty

pprAReturn' :: AReturn' Rec -> Doc
pprAReturn' (ValR' ty) = text "val" <+> pprType ty
pprAReturn' (OwnR' ty) = text "own" <+> pprType ty
pprAReturn' (RefR' v ty) = text "ref" <> parens (pprVar v) <+> pprType ty
pprAReturn' (BorR' a ty) = text "bor" <> parens (pprExp a) <+> pprType ty

pprAReturn :: AReturn Rec -> Doc
pprAReturn (ValR ty) = text "val" <+> pprType ty
pprAReturn (OwnR ty) = text "own" <+> pprType ty
pprAReturn (RefR v p ty) = text "bor" <> parens (pprVar v <> text "," <+> pprVar p) <+> pprType ty

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
     ARetT {atypeEffect = eff, atypeReturn = ret} ->
       text "ret" <+> parens (pprAType eff) <+> pprAReturn' ret

pprMVal :: RVal -> Maybe Doc
pprMVal (TypeV {}) = Nothing
pprMVal x = Just $ pprVal x

pprMVals :: [RVal] -> [Doc]
pprMVals = mapMaybe pprMVal

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
       let args_doc = if showTypes
                      then map (parens . pprVal) args
                      else map parens $ pprMVals args
       in hang (parens (pprVal op)) 4 $ sep args_doc
     StreamV {valBody = body} ->
       text "stream" <+> parens (pprStm body)

pprStm :: RStm -> Doc
pprStm stm =
  case stm
  of ReturnS {stmValue = v} -> text "return" <+> pprVal v
     DoS {stmValue = v} -> pprVal v 
     LetS {stmBinder = b, stmRhs = r, stmBody = body} ->
       hang (pprBinder b <+> text "=") 4 (pprStm r) $$ pprStm body
     StoreS {stmValue = v, stmDestination = dst} ->
       text "store" <> parens (pprVal dst) <+> pprVal v
     EvalS {stmRhs = r, stmBody = body} ->
       pprStm r $$ pprStm body
     LetrecS {stmDefs = defs, stmBody = body} ->
       text "letrec" $$ nest 2 (vcat $ map pprDef defs) $$ pprStm body
     CaseS {stmScrutinee = scr, stmAlts = alts} ->
       text "case" <+> pprVal scr $$
       text "of" <+> vcat (map pprAlt alts)

pprAlt alt =
  let con_doc = text $ showLabel $ conName $ faltConstructor alt
      args_doc = if showTypes
                 then map pprVal $ faltTyArgs alt
                 else []
      params_doc = map pprBinder $ faltParams alt
      body_doc = pprStm $ faltBody alt
  in hang (con_doc <+> sep (args_doc ++ params_doc) <> text ".") 4 body_doc

pprFun :: RecFun Rec -> Doc
pprFun f =
  let return_doc = pprAReturn $ ffunReturn f
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
  supplyToST f = EffEnv $ ReaderT $ \env -> stToIO (f (unsafeIOToST $ supplyValue $ varSupply env))

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

-- | Create a return value binder for the given expression.  The return region
-- (if there is one) is a new region.
createNewReturn :: PassConv -> RAType -> EffEnv (AReturn Rec)
createNewReturn pc ty = do
  -- If needed, create a new variable representing the return address
  rgn <- if pc == Borrowed
         then liftM Just $ newAnonymousVariable ObjectLevel
         else return Nothing
  createReturn rgn pc ty

-- | Create a return value binder for the given expression.
createReturn :: Maybe Var -> PassConv -> RAType -> EffEnv (AReturn Rec)
createReturn mrgn pc ty =
  case (pc, mrgn)
  of (ByValue,  Nothing) -> return $ ValR ty
     (Owned,    Nothing) -> return $ OwnR ty
     (Borrowed, Just rv) -> do
       ptr_v <- newAnonymousVariable ObjectLevel
       return $ RefR rv ptr_v ty

-- | Create a return type for the given expression.  The return region
-- (if there is one) is a new region.
createNewReturn' :: PassConv -> RAType -> EffEnv (AReturn' Rec)
createNewReturn' pc ty = do
  -- If needed, create a new variable representing the return address
  rgn <- if pc == Borrowed
         then liftM Just $ newAnonymousVariable ObjectLevel
         else return Nothing
  createReturn' rgn pc ty

-- | Create a return type for the given expression.
createReturn' :: Maybe Var -> PassConv -> RAType -> EffEnv (AReturn' Rec)
createReturn' mrgn pc ty =
  return $! case (pc, mrgn)
            of (ByValue,  Nothing) -> ValR' ty
               (Owned,    Nothing) -> OwnR' ty
               (Borrowed, Just rv) -> RefR' rv ty

convertPassType :: PassTypeAssignment -> RExp -> EffEnv (PassConvType Rec)
convertPassType (MonoAss pt) sf_type = convertMonoPassType pt sf_type

convertPassType (PolyAss (PolyPassType eff_vars pt)) sf_type = do
  withMany withNewEffectVariable eff_vars $ \eff_vars' -> do
    mono_type <- convertMonoPassType pt sf_type
    return $ foldr add_effect_param mono_type eff_vars'
  where
    add_effect_param ev rng =
      (Owned, AFunT { atypeInfo = expInfo sf_type
                    , atypeMParam = ValB' (Just ev) effect_type
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
       anf_ret <-
         case anf_rng
         of (ByValue,  ty) -> return $ ValR' ty
            (Owned,    ty) -> return $ OwnR' ty
            (Borrowed, ty) -> do addr_v <- newAnonymousVariable ObjectLevel
                                 return $ RefR' addr_v ty
       return (Borrowed, ARetT { atypeInfo = expInfo sf_type
                               , atypeEffect = anf_eff
                               , atypeReturn = anf_ret
                               })

convertPassTypeParam param (Binder' mv dom ()) k = do
  (dom_pc, dom_ty) <- convertMonoPassType (paramType param) dom

  case dom_pc of
    ByValue -> k $ ValB' mv dom_ty
    Owned -> k $ OwnB' dom_ty
    Borrowed ->
      -- Create a new region variable for the parameter's region
      case paramRegion param
      of Just rv -> withNewRegionVariable rv dom_ty $ \rv' ->
           k $ RefB' rv' dom_ty
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

newtype StmContext = StmContext (Maybe (RStm -> RStm))

stmContext f = StmContext (Just f)
idContext = StmContext Nothing

isIdContext (StmContext Nothing) = True
isIdContext (StmContext (Just _)) = False

instance Monoid StmContext where
  mempty = idContext
  mappend (StmContext Nothing) x = x
  mappend x (StmContext Nothing) = x
  mappend (StmContext (Just x)) (StmContext (Just y)) =
    StmContext (Just (x . y))

applyContext (StmContext Nothing) x = x
applyContext (StmContext (Just f)) x = f x

data Flattened a =
  Flattened
  { flattenedThing :: a
    -- | The flattened term's return information
  , flattenedReturn :: !(AReturn' Rec)
    -- | Iff returning a reference, this is the return pointer.
    -- Else Nothing.
  , flattenedReturnPtr :: !(Maybe Var)
  }

flattened :: String -> a -> AReturn' Rec -> Maybe Var -> Flattened a
flattened msg thing ret ptr = check_arguments $ Flattened thing ret ptr
  where
    check_arguments =
      case areturn'Type ret
      of ARetT {atypeReturn = ret'} -> check ret'
         _ -> check ret
      
    check ret =
      case ret
      of ValR' {} | isNothing ptr -> ok
         OwnR' {} | isNothing ptr -> ok
         RefR' {} | isJust ptr -> ok
                  | otherwise -> internalError $ msg ++ ": Expecting return pointer"
         BorR' {} | isNothing ptr -> ok
         _ -> internalError $ msg ++ ": Unexpected return pointer"
    ok = id

type FlattenedVal = Flattened RVal

flattenedVal :: Flattened RVal -> RVal
flattenedVal = flattenedThing

type FlattenedStm = Flattened RStm

flattenedStm :: Flattened RStm -> RStm
flattenedStm = flattenedThing

flattenedType :: Flattened a -> RAType
flattenedType x = areturn'Type $ flattenedReturn x

flattenedConv :: Flattened a -> PassConv
flattenedConv x = areturn'PassConv $ flattenedReturn x

type ContextVal = (StmContext, FlattenedVal)
type ContextStm = (StmContext, FlattenedStm)

genDoStatement :: FlattenedVal -> FlattenedStm
genDoStatement val =
  -- Create a 'do' statement to execute this value
  let return_binder =
        case flattenedType val
        of ARetT {atypeReturn = ret} -> ret
           _ -> internalError "genDoStatement"
      eval_info = mkSynInfo (getSourcePos $ flattenedVal val) ObjectLevel
      eval_stm = DoS { stmInfo = eval_info
                     , stmValue = flattenedVal val}
  in flattened "genDoStatement" eval_stm return_binder (flattenedReturnPtr val)
  
-- | Generate code to bind a statement's return value to a new temporary
-- variable.  The statement must have a runnable ('ARetT') type.
genLetStatement :: FlattenedStm -> EffEnv ContextVal
genLetStatement fstm = do
  -- Create a binder for the new temporary value
  binder <- make_binder
  
  -- Create a 'let' statement to bind the result
  let letstm body =
        let pos = getSourcePos $ stmInfo body
            info = mkSynInfo pos ObjectLevel
        in LetS { stmInfo = info
                , stmBinder = binder
                , stmRhs = flattenedStm fstm
                , stmBody = body}
  
  let pos = getSourcePos $ flattenedStm fstm
      
      return_binder =
        case binder
        of ValB _ ty -> ValR' ty
           OwnB _ ty -> OwnR' ty
           LocalB addr _ ty -> 
             -- Return a borrowed reference to this local variable
             BorR' (mkInternalVarE addr) ty
           BorB addr _ ty -> BorR' addr ty
  return (stmContext letstm,
          flattened "genLetStatement" (abinderValue pos binder) return_binder Nothing)
  where
    make_binder =
      case flattenedReturn fstm
      of ValR' ty -> do
           bound_var <- newAnonymousVariable ObjectLevel
           return $ ValB bound_var ty
         OwnR' ty -> do
           bound_var <- newAnonymousVariable ObjectLevel
           return $ OwnB bound_var ty
         RefR' addr ty -> do
           bound_ptr <- newAnonymousVariable ObjectLevel
           return $ LocalB addr bound_ptr ty
         BorR' addr ty -> do
           bound_ptr <- newAnonymousVariable ObjectLevel
           return $ BorB addr bound_ptr ty

genStoreStatement :: AReturn Rec -> FlattenedVal -> ContextStm
genStoreStatement ret val =
  case ret
  of RefR addr ptr ty ->
       let ret = BorR' (mkInternalVarE addr) ty

           pos = getSourcePos $ flattenedVal val
           dst = RefV (mkSynInfo pos ObjectLevel) (mkInternalVarE addr) ptr
           stm =
             StoreS { stmInfo = mkSynInfo pos ObjectLevel
                    , stmValue = flattenedVal val
                    , stmDestination = dst
                    }
       in (idContext, flattened "genStoreStatement" stm ret Nothing)

-- | Convert the value to a statement by putting it in a 'do' or 'return'
-- statement.
forceValue :: FlattenedVal -> EffEnv FlattenedStm
forceValue val =
  case flattenedType val
  of ARetT {} -> return $ genDoStatement val
     _ -> let v = flattenedVal val
          in return $ flattened "forceValue" (ReturnS (valInfo v) v) (flattenedReturn val) (flattenedReturnPtr val)

-- | Generate a 'do' or 'return' statement around this value to get the result.
forceValueVal :: FlattenedVal -> EffEnv ContextVal
forceValueVal val =
  case flattenedType val
  of ARetT {} -> genLetStatement $ genDoStatement val
     _ -> return (idContext, val)

renameReturnRegionForCoerce :: AReturn Rec -> FlattenedVal
                            -> EffEnv (StmContext, RVal)
renameReturnRegionForCoerce binder val =
  case binder 
  of ValR {} -> return (idContext, flattenedVal val)
     OwnR {} -> return (idContext, flattenedVal val)
     RefR addr ptr ty -> rename_region addr ptr ty
  where
    old_ptr = case flattenedReturnPtr val of Just p -> p

    rename_region rgn ptr ty =
      case flattenedReturn val
      of RefR' old_rgn _ ->
           let renamed_val = substFully $ rename old_rgn rgn $
                             rename old_ptr ptr $
                             verbatim $ flattenedVal val
            in return (idContext, renamed_val)
         BorR' old_addr _ ->
           case old_addr
           of VarE {expVar = v} | v == rgn ->
                return (idContext, flattenedVal val) -- No change required
              _ -> do
                -- Copy into to a temporary let-bound variable
                let copy = makeCopyStatement ty val rgn ptr
                let letstm body =
                      let info = internalSynInfo ObjectLevel
                      in LetS { stmInfo = info   
                              , stmBinder = LocalB rgn ptr ty
                              , stmRhs = copy
                              , stmBody = body
                              }
                    val = RefV (internalSynInfo ObjectLevel) (mkInternalVarE rgn) ptr
                return (stmContext letstm, val)

renameReturnRegion :: ABinder Rec -> FlattenedStm -> EffEnv RStm
renameReturnRegion binder stm =
  case binder
  of ValB {} -> return $ flattenedStm stm
     OwnB {} -> return $ flattenedStm stm
     LocalB a p ty -> rename_region a p ty
     RefB a p ty -> rename_region a p ty
  where
    rename_region rgn ptr ty =
      case flattenedReturn stm
      of RefR' old_rgn _ ->
           let old_ptr = case flattenedReturnPtr stm of Just p -> p
               renamed_stm = substFully $ rename old_rgn rgn $
                             rename old_ptr ptr $
                             verbatim $ flattenedStm stm
           in return renamed_stm
         BorR' old_addr _ -> do
           -- Assign the return pointer to a temporary variable, then 
           -- copy to destination
           (ctx, val) <- genLetStatement stm
           copy <- return $ makeCopyStatement ty val rgn ptr
           return $ applyContext ctx copy

makeCopyStatement ty src dst_rgn dst_ptr =
  let oper = ConV (internalSynInfo ObjectLevel) $
             pyonBuiltin the_fun_copy
      params = [ TypeV (internalSynInfo TypeLevel) ty
               , flattenedVal src
               , RefV (internalSynInfo ObjectLevel) (mkInternalVarE dst_rgn) dst_ptr]
      info = internalSynInfo ObjectLevel
  in DoS info $ AppV info oper params

-- | Convert a value to match the given type and passing convention.
-- FIXME: Insert code to copy the return value, when needed. 
coerceValue :: AReturn Rec -- ^ Target type and passing convention
            -> FlattenedVal
            -> EffEnv ContextVal
coerceValue expect_return val = do
  coercion <-
    coerceValPassType expect_return (flattenedType val) (flattenedConv val) (flattenedReturnPtr val)
  case coercion of
    Nothing -> return (idContext, val)
    Just f  -> f val

-- | Convert a statement to match the given type and passing convention.
-- FIXME: Insert code to copy the return value, when needed. 
coerceStm :: AReturn Rec       -- ^ Target type and passing convention
          -> FlattenedStm       -- ^ Statement to coerce
          -> EffEnv ContextStm
coerceStm expect_return stm = do
  coercion <-
    traceShow (text "coerceStm" <+> pprAReturn' (flattenedReturn stm)) $ coerceStmPassType expect_return (flattenedType stm) (flattenedConv stm) (flattenedReturnPtr stm)
  case coercion of
    Nothing -> return (idContext, stm)
    Just f  -> f stm

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
coerceValPassType :: AReturn Rec -- ^ Expected type and passing convention
                  -> RAType      -- ^ Given type
                  -> PassConv    -- ^ Given passing convention
                  -> Maybe Var   -- ^ Given return pointer
                  -> EffEnv (Maybe (FlattenedVal -> EffEnv ContextVal))
coerceValPassType expect_return given_type given_conv given_ptr =
  case (areturnType expect_return, given_type)
  of (_, ARetT {atypeReturn = given_range}) -> 
       return $ Just $ \fval -> do
         -- Evaluate the given expression; bind it to a temporary variable
         (ctx, new_fval) <- genLetStatement $ genDoStatement fval
       
         -- Coerce the result
         (ctx', new_val') <- coerceValue expect_return new_fval
         return (ctx `mappend` ctx', new_val')

     (ARetT {}, _) -> not_implemented
     (et@(AFunT {}), gt@(AFunT {})) -> coerceFunctionType et gt
     (_, AFunT {}) -> not_implemented
     -- (_, ALamT {}) -> not_implemented
     (AFunT {}, _) -> not_implemented
     -- (ALamT {}, _) -> not_implemented
     
     -- AExpT or AAppT
     _ | areturnPassConv expect_return == given_conv ->
           -- If pass-by-reference, do the return addresses agree?
           case expect_return
           of RefR _ ptr _ ->
                case given_ptr
                of Just ptr' | ptr == ptr' -> return Nothing
                   _ -> return $ Just $ \fval -> do
                       -- Rename the return region
                       (ctx, fval') <- renameReturnRegionForCoerce expect_return fval
                       return (ctx, flattened "coerceValPassType" fval' ty_binder (Just ptr))
              _ -> return Nothing
       | areturnPassConv expect_return == Borrowed &&
         given_conv == ByValue -> return $ Just $ \fval -> do
           (ctx, stm) <- return $ genStoreStatement expect_return fval
           (ctx', new_val) <- genLetStatement stm
           return (ctx `mappend` ctx', new_val)
       | otherwise -> not_implemented
  where
    ty_binder = 
      case expect_return
      of ValR ty -> ValR' ty
         OwnR ty -> OwnR' ty
         RefR a p ty -> RefR' a ty
    ptr =
      case expect_return
      of RefR _ p _ -> Just p
         _ -> Nothing
    not_implemented = traceShow (pprAReturn expect_return $$ pprPassConv given_conv $$ pprAType given_type) $ internalError $ "coerceValPassType: not implemented"

coerceStmPassType :: AReturn Rec -- ^ Expected type and passing convention
                  -> RAType      -- ^ Given type
                  -> PassConv    -- ^ Given passing convention
                  -> Maybe Var
                  -> EffEnv (Maybe (FlattenedStm -> EffEnv ContextStm))
coerceStmPassType expect_return given_type given_conv given_ptr =
  case (areturnType expect_return, given_type)
  of (_, ARetT {atypeReturn = given_range}) -> coerce_value
     (ARetT {}, _) -> not_implemented
     (et@(AFunT {}), gt@(AFunT {})) -> coerce_value
     (_, AFunT {}) -> not_implemented
     -- (_, ALamT {}) -> not_implemented
     (AFunT {}, _) -> not_implemented
     -- (ALamT {}, _) -> not_implemented
     
     -- AExpT or AAppT.  Assume the types match.
     _ | areturnPassConv expect_return == given_conv ->
           -- If pass-by-reference, do the return addresses agree?
           case expect_return
           of RefR _ ptr _ ->
                case given_ptr
                of Just ptr' | ptr == ptr' -> return Nothing
                   _ -> return $ Just $ \fstm -> do
                       -- Fix up the return region
                       fstm' <- renameReturnRegion ret_binder fstm
                       return (idContext, flattened "coerceStmPassType" fstm' ty_binder (Just ptr))
              _ -> return Nothing
       | areturnPassConv expect_return == Borrowed &&
         given_conv == ByValue -> return $ Just $ \fstm -> do
           (ctx, val) <- genLetStatement fstm
           (ctx', stm) <- return $ genStoreStatement expect_return val
           return (ctx `mappend` ctx', stm)
       | otherwise -> not_implemented
  where
    ret_binder =
      case expect_return
      of ValR ty -> ValB no_var ty
         OwnR ty -> OwnB no_var ty
         RefR a p ty -> RefB a p ty
      where no_var = internalError "coerceStmPassType: not a variable"
    ty_binder = 
      case expect_return
      of ValR ty -> ValR' ty
         OwnR ty -> OwnR' ty
         RefR a p ty -> RefR' a ty
    not_implemented = traceShow (pprAReturn expect_return $$ pprPassConv given_conv $$ pprAType given_type) $ internalError $ "coerceStmPassType: not implemented"

    coerce_value = do
      coercion <- coerceValPassType expect_return given_type given_conv given_ptr
      case coercion
        of Nothing -> return Nothing
           Just f  -> return $ Just $ \stm -> do
             (ctx_let, val) <- genLetStatement stm
             (ctx_f, val') <- f val
             stm' <- forceValue val'
             return (ctx_let `mappend` ctx_f, stm')

coerceFunctionType expect_type_ given_type_ =
  go (verbatim expect_type_) (verbatim given_type_) [] []
  where
    go expect_type given_type rbinders rcoercions =
      case substHead expect_type
      of AFunT {atypeMParam = e_param, atypeRange = (e_conv, e_rng)} ->
           case substHead given_type
           of AFunT {atypeMParam = g_param, atypeRange = (g_conv, g_rng)} -> do
                -- Coerce this binder
                (s1, s2, lambda_b, coercion) <-
                  coerceBinder (substFullyBinder' e_param) (substFullyBinder' g_param)
                let e_rng' = joinSubst s1 e_rng
                let g_rng' = joinSubst s1 g_rng
                
                -- Coerce other binders
                go e_rng' g_rng' (lambda_b : rbinders) (coercion : rcoercions)
              _ -> internalError "coerceFunctionType: Parameter length mismatch"
         ARetT {atypeReturn = e_ret} ->
           case substHead given_type
           of ARetT {atypeReturn = g_ret} -> do
                -- Create a temporary variable for the
                -- original function's return value
                (expect_range_binder, range_ptr) <-
                  case e_ret
                  of ValR' ty -> return (ValR $ substFully ty, Nothing)
                     OwnR' ty -> return (OwnR $ substFully ty, Nothing)
                     RefR' addr ty -> do
                       range_ptr <- newAnonymousVariable ObjectLevel
                       return (RefR addr range_ptr $ substFully ty, Just range_ptr)

                -- Coerce the return value from given type to expected type
                return_coercion <- coerceValPassType expect_range_binder
                                   (substFully $ areturn'Type g_ret)
                                   (areturn'PassConv g_ret)
                                   range_ptr
                
                -- If no coercions are required, then return Nothing
                if isNothing return_coercion && all isNothing rcoercions
                  then return Nothing
                  else traceShow (pprAType expect_type_ $$ pprAType given_type_) $ internalError "coerceFunctionType: Not implemented"

              _ -> internalError "coerceFunctionType: Parameter length mismatch"

coerceReturn :: AReturn' Rec
             -> AReturn' Rec
             -> EffEnv (AReturn Rec, Maybe (FlattenedStm -> EffEnv ContextStm))
coerceReturn expect_ret given_ret =
  case (expect_ret, given_ret)
  of (ValR' expect_ty, ValR' given_ty) ->
       coerce (ValR expect_ty) given_ty ByValue Nothing
     (OwnR' expect_ty, OwnR' given_ty) ->
       coerce (OwnR expect_ty) given_ty Owned Nothing
     (RefR' expect_addr expect_ty, RefR' given_addr given_ty) -> do
       ptr <- newAnonymousVariable ObjectLevel
       coerce (RefR expect_addr ptr expect_ty) given_ty Borrowed (Just ptr)
  where
    coerce binder given_ty conv ptr = do
      coercion <- coerceStmPassType binder given_ty conv ptr
      return (binder, coercion)

-- | Create a coercion to convert a value of a given passing convention to 
-- a value of an expected passing convention.
--
-- Return substitution to apply to the first expression, substitution to apply
-- to the second expression, a value binder equivalent of the given
-- variable, and a coercion to the expected variable.
coerceBinder :: ABinder' Rec -- ^ Expected binder
             -> ABinder' Rec -- ^ Given binder
             -> EffEnv (Substitution,
                        Substitution,
                        ABinder Rec,
                        Maybe (FlattenedVal -> EffEnv ContextVal))
coerceBinder expect_binder given_binder =
  -- In each branch, do the following.
  -- 1. Rename bound variables
  -- 2. Create a coercion for the value that the binder binds
  -- 3. Create a binder that may be used in a lambda expression  
  case (expect_binder, given_binder)
  of (ValB' expect_mv expect_ty, ValB' given_mv given_ty) -> do
       (mv', subst1, subst2) <- renameMaybeVar given_mv expect_mv
       coercion <- coerceValPassType (ValR expect_ty) given_ty ByValue Nothing

       v <- newAnonymousVariable (pred $ getLevel given_ty)
       let binder = ValB v given_ty
           
       return (subst1, subst2, binder, coercion)

     (OwnB' expect_ty, OwnB' given_ty) -> do
       coercion <- coerceValPassType (OwnR expect_ty) given_ty Owned Nothing

       v <- newAnonymousVariable (pred $ getLevel given_ty)
       let binder = OwnB v given_ty
           
       return (mempty, mempty, binder, coercion)
     
     (RefB' expect_v expect_ty, RefB' given_v given_ty) -> do
       (v', subst1, subst2) <- renameVar given_v expect_v
       ptr_v <- newAnonymousVariable (pred $ getLevel given_ty)
       coercion <- coerceValPassType (RefR expect_v ptr_v expect_ty) given_ty Borrowed (Just ptr_v)

       let binder = RefB v' ptr_v given_ty
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

-- | Convert a binder
convertBinder :: Bool
              -> Effect.EIBinder 
              -> (ABinder Rec -> EffEnv a)
              -> EffEnv a
convertBinder is_let (Binder v ty (rgn, pass_type)) k = do
  (conv, ty') <- convertMonoPassType pass_type (Effect.fromEIType ty)
  case conv of
    ByValue  -> k $ ValB v ty'
    Owned    -> k $ OwnB v ty'
    Borrowed ->
      case rgn
      of Just rv -> withNewRegionVariable rv ty' $ \rv' ->
                    k $! (if is_let then LocalB else RefB) rv' v ty'
         Nothing -> internalError "convertBinder"

-- | Determine what this expression returns based on its effect-inferred type,
-- assuming the expression creates a new return value.  The answer will not be
-- correct for other expressions.
effectReturnType :: Effect.EIExp -> EffEnv (AReturn' Rec)
effectReturnType expr = do
  (new_conv, new_type) <-
    convertPassType (Effect.eiReturnType expr) (Effect.eiType expr)
  case new_conv of
    ByValue -> return $ ValR' new_type
    Owned -> return $ OwnR' new_type
    Borrowed -> do
      addr <- newAnonymousVariable ObjectLevel
      return $ RefR' addr new_type

-- | Convert an effect to the corresponding type
effectValue :: SourcePos -> Effect -> EffEnv RVal
effectValue pos eff = do
  ty <- convertEffect eff
  let info = mkSynInfo pos TypeLevel
  return $ TypeV info ty

-- | Flatten an expression as a statement that returns a value.
flattenExpAsStm :: Effect.EIExp -- ^ Expression to flatten
                -> EffEnv ContextStm
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
flattenExpAsVal :: Effect.EIExp -- ^ Expression to flatten
                -> EffEnv ContextVal
flattenExpAsVal expression =
  case Effect.eiExp expression
  of Effect.VarE {Effect.expVar = v} ->
       flattenVarExp expression v
     Effect.ConE {Effect.expCon = c} ->
       flattenConExp expression c
     Effect.LitE {Effect.expLit = l} -> do
       -- Literals are always by-value, regardless of what effect inference
       -- says
       let pass_type = alter_literal_type $ Effect.eiReturnType expression
       (conv, ty) <- convertPassType pass_type (Effect.eiType expression)
       let rt = case conv
                of ByValue -> ValR' ty
                   _ -> internalError "flattenExpAsVal"

       let inf = mkSynInfo (getSourcePos expression) ObjectLevel
       return_value (LitV inf l) rt
     Effect.TypeE {Effect.expTypeValue = ty} -> do
       rt <- effectReturnType expression
       let inf = mkSynInfo (getSourcePos expression) TypeLevel
       return_value (TypeV inf $ convertType ty) rt
     Effect.InstanceE { Effect.expOper = op
                      , Effect.expEffectArgs = effects} ->
       flattenInstanceExp expression op effects
     Effect.RecPlaceholderE { Effect.expVar = v
                            , Effect.expPlaceholderValue = ph_val} ->
       internalError "Not implemented: flattening recursive placeholders"
     Effect.CallE {Effect.expOper = op, Effect.expArgs = args} ->
       flattenCall expression op args
     Effect.FunE {Effect.expFun = f} -> do
       rt <- effectReturnType expression
       unless (areturn'PassConv rt == Owned) $ internalError "flattenExpAsVal"
       let inf = mkSynInfo (getSourcePos expression) ObjectLevel
       f' <- flattenFun f
       return (idContext, flattened "flattenExpAsVal" (FunV inf f') rt Nothing)
     Effect.DoE { Effect.expTyArg = ty
                , Effect.expPassConv = pc
                , Effect.expBody = body} ->
       flattenDo expression ty pc body
     _ -> do (ctx, stm) <- flattenExpAsStm expression
             (ctx', val) <- genLetStatement stm
             return (ctx `mappend` ctx', val)
  where
    alter_literal_type (MonoAss (AtomT pc ty)) = MonoAss (AtomT ByValue ty)
    alter_literal_type _ = internalError "flattenExpAsVal"
    return_value val rt =
      return (idContext, flattened "flattenExpAsVal" val rt Nothing)

flattenVarExp expression v = do
  -- Get the variable's type
  (conv, ty) <- convertPassType (Effect.eiReturnType expression) (Effect.eiType expression)

  let inf = mkSynInfo (getSourcePos expression) ObjectLevel
  case conv of
    ByValue  -> return (idContext, flattened "flattenVarExp" (ValV inf v) (ValR' ty) Nothing)
    Owned    -> return (idContext, flattened "flattenVarExp" (ValV inf v) (OwnR' ty) Nothing)
    Borrowed ->
      -- Get the variable's region
      case Effect.eiRegion expression
      of Just rv -> do
           rgn <- convertRegion rv
           
           -- This is a borrowed reference to the variable
           let val = RefV inf (mkVarE (getSourcePos expression) rgn) v
           return (idContext, flattened "flattenVarExp" val (BorR' (mkInternalVarE rgn) ty) Nothing)

flattenConExp expression c = do
  rt <- effectReturnType expression
  
  -- Can't handle the borrowed return convention
  when (case rt of {BorR' {} -> True; _ -> False}) $ 
    internalError "flattenConExp"
  let inf = mkSynInfo (getSourcePos expression) (getLevel c)
  return (idContext, flattened "flattenConExp" (ConV inf c) rt Nothing)

-- Flatten an effect instantiation expression.
-- The result is an application term.
flattenInstanceExp expression op effects = do
  -- Flatten the operator.  It must have function type.
  (op_context, flat_op) <- flattenExpAsVal op
  unless (flattenedConv flat_op == Owned) $
    internalError "flattenInstanceExp"

  -- Make effect operands
  effect_vals <- mapM (effectValue $ getSourcePos expression) effects

  -- Get the effect information for this instance of the operator
  rt <- effectReturnType expression
  let inf = mkSynInfo (getSourcePos expression) ObjectLevel
  
  -- The result should not have the 'borrowed' passing convention
  let val = AppV inf (flattenedVal flat_op) effect_vals
  return (op_context, flattened "flattenInstanceExp" val rt Nothing)

flattenCall :: Effect.EIExp -> Effect.EIExp -> [Effect.EIExp]
            -> EffEnv ContextVal
flattenCall call_expression op args = do
  -- Flatten operator.  It must be a function.
  (op_context, flat_op) <- flattenExpAsVal op
  unless (flattenedConv flat_op == Owned) $
    traceShow (pprPassConv $ flattenedConv flat_op) $
    traceShow (pprAType $ flattenedType flat_op) $
    traceShow (Effect.pprExp op) $
    internalError "flattenCall"

  -- Flatten arguments and create call expression
  (call_context, call_val) <- flatten_and_make_call flat_op args
  return (op_context `mappend` call_context, call_val)
  where
    -- Take the flattened operator and flatten the arguments, generating one
    -- or more function call expressions
    flatten_and_make_call flat_op args = do
      -- Flatten operands
      ((oprd_context, val), excess_args) <-
        flatten_operands (getSourcePos call_expression) flat_op args

      -- If there are no more arguments, then return the call expression
      if null excess_args
        then return (oprd_context, val)
        else do
        -- Produce a value from the first call (it will be a function value)
        (call_context, call_val) <- genLetStatement =<< forceValue val

        -- Make another call expression for the remaining arguments
        (sub_context, call_val') <- flatten_and_make_call call_val excess_args
    
        return (oprd_context `mappend` call_context `mappend` sub_context, call_val')

    -- Flatten operands to a function call.
    -- Return context, the flattened operands, the return type,
    -- the return passing convention, and unused arguments.
    flatten_operands :: SourcePos      -- ^ Position of call expression
                     -> FlattenedVal   -- ^ Operator type
                     -> [Effect.EIExp] -- ^ Arguments, not yet flattened
                     -> EffEnv (ContextVal, [Effect.EIExp])
    flatten_operands pos flat_op args = do
      -- Flatten operands
      (ctx, arg_values, rptr, rparam, excess_args) <-
        flatten_operands' (verbatim $ flattenedType flat_op)
        (flattenedConv flat_op) args

      -- Create call expression
      let inf = mkSynInfo pos ObjectLevel
          val = AppV inf (flattenedVal flat_op) arg_values

      return ((ctx, flattened "flattenCall" val rparam rptr), excess_args)
    
    flatten_operands' :: RecAType SubstRec -- ^ Operator type
                      -> PassConv       -- ^ Operator passing convention (if
                                        -- there are no more arguments, this
                                        -- is the return passing convention)
                      -> [Effect.EIExp] -- ^ Arguments, not yet flattened
                      -> EffEnv (StmContext, [RVal], Maybe Var, AReturn' Rec, [Effect.EIExp])
    flatten_operands' op_type op_conv args = do
      op_type' <- freshenHead op_type
      case op_type' of
        AFunT {atypeMParam = binder, atypeRange = (pc, rng)} ->
          case args
          of arg : args' -> do
               -- Flatten operand and add it to the App term
               expected_return <-
                 case binder
                 of ValB' _ ty -> return $ ValR (substFully ty)
                    OwnB' ty -> return $ OwnR (substFully ty)
                    RefB' rgn ty -> do
                      operand_var <- newAnonymousVariable ObjectLevel
                      return $ RefR rgn operand_var (substFully ty)
               (context, arg_val) <- flattenCallOperand expected_return arg
               (context2, arg_vals, rptr, ret, excess_args) <-
                 flatten_operands' rng pc args'
               return (context `mappend` context2,
                       arg_val : arg_vals,
                       rptr,
                       ret,
                       excess_args)
             [] ->
               -- Under-saturated application
               return (idContext, [], Nothing, OwnR' (substFully op_type), [])
               
        ARetT {atypeReturn = ret} -> do
          -- Saturated application
          
          -- Add extra parameter for return region, if using the borrowed
          -- convention
          (return_arg, return_param) <-
            case ret
            of RefR' rgn ty -> do
                 -- Create a parameter for the borrowed return value
                 ptr <- newAnonymousVariable ObjectLevel
                 
                 let return_arg =
                       RefV { valInfo = internalSynInfo ObjectLevel
                            , valAddr = mkInternalVarE rgn
                            , valPtr = ptr
                            }
                 return ([return_arg], Just ptr)
               _ -> return ([], Nothing)
          
          return (idContext, return_arg, return_param, OwnR' (substFully op_type), args)

        _ ->
          internalError "flattenCall: Unexpected function type"
    
    -- Should be ignored: function calls will have at least one argument 
    undefined_pc = internalError "flattenCall"
    
flattenCallOperand :: AReturn Rec -> Effect.EIExp 
                   -> EffEnv (StmContext, RVal)
flattenCallOperand expect_return arg = do
  let arg_region = Effect.eiRegion arg
      
  -- Flatten the argument
  (arg_context, arg_val) <- flattenExpAsVal arg
  
  -- Coerce it to the expected type
  (arg_context2, arg_val') <- coerceValue expect_return arg_val
  return (arg_context `mappend` arg_context2, flattenedVal arg_val')

flattenDo expression ty pc body = do
  -- Convert operands
  (pc_context, pc_val) <- flattenExpAsVal pc
  (body_context, body_stm) <- flattenExpAsStm body
  
  -- Create the expression
  let inf = Effect.expInfo $ Effect.eiExp expression
  let val = StreamV inf (flattenedVal pc_val) (flattenedStm body_stm)
  (conv, ty) <-
    convertPassType (Effect.eiReturnType expression) (Effect.eiType expression)
    
  -- Return an owned stream value
  let rparam = OwnR' ty
  return (pc_context `mappend` body_context, flattened "flattenDo" val rparam Nothing)

flattenLet expression binder rhs body = do
  (rhs_context, rhs') <- flattenExpAsStm rhs
  convertBinder True binder $ \binder' -> do
    rhs'' <- renameReturnRegion binder' rhs'
    (body_context, body') <- flattenExpAsStm body
    let inf = Effect.expInfo $ Effect.eiExp expression
    let expr = LetS inf binder' (applyContext rhs_context rhs'') (flattenedStm body')

    return (body_context, body' {flattenedThing = expr})

flattenLetrec expression defs body = do
  defs' <- mapM flattenDef defs
  (body_context, body') <- flattenExpAsStm body
  let inf = Effect.expInfo $ Effect.eiExp expression
  let expr = LetrecS inf defs' (applyContext body_context $ flattenedStm body')
  return (body_context, body' {flattenedThing = expr})

flattenFun :: Effect.FunOf Effect.EI Effect.EI -> EffEnv (Fun Rec)
flattenFun fun =
  -- Add effect parameters to the environment
  assume_effects (Effect.funEffectParams fun) $ \effect_vars ->

  -- Convert binders and add parameter regions to environment
  withMany (convertBinder False) (Effect.funParams fun) $ \binders ->
  
  -- Convert the return type and create a return binder
  convert_return_type $ \ret_binder -> do
    
    -- Flatten the function body
    (body_context, body_stm) <- flattenExpAsStm $ Effect.funBody fun
    (body_context', body_stm') <- coerceStm ret_binder body_stm
    let body = applyContext (body_context `mappend` body_context') (flattenedStm body_stm')
    effect <- convertEffect $ Effect.funEffect fun

    let effect_params = [ValB v effect_type | v <- effect_vars]
          where effect_type = AExpT (internalSynInfo KindLevel) effectKindE
        
    let new_fun = Fun { ffunInfo = Effect.funInfo fun
                      , ffunParams = effect_params ++ binders
                      , ffunReturn = ret_binder
                      , ffunEffect = effect
                      , ffunBody = body
                      }
    return new_fun
  where
    assume_effects = withMany withNewEffectVariable
    
    convert_return_type k = do
      (return_conv, return_type) <-
        convertMonoPassType
        (Effect.funReturnPassType fun)
        (Effect.fromEIType $ Effect.funReturnType fun)

      case return_conv of
        ByValue  -> k $ ValR return_type
        Owned    -> k $ OwnR return_type
        Borrowed -> do
          -- Create parameters for the return pointer
          ret_addr <- newAnonymousVariable ObjectLevel
          ret_ptr <- newAnonymousVariable ObjectLevel
          k $ RefR ret_addr ret_ptr return_type
      

flattenCase :: Effect.EIExp 
            -> Effect.EIExp 
            -> [Effect.AltOf Effect.EI Effect.EI]
            -> EffEnv ContextStm
flattenCase expression scr alts = do
  -- Flatten the scrutinee
  (scr_context, scr_val) <- flattenExpAsVal scr
  (scr_context', scr_val') <- forceValueVal scr_val

  -- Get the case statement's return type
  (expr_conv, expr_type) <-
    convertPassType (Effect.eiReturnType expression) (Effect.eiType expression)

  -- The return type seen by effect inference should not be a RetT type
  when (case expr_type of {ARetT {} -> True; _ -> False}) $
    internalError "flattenCase"

  -- Flatten alternatives
  flattened_alts <- mapM (flattenAlt (getSourcePos expression)) alts

  -- Change alternatives so that they all write to the same destination.
  -- No change if the return convention is not 'Borrowed'.
  (alts', rp) <-
    case expr_conv
    of ByValue  -> return (map mk_alt flattened_alts, internalError "flattenCase")
       Owned    -> return (map mk_alt flattened_alts, internalError "flattenCase")
       Borrowed -> use_same_destination expr_type flattened_alts
  
  let inf = Effect.expInfo $ Effect.eiExp expression
  let stm = CaseS { stmInfo = inf
                  , stmScrutinee = flattenedVal scr_val'
                  , stmAlts = alts'
                  }
  let (rparam, rptr) =
        case expr_conv
        of ByValue  -> (ValR' expr_type, Nothing)
           Owned    -> (OwnR' expr_type, Nothing)
           Borrowed -> (RefR' (fst rp) expr_type, Just $ snd rp)
  return (scr_context `mappend` scr_context', flattened "flattenCase" stm rparam rptr)
  where
    mk_alt (inf, con, ty_args, params, body) =
      Alt inf con ty_args params (flattenedStm body)

    -- Ensure that all alternatives write their return value to the same
    -- place.  The return value is a borrowed value.
    -- Pick one return region
    -- and then coerce all alternatives to write into the same region.
    use_same_destination return_type flattened_alts = do
      -- Create a moveable return region
      addr <- newAnonymousVariable ObjectLevel
      ptr <- newAnonymousVariable ObjectLevel
      let return_param = (addr, ptr)
          return_binder = RefR addr ptr return_type
          
      -- Coerce all alternatives to write into this region
      let coerce_alt (inf, con, ty_args, params, body) = do
            (ctx, body') <- coerceStm return_binder body
            let body'' = body' {flattenedThing = applyContext ctx $ flattenedThing body'}
            return $ mk_alt (inf, con, ty_args, params, body'')
            
      alts' <- mapM coerce_alt flattened_alts
      
      return (alts', return_param)

-- | Flatten a case alternative.  The alternative's body will later be altered
-- so that all alternatives write their output to the same place.
flattenAlt :: SourcePos -> Effect.AltOf Effect.EI Effect.EI 
           -> EffEnv (SynInfo, Con, [RVal], [ABinder Rec], FlattenedStm)
flattenAlt pos alt = do
  let ty_arg_info = mkSynInfo pos TypeLevel
  let ty_args = map (TypeV ty_arg_info) $
                map convertType $
                Effect.eialtTyArgs alt
  withMany (convertBinder False) (Effect.eialtParams alt) $ \params -> do
    (body_ctx, body_stm) <- flattenExpAsStm $ Effect.eialtBody alt
  
    let body = body_stm {flattenedThing = applyContext body_ctx $ flattenedThing body_stm}
    let inf = mkSynInfo pos ObjectLevel
        con = Effect.eialtConstructor alt
    return (inf, con, ty_args, params, body)

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
