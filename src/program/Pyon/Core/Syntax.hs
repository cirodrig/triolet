
{-# LANGUAGE TypeFamilies, TypeSynonymInstances, RankNTypes, DeriveDataTypeable #-}
module Pyon.Core.Syntax where

import Control.Monad
import Data.Typeable

import Gluon.Common.Error
import Gluon.Common.SourcePos
import Gluon.Core.Level
import Gluon.Core.Syntax
import Gluon.Core.RenameBase
import Gluon.Core.Rename
import qualified Gluon.Core.Builtins.Effect

import qualified Pyon.SystemF.Syntax as SystemF

data family CTypeOf s :: * -> *
data family CFunTypeOf s :: * -> *
data family CExpOf s :: * -> *
data family CAltOf s :: * -> *
data family CFunOf s :: * -> *
     
type CType s = CTypeOf Rec s
type CFunType s = CFunTypeOf Rec s
type CExp s = CExpOf Rec s
type CAlt s = CAltOf Rec s
type CFun s = CFunOf Rec s

type RecCType s = CTypeOf s s
type RecCFunType s = CFunTypeOf s s
type RecCExp s = CExpOf s s
type RecCAlt s = CAltOf s s
type RecCFun s = CFunOf s s

type RCType = RecCType Rec
type RCFunType = RecCFunType Rec
type RCExp = RecCExp Rec
type RCAlt = RecCAlt Rec
type RCFun = RecCFun Rec

-- TODO: Combine this with the identical definition in PassConv.hs
data PassConv = ByValue | Owned | Borrowed
              deriving(Eq)

-- | An address variable appearing in a binder
type AddrVar = Var

-- | A pointer variable appearing in a binder
type PtrVar = Var

-- | An expression that evaluates to an address value
type AddrExp s = RecExp s

-- | An expression that evaluates to a pointer value
type PtrExp s = RecCExp s

-- | Something decorated with a type.
data CBind t s = !(t s) ::: RecCType s

fromCBind :: CBind t s -> t s
fromCBind (x ::: _) = x

cbindType :: CBind t s -> RecCType s
cbindType (_ ::: t) = t

-- | A parameter type.
data CParamT s =
    -- | A pass-by-value parameter.  If the variable is present, the parameter 
    -- type is used dependently.
    ValPT !(Maybe Var)
    -- | An owned-reference parameter.
  | OwnPT
    -- | A borrowed reference, read-only parameter.
  | ReadPT !AddrVar

-- | A return type.
data CReturnT s =
    -- | A pass-by-value return type. 
    ValRT
    -- | An owned-reference return type. 
  | OwnRT
    -- | A borrowed-reference return type.  This type represents writing into
    --   a memory area chosen by the caller. 
  | WriteRT
    -- | A read-only reference to a memory area chosen by the callee.
  | ReadRT !(AddrExp s)

-- | A parameter binder.
data CParam s =
    -- | A pass-by-value parameter.
    ValP !Var
    -- | An owned reference parameter.
  | OwnP !Var
    -- | A borrowed-reference parameter.  The parameter consists of address
    -- and pointer variables.
  | ReadP !AddrVar !PtrVar

-- | A return binder.
data CReturn s =
    -- | Return a value
    ValR
    -- | Return an owned reference
  | OwnR
    -- | Return by writing into a borrowed reference.  The return address and
    --   pointer are passed as parameters.
  | WriteR !AddrVar !PtrVar
    -- | Return a borrowed reference to an existing object.
  | ReadR !(AddrExp s) !PtrVar 

returnType :: CReturn s -> CReturnT s
returnType ValR = ValRT
returnType OwnR = OwnRT
returnType (WriteR a p) = WriteRT
returnType (ReadR a p) = ReadRT a

-- | A @let@ binder.
data LetBinder s =
    -- | Bind a value
    ValB !Var
    -- | Bind an owned reference
  | OwnB !Var
    -- | Allocate a local variable.  The address and pointer are allocated
    -- and should be passed as a parameter to the RHS of the let expression,
    -- which will write the variable.
  | LocalB !AddrVar !PtrVar
    -- | Bind a borrowed reference to an existing variable.  The RHS of the
    --   let expression returns a pointer to a known address.
  | RefB !(AddrExp s) !PtrVar

data Value s =
    ValueVarV !Var
  | OwnedVarV !Var
  | ReadVarV !(AddrExp s) !PtrVar
  | WriteVarV !(AddrExp s) !PtrVar
  | ValueConV !Con
  | OwnedConV !Con
  | LitV !SystemF.Lit
  | TypeV (RecCType s)

letBinderValue :: LetBinder Rec -> Value Rec
letBinderValue (ValB v) = ValueVarV v
letBinderValue (OwnB v) = OwnedVarV v
letBinderValue (LocalB a p) = ReadVarV (mkInternalVarE a) p
letBinderValue (RefB a p) = ReadVarV a p

letBinderReturn :: CBind LetBinder Rec -> CBind CReturn Rec
letBinderReturn (lb ::: ty) =
  let rt = case lb
           of ValB _     -> ValR
              OwnB _     -> OwnR
              LocalB a p -> WriteR a p
              RefB a p   -> ReadR a p
  in rt ::: ty

letBinderType :: CBind LetBinder Rec -> CBind CReturnT Rec
letBinderType (lb ::: ty) =
  let rt = case lb
           of ValB _     -> ValRT
              OwnB _     -> OwnRT
              LocalB a _ -> ReadRT (mkInternalVarE a)
              RefB a _   -> ReadRT a
  in rt ::: ty

writePointerRV :: SourcePos -> AddrExp Rec -> PtrVar -> RCExp
writePointerRV pos a p = ValCE (mkSynInfo pos ObjectLevel) (WriteVarV a p)

-- | A data type after translation from System F.
data instance CTypeOf Rec s =
    -- | A System F data type.
    ExpCT
    { ctValue :: RecExp s
    }
    -- | A System F data type.
  | AppCT
    { ctOper :: RecExp s
    , ctArgs :: [(PassConv, RecCType s)]
    }
    -- | A function type.
  | FunCT
    { ctFunType :: RecCFunType s
    }

data instance CFunTypeOf Rec s =
    ArrCT
    { ctParam :: !(CBind CParamT s)
    , ctEffect :: RecCType s
    , ctRange :: RecCFunType s
    }
  | RetCT
    { ctEffect :: RecCType s
    , ctReturn :: !(CBind CReturnT s)
    }

expCT :: RecExp s -> CType s
expCT e = ExpCT e

appCT :: RecExp s -> [(PassConv, RecCType s)] -> CType s
appCT op args = AppCT op args

appByValue :: RecExp s -> [RecCType s] -> CType s
appByValue op args = AppCT op [(ByValue, t) | t <- args]

funCT :: RecCFunType s -> CType s
funCT = FunCT

arrCT :: CBind CParamT s -> RecCType s -> RecCFunType s -> CFunType s
arrCT param eff range = ArrCT param eff range

pureArrCT :: CBind CParamT Rec -> RCFunType -> RCFunType
pureArrCT param range = arrCT param empty_effect range
  where
    empty_effect = expCT Gluon.Core.Builtins.Effect.empty

retCT :: RecCType s -> CBind CReturnT s -> CFunType s
retCT eff ret = RetCT eff ret

functionCT :: [CBind CParamT Rec] -> RCType -> CBind CReturnT Rec -> RCFunType
functionCT params eff ret = foldr pureArrCT (retCT eff ret) params

data instance CExpOf Rec s =
    ValCE
    { cexpInfo :: !SynInfo
    , cexpVal :: !(Value s)
    }
  | AppCE
    { cexpInfo :: !SynInfo
    , cexpOper :: RecCExp s
    , cexpArgs :: [RecCExp s]
      -- | An argument saying where to store the return value.  This is either
      -- 'Nothing' or an expression that evaluates to a 'WriteRV' value.
    , cexpReturnArg :: !(Maybe (RecCExp s))
    }
  | LamCE
    { cexpInfo :: !SynInfo
    , cexpFun :: RecCFun s
    }
  | LetCE
    { cexpInfo :: !SynInfo
    , cexpBinder :: !(CBind LetBinder s)
    , cexpRhs :: RecCExp s
    , cexpBody :: RecCExp s
    }
  | LetrecCE
    { cexpInfo :: !SynInfo
    , cexpDefs :: [CDef s]
    , cexpBody :: RecCExp s
    }
  | CaseCE
    { cexpInfo :: !SynInfo
    , cexpScrutinee :: RecCExp s
    , cexpAlternatives :: [RecCAlt s]
    }

data instance CAltOf Rec s =
  CAlt
  { caltInfo :: !SynInfo
  , caltConstructor :: !Con
  , caltTyArgs :: [RecCExp s]
  , caltParams :: [CBind CParam s]
  , caltBody :: RecCExp s
  }

data instance CFunOf Rec s =
  CFun
  { cfunInfo :: !SynInfo
  , cfunParams :: [CBind CParam s]
  , cfunReturn :: CBind CReturn s
  , cfunEffect :: RecCType s
  , cfunBody :: RecCExp s
  }

data CDef s = CDef !Var !(RecCFun s)
            deriving(Typeable)

instance HasSourcePos (CExp s) where
  getSourcePos e = getSourcePos $ cexpInfo e
  setSourcePos e p = e {cexpInfo = setSourcePos (cexpInfo e) p}

-------------------------------------------------------------------------------
-- Renaming

type Substituter a b = forall t. Substitutable t => t a a -> t b b

substituteCBind :: (Substituter u v -> a u -> a v)
                -> Substituter u v
                -> CBind a u
                -> CBind a v
substituteCBind g f (x ::: t) = g f x ::: f t

substituteCParamT :: Substituter u v
                -> CParamT u
                -> CParamT v
substituteCParamT _ param =
  case param
  of ValPT mv -> ValPT mv
     OwnPT    -> OwnPT
     ReadPT v -> ReadPT v

substituteCReturnT :: Substituter u v
                   -> CReturnT u
                   -> CReturnT v
substituteCReturnT f ret =
  case ret
  of ValRT    -> ValRT
     OwnRT    -> OwnRT
     WriteRT  -> WriteRT
     ReadRT a -> ReadRT (f a)

substituteCParam :: Substituter u v -> CParam u -> CParam v
substituteCParam _ param =
  case param
  of ValP v -> ValP v
     OwnP v -> OwnP v
     ReadP a v -> ReadP a v

substituteCReturn :: Substituter u v -> CReturn u -> CReturn v
substituteCReturn _ ret =
  case ret
  of ValR       -> ValR
     OwnR       -> OwnR
     WriteR a v -> WriteR a v

substituteLetBinder :: Substituter u v -> LetBinder u -> LetBinder v
substituteLetBinder f binder =
  case binder
  of ValB v -> ValB v
     OwnB v -> OwnB v
     LocalB a p -> LocalB a p
     RefB a p -> RefB (f a) p

substituteValue :: Substituter u v -> Value u -> Value v
substituteValue f value =
  case value
  of ValueVarV v  -> ValueVarV v
     OwnedVarV v  -> OwnedVarV v
     ReadVarV a v -> ReadVarV (f a) v
     WriteVarV a v -> WriteVarV (f a) v
     ValueConV c -> ValueConV c
     OwnedConV c -> OwnedConV c
     LitV l -> LitV l
     TypeV t -> TypeV (f t)

substituteDef :: Substituter u v -> CDef u -> CDef v
substituteDef f (CDef v fun) = CDef v (f fun)

withFreshVarMaybe Nothing m = do
  x <- m
  return (Nothing, x)
  
withFreshVarMaybe (Just v) m = do
  (v', x) <- withFreshVar v m
  return (Just v', x)

freshenCBind :: (t SubstRec -> WithSubstitution a -> WithSubstitution (t SubstRec, a))
             -> CBind t SubstRec
             -> WithSubstitution a
             -> WithSubstitution (CBind t SubstRec, a)
freshenCBind f (x ::: ty) m = do 
  (x', y) <- f x m
  ty' <- joinSubstitution ty
  return (x' ::: ty', y)

freshenCBind' f (x ::: ty) = liftM2 (:::) (f x) (joinSubstitution ty)

freshenFullyCBind :: (t SubstRec -> WithSubstitution a -> WithSubstitution (t Rec, a))
             -> CBind t SubstRec
             -> WithSubstitution a
             -> WithSubstitution (CBind t Rec, a)
freshenFullyCBind f (x ::: ty) m = do
  (x', y) <- f x m
  ty' <- freshenFully ty
  return (x' ::: ty', y)

freshenFullyCBind' f (x ::: ty) = liftM2 (:::) (f x) (freshenFully ty)

freshenCParamT :: CParamT SubstRec
               -> WithSubstitution a
               -> WithSubstitution (CParamT s, a)
freshenCParamT param m =
  case param
  of ValPT mv -> do
       (mv', x) <- withFreshVarMaybe mv m
       return (ValPT mv', x)
     OwnPT -> do
       x <- m
       return (OwnPT, x)
     ReadPT a -> do
       (a', x) <- withFreshVar a m
       return (ReadPT a', x)

freshenCReturnT :: CReturnT SubstRec
                -> WithSubstitution (CReturnT SubstRec)
freshenCReturnT retn =
  case retn
  of ValRT    -> return ValRT
     OwnRT    -> return OwnRT
     WriteRT  -> return WriteRT
     ReadRT e -> ReadRT `liftM` joinSubstitution e

freshenFullyCReturnT :: CReturnT SubstRec
                     -> WithSubstitution (CReturnT Rec)
freshenFullyCReturnT retn =
  case retn
  of ValRT    -> return ValRT
     OwnRT    -> return OwnRT
     WriteRT  -> return WriteRT
     ReadRT e -> ReadRT `liftM` freshenFully e

data instance CTypeOf (Subst s) (Subst s) = SubstCType (SubstWrapped CTypeOf)
data instance CFunTypeOf (Subst s) (Subst s) = SubstCFT (SubstWrapped CFunTypeOf)
data instance CExpOf (Subst s) (Subst s) = SubstCExp (SubstWrapped CExpOf)
data instance CFunOf (Subst s) (Subst s) = SubstCFun (SubstWrapped CFunOf)
data instance CAltOf (Subst s) (Subst s) = SubstCAlt (SubstWrapped CAltOf)

instance Substitutable CTypeOf where
  asSubst = SubstCType
  fromSubst (SubstCType x) = x
  
  mapSubstitutable f expression =
    case expression
    of ExpCT val -> ExpCT (f val)
       AppCT op args -> AppCT (f op) [(pc, f arg) | (pc, arg) <- args]
       FunCT t -> FunCT (f t)
  
  applySubstitution subst = mapSubstitutable (joinSubst subst)
  
instance Renameable CTypeOf where
  freshenHead expression = withSubstitutable expression f
    where
      f expression =
        case expression
        of ExpCT val -> ExpCT `liftM` joinSubstitution val
           AppCT op args -> AppCT `liftM`
                            joinSubstitution op `ap`
                            mapM joinPassType args 
           FunCT t -> FunCT `liftM` joinSubstitution t

      joinPassType (pc, t) = do
        t' <- joinSubstitution t
        return (pc, t')

  freshenFully x = do 
    x' <- freshenHead x
    case x' of
      ExpCT val -> ExpCT `liftM` freshenFully val
      AppCT op args -> AppCT `liftM`
                       freshenFully op `ap`
                       mapM freshen args 
      FunCT t -> FunCT `liftM` freshenFully t
    where
      freshen (pc, t) = do
        t' <- freshenFully t
        return (pc, t')

instance Substitutable CFunTypeOf where
  asSubst = SubstCFT
  fromSubst (SubstCFT x) = x
  mapSubstitutable f expression =
    case expression
    of ArrCT param eff rng ->
         ArrCT (substituteCBind substituteCParamT f param) (f eff) (f rng)
       RetCT eff ret ->
         RetCT (f eff) (substituteCBind substituteCReturnT f ret)
  
  applySubstitution subst = mapSubstitutable (joinSubst subst)

instance Renameable CFunTypeOf where
  freshenHead expression = withSubstitutable expression f
    where
      f expression =
        case expression
        of ArrCT param eff range -> do
             (param', (eff', range')) <-
               freshenCBind freshenCParamT param $ do
                 eff' <- joinSubstitution eff
                 range' <- joinSubstitution range
                 return (eff', range')
             return $ ArrCT param' eff' range'
           RetCT eff ret ->
             RetCT `liftM`
             joinSubstitution eff `ap`
             freshenCBind' freshenCReturnT ret

  freshenFully x = withSubstitutable x freshen
    where
      freshen expression =
        case expression
        of ArrCT param eff range -> do
             (param', (eff', range')) <-
               freshenFullyCBind freshenCParamT param $ do
                 eff' <- freshenFully eff
                 range' <- freshenFully range
                 return (eff', range')
             return $ ArrCT param' eff' range'
           RetCT eff ret ->
             RetCT `liftM`
             freshenFully eff `ap`
             freshenFullyCBind' freshenFullyCReturnT ret


instance Substitutable CExpOf where
  asSubst = SubstCExp
  fromSubst (SubstCExp x) = x
  
  mapSubstitutable f expression =
    case expression
    of ValCE inf v -> ValCE inf (substituteValue f v)
       AppCE inf op args ra ->
         AppCE inf (f op) (map f args) (fmap f ra)
       LamCE inf fun -> LamCE inf (f fun)
       LetCE inf b rhs body ->
         LetCE inf (substituteCBind substituteLetBinder f b) (f rhs) (f body)
       LetrecCE inf defs body ->
         LetrecCE inf (map (substituteDef f) defs) (f body)
       CaseCE inf scr alts ->
         CaseCE inf (f scr) (map f alts)

  applySubstitution subst expression =
    case expression 
    of ValCE inf value ->
         let value' =
               case value
               of ValueVarV v   -> ValueVarV $! subst_var v
                  OwnedVarV v   -> OwnedVarV $! subst_var v
                  ReadVarV a p  -> ReadVarV (joinSubst subst a) $! subst_var p
                  WriteVarV a p -> WriteVarV (joinSubst subst a) $! subst_var p
                  ValueConV c   -> ValueConV c
                  OwnedConV c   -> OwnedConV c
                  LitV l        -> LitV l
                  TypeV t       -> TypeV $ joinSubst subst t
         in ValCE inf value'
       _ -> mapSubstitutable (joinSubst subst) expression
    where
      subst_var v =
        case lookupVarVar v subst
        of Nothing -> v
           Just (Just v') -> v'
           Just Nothing -> internalError "CExpOf.applySubstitution: cannot substitute an expression here"

instance Substitutable CFunOf where
  asSubst = SubstCFun
  fromSubst (SubstCFun x) = x
  
  mapSubstitutable f fun =
    CFun { cfunInfo = cfunInfo fun
         , cfunParams = map (substituteCBind substituteCParam f) $
                        cfunParams fun
         , cfunReturn = substituteCBind substituteCReturn f $ cfunReturn fun
         , cfunEffect = f $ cfunEffect fun
         , cfunBody = f $ cfunBody fun
         }

  applySubstitution subst = mapSubstitutable (joinSubst subst)

instance Substitutable CAltOf where
  asSubst = SubstCAlt
  fromSubst (SubstCAlt x) = x
  
  mapSubstitutable f alt =
    CAlt { caltInfo = caltInfo alt
         , caltConstructor = caltConstructor alt
         , caltTyArgs = map f $ caltTyArgs alt
         , caltParams = map (substituteCBind substituteCParam f) $
                        caltParams alt
         , caltBody = f $ caltBody alt
         }

  applySubstitution subst = mapSubstitutable (joinSubst subst)

assignType :: Var -> RCType -> RecCType SubstRec -> RecCType Rec
assignType v ty assigned_type = assign_in assigned_type
  where
    assign_in t =
      case substHead t
      of ExpCT e ->
           case substHead e
           of VarE {expInfo = inf, expVar = v'}
                | v == v'   -> ty
                | otherwise -> ExpCT $ VarE inf v'
                               
              -- Other expressions must not mention 'v'; we can't
              -- put the new type expression there
              e' | substFullyUnder e' `mentions` v ->
                internalError "assignType"
                 | otherwise -> ExpCT $ substFullyUnder e'

         AppCT op args
           | substFully op `mentions` v ->
                internalError "assignType"
           | otherwise ->
             AppCT (substFully op) [(pc, assign_in arg) | (pc, arg) <- args]

         FunCT t -> FunCT (assign_fun t)

    assign_fun t = assignTypeFun v ty t

assignTypeFun :: Var -> RCType -> RecCFunType SubstRec -> RecCFunType Rec
assignTypeFun v ty assigned_type = assign_fun assigned_type
  where
    assign_in t = assignType v ty t

    assign_fun t =
      case substHead t
      of ArrCT param eff rng ->
           ArrCT (assign_param param) (assign_in eff) (assign_fun rng)
         RetCT eff ret ->
           RetCT (assign_in eff) (assign_ret ret)
        
    assign_param (p ::: ty) =
      let p' = case p
               of ValPT mv -> ValPT mv
                  OwnPT -> OwnPT
                  ReadPT a -> ReadPT a
      in p' ::: assign_in ty                  
         
    assign_ret (r ::: ty) =
      let r' = case r
               of ValRT -> ValRT
                  OwnRT -> OwnRT
                  WriteRT -> WriteRT
                  ReadRT e 
                    | substFully e `mentions` v -> internalError "assignType"
                    | otherwise -> ReadRT (substFully e)
      in r' ::: assign_in ty