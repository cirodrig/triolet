{-| Intermediate representation with explicit data representations. 

This representation extends the pure System F
with more detailed information about how data structures fit
into memory.  Each variable binding gets extra information.
-}

module SystemF.MemoryIR
       (Mem,
        Mentions(..),
        Pat(PatM),
        patM,
        patMVar,
        patMType,
        patMBinder,
        patMUses,
        setPatMUses,
        patMDmd,
        setPatMDmd,
        isDeadPattern,
        Exp(..),
        Alt(..),
        Fun(..),
        PatM, ExpM, AltM, FunM,
        appE, conE,
        unpackVarAppM, unpackDataConAppM, isDataConAppM,
        assumePatM, assumePatMs,
        assumeTyPat, assumeTyPats,
        assumeDef,
        assumeDefGroup,
        functionType,
        partitionParameters
       )
where

import Common.Error
import SystemF.Syntax
import SystemF.Demand
import SystemF.DeadCode(Mentions(..))
import Type.Environment
import Type.Type
import Type.Var
import Type.Eval

data Mem

-- | A variable binding in a program.
--   Bindings are annotated with demand information.
data instance Pat Mem =
  PatM
  { _patMBinder :: {-#UNPACK#-}!Binder
  , _patMUses :: {-#UNPACK#-}!Dmd
  }

patM :: Binder -> PatM
patM binder = PatM binder unknownDmd

patMVar :: PatM -> Var
patMVar (PatM (v ::: _) _) = v

patMType :: PatM -> Type
patMType (PatM (_ ::: t) _) = t

patMBinder :: PatM -> Binder
patMBinder = _patMBinder

-- | For compatibility with old code, we can convert between mentions and
--   demand types.
mentionToDmd :: Mentions -> Dmd
mentionToDmd One  = Dmd OnceUnsafe Used
mentionToDmd Many = Dmd ManyUnsafe Used

-- | For compatibility with old code, we can convert between mentions and
--   demand types.  The conversion from 'Dmd' to 'Mentions' is lossy.
dmdToMention :: Dmd -> Mentions
dmdToMention dmd = case multiplicity dmd
                   of Dead       -> One
                      OnceSafe   -> One
                      OnceUnsafe -> One
                      _          -> Many

patMUses :: PatM -> Mentions
patMUses = dmdToMention . _patMUses

setPatMUses :: Mentions -> PatM -> PatM
setPatMUses m pat = pat {_patMUses = mentionToDmd m}

patMDmd :: PatM -> Dmd
patMDmd (PatM {_patMUses = u}) = u

setPatMDmd :: Dmd -> PatM -> PatM
setPatMDmd m pat = pat {_patMUses = m}

-- | Return True if the pattern is marked as dead.
isDeadPattern :: PatM -> Bool
isDeadPattern pat = multiplicity (patMDmd pat) == Dead

newtype instance Exp Mem = ExpM {fromExpM :: BaseExp Mem}
newtype instance Alt Mem = AltM {fromAltM :: BaseAlt Mem}
newtype instance Fun Mem = FunM {fromFunM :: BaseFun Mem}

type PatM = Pat Mem
type ExpM = Exp Mem
type AltM = Alt Mem
type FunM = Fun Mem

appE :: ExpInfo -> ExpM -> [Type] -> [ExpM] -> ExpM
appE _ op [] [] = op
appE inf op type_args args = ExpM (AppE inf op type_args args)

conE :: ExpInfo -> ConInst -> [ExpM] -> ExpM
conE inf op args = ExpM (ConE inf op args)

{- Obsolete; 'BaseAlt' is isomorphic to this tuple type now
-- | Construct a case alternative given a 'MonoCon' and the other required 
--   fields
altFromMonoCon :: DeConInst -> [PatM] -> ExpM -> AltM
altFromMonoCon (VarDeCon con ty_args ex_types) fields body =
  let ex_patterns = map TyPatM ex_types
  in AltM $ DeCon con (map TypM ty_args) ex_patterns fields body

altFromMonoCon (TupleDeCon _) fields body =
  AltM $ DeTuple fields body

altToMonoCon :: AltM -> (DeConInst, [PatM], ExpM)
altToMonoCon (AltM (VarDeCon con ty_args ex_types fields body)) =
  (TupleDeCon con (map fromTypM ty_args) [b | TyPatM b <- ex_types], fields, body)

altToMonoCon (AltM (DeTuple fields body)) =
  (MonoTuple (map patMType fields), fields, body)
-}

unpackVarAppM :: ExpM -> Maybe (Var, [Type], [ExpM])
unpackVarAppM (ExpM (AppE { expOper = ExpM (VarE _ op)
                          , expTyArgs = ts
                          , expArgs = xs})) =
  Just (op, ts, xs)

unpackVarAppM (ExpM (VarE { expVar = op })) =
  Just (op, [], [])

unpackVarAppM _ = Nothing

-- | If the expression is a data constructor (other than a tuple),
--   return the data constructor, type arguments, existential types,
--   and field arguments
unpackDataConAppM :: TypeEnv -> ExpM
                  -> Maybe (DataConType, [Type], [Type], [ExpM])
unpackDataConAppM tenv (ExpM (ConE inf con args)) =
  case con of
    VarCon op ty_args ex_types -> 
      let Just dcon = lookupDataCon op tenv
      in Just (dcon, ty_args, ex_types, args)
    TupleCon types ->
      Nothing

unpackDataConAppM _ _ = Nothing

-- | Return True if the expression is a data constructor or data constructor
--   application.
--
--   The type environment is only used for looking up potential data
--   constructors.
isDataConAppM :: TypeEnv -> ExpM -> Bool
isDataConAppM tenv e = case unpackDataConAppM tenv e
                       of Just _ -> True
                          _ -> False

assumePatM :: TypeEnvMonad m => PatM -> m a -> m a
assumePatM pat m = assumeBinder (patMBinder pat) m

assumePatMs :: TypeEnvMonad m => [PatM] -> m a -> m a
assumePatMs pats m = foldr assumePatM m pats

assumeTyPat :: TypeEnvMonad m => TyPat -> m a -> m a
assumeTyPat (TyPat b) m = assumeBinder b m

assumeTyPats :: TypeEnvMonad m => [TyPat] -> m a -> m a
assumeTyPats pats m = foldr assumeTyPat m pats

assumeDef :: forall m a. TypeEnvMonad m => Def Mem -> m a -> m a
{-# INLINE assumeDef #-}
assumeDef def m = assume (definiendum def) (functionType $ definiens def) m

assumeDefGroup :: forall m a b. TypeEnvMonad m =>
                  DefGroup (Def Mem) -> m a -> m b -> m (a, b)
{-# INLINE assumeDefGroup #-}
assumeDefGroup g group_m body_m =
  case g
  of NonRec def -> do x <- group_m 
                      y <- assumeDef def body_m
                      return (x, y)
     Rec defs -> assume_defs defs $ do x <- group_m
                                       y <- body_m
                                       return (x, y)
  where
    assume_defs :: forall a. [Def Mem] -> m a -> m a
    assume_defs defs m = foldr assumeDef m defs

-- | Get the type of a function using its parameter and return types.
functionType :: FunM -> Type 
functionType (FunM (Fun { funTyParams = ty_params
                        , funParams = params
                        , funReturn = ret
                        })) =
  forallType [b | TyPat b <- ty_params] $
  funType (map patMType params) ret

-- | Partition a list of parameters into input and output parameters.
--   Output parameters must follow input parameters.
partitionParameters :: TypeEnv -> [PatM] -> ([PatM], [PatM])
partitionParameters tenv params = go id params 
  where
    -- Take parameters until the first output parameter is found
    go hd (p:ps) =
      case toBaseKind $ typeKind tenv (patMType p)
      of OutK -> (hd [], check_out_kinds (p:ps))
         _    -> go (hd . (p:)) ps

    go hd [] = (hd [], [])
        
    -- Verify that all parameters in the list are output parameters
    check_out_kinds ps
      | and [OutK == toBaseKind (typeKind tenv (patMType p)) | p <- ps] = ps
      | otherwise =
        internalError "partitionParameters: Invalid parameter order"
    
