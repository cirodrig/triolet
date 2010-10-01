
{-# LANGUAGE FlexibleInstances, ViewPatterns, Rank2Types #-}
module SystemF.Flatten.EffectExp
where

import Control.Monad
import Control.Monad.Trans
import Control.Concurrent.MVar
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.MonadLogic
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Gluon.Core.Level
import Gluon.Core.Variance
import Gluon.Core(Rec, SynInfo(..), mkSynInfo, internalSynInfo,
                  Con, conID, Var, varID)
import qualified Gluon.Core as Gluon
import Gluon.Eval.Eval
import qualified SystemF.Syntax as SF
import qualified SystemF.Print as SF
import qualified SystemF.Typecheck as SF
import qualified Core.Syntax as Core
import Core.Syntax(Representation(..))
import qualified Core.BuiltinTypes as Core
import SystemF.Flatten.Constraint
import SystemF.Flatten.Effect
import SystemF.Flatten.EffectType
import Globals

-- | A placeholder reference to an expression.  The placeholder is created to
-- stand for the value of a recursively defined variable.  It is assigned an
-- expression during generalization.
type PlaceholderRef = MVar EExp

-- | An effect-typed parameter.
--
-- Constructors of 'EParam' correspond to constructors of 'EParamType', except
-- that a bound variable is given.
data EParam =
    ValP Var EType
  | OwnP Var EType
  | ReadP Var RVar EType

paramVar :: EParam -> Var
paramVar (ValP v _) = v
paramVar (OwnP v _) = v
paramVar (ReadP v _ _) = v

paramType :: EParam -> EType
paramType (ValP _ t) = t
paramType (OwnP _ t) = t
paramType (ReadP _ _ t) = t

-- | Get the 'EParamType' of a parameter.  The boolean flag is used to indicate
-- whether the parameter variable is used dependently in the rest of the
-- expression.
paramParamType :: EParam -> Bool -> EParamType
paramParamType (ValP v t) True = ValPT (Just v) t
paramParamType (ValP v t) False = ValPT Nothing t
paramParamType (OwnP _ t) False = OwnPT t
paramParamType (ReadP _ rgn t) False = ReadPT rgn t
paramParamType _ True =
  internalError "paramParamType: Unexpected dependent parameter" 

paramReturnType :: EParam -> EReturnType
paramReturnType (ValP _ t) = ValRT t
paramReturnType (OwnP _ t) = OwnRT t
paramReturnType (ReadP _ rgn t) = ReadRT rgn t

paramRegion :: EParam -> Maybe RVar
paramRegion (ValP {}) = Nothing 
paramRegion (OwnP {}) = Nothing 
paramRegion (ReadP _ rgn _) = Just rgn

mkParamFromTypeParam :: EParamType -> RegionM EParam
mkParamFromTypeParam pt = 
  case pt
  of ValPT (Just v) t -> return $ ValP v t
     ValPT Nothing t -> do
       v <- Gluon.newAnonymousVariable (pred $ getLevel t)
       return $ ValP v t
     OwnPT t -> do
       v <- Gluon.newAnonymousVariable (pred $ getLevel t)
       return $ OwnP v t
     ReadPT rgn t -> do
       v <- Gluon.newAnonymousVariable (pred $ getLevel t)
       return $ ReadP v rgn t

paramVarExp :: EParam -> EExp
paramVarExp param =
  let exp = VarE $ paramVar param
      info = internalSynInfo $ getLevel $ paramVar param
      return_type = paramReturnType param
  in EExp info return_type exp

data EExp = 
  EExp
  { expInfo :: !SynInfo
  , expReturn :: EReturnType       -- ^ Type of the expression's result value
  , expExp :: !EExp'
  }

data EExp' =
    VarE
    { expVar :: Var
    }
  | ConE 
    { expCon :: !Con
    }
  | LitE 
    { expLit :: !SF.Lit
    , expType :: EType
    }
  | TypeE 
    { expTypeValue :: EType
    }
  | InstE 
    { expPolyOper :: Either Var Con 
    , expPolyArgs :: [Effect]
    }
  | RecPlaceholderE 
    { expVar :: Var 
    , expPlaceholderValue :: {-# UNPACK #-}!PlaceholderRef
    }
  | CallE
    { expOper :: EExp
    , expArgs :: [EExp]
    }
  | FunE
    { expFun :: EFun
    }
  | DoE
    { expTyArg :: EExp
    , expPassConv :: EExp
    , expBody :: EExp
    }
  | LetE
    { expLhs :: Var
    , expLhsType :: EReturnType
    , expRhs :: EExp
    , expBody :: EExp
    }
  | LetrecE
    { expDefs :: EDefGroup
    , expBody :: EExp
    }
  | CaseE
    { expScrutinee :: EExp
    , expAlts :: [EAlt]
    }

  -- Coercions
    
    -- | Load a return value (coerce @Read -> Value@)
  | GenLoadValue EExp
    -- | Create temporary storage to hold a return value, then load it
    -- (coerce @Write -> Value@)
  | GenTempLoadValue EExp
    -- | Load an owned reference (coerce @Read -> Owned@)
  | GenLoadOwned EExp
    -- | Create temporary storage to hold an owned reference, then load it
    -- (coerce @Write -> Owned@)
  | GenTempLoadOwned EExp
    -- | Store a return value (coerce @Value -> Write@)
  | GenStoreValue EExp
    -- | Store a value for a parameter (coerce @Value -> Read@)
  | GenTempStoreValue EExp
    -- | Store a return owned reference (coerce @Owned -> Write@)
  | GenStoreOwned EExp
    -- | Store an owned reference for a parameter (coerce @Owned -> Read@)
  | GenTempStoreOwned EExp

data EAlt =
  EAlt
  { ealtCon    :: Con
  , ealtTyArgs :: [EType]
  , ealtParams :: [EParam]
  , ealtBody   :: EExp
  }

data EFun =
  EFun
  { funInfo         :: !SynInfo
  , funEffectParams :: [EVar]
  , funParams       :: [EParam]
  , funReturnType   :: EReturnType
  , funEffect       :: Effect
  , funBody         :: EExp
  }

-- | Get the type of an effect-inferred function, without universal
-- quantifiers.
efunMonoType :: EFun -> ERepType
efunMonoType fun
  | null $ funParams fun = internalError "efunMonoType: Nullary function"
  | otherwise =
      -- Process parameters in reverse order
      let (last_param:params) = reverse $ funParams fun

          last_param_mentioned =
            funReturnType fun `mentionsT` paramVar last_param ||
            funEffect fun `mentionsT` paramVar last_param

          last_param_type = paramParamType last_param last_param_mentioned
          fun_type_1 =
            funT last_param_type (funEffect fun) (funReturnType fun)
      
      in foldl add_parameter fun_type_1 params
  where
    add_parameter range param =
      let param_mentioned = range `mentionsT` paramVar param
          param_type = paramParamType param param_mentioned
      in funT param_type emptyEffect (OwnRT $ discardTypeRepr range)

efunPolyType :: EFun -> EffectAssignment
efunPolyType f =
  let mono_type = OwnRT $ discardTypeRepr $ efunMonoType f
  in if null $ funEffectParams f
     then MonoEffect mono_type
     else PolyEffect (funEffectParams f) mono_type
      

data EDef = EDef Var EFun

type EDefGroup = [EDef]

-- | An effect type that is assigned to a variable or constructor in the
-- environment
data EffectAssignment =
    -- | A type that is not effect-polymorphic
    MonoEffect EReturnType

    -- | An effect-polymorphic type.  The forall'd effect variables will be
    -- renamed to fresh variables each time the expression is instantiated.
  | PolyEffect [EVar] EReturnType

    -- | A recursively defined variable's effect
  | RecEffect {-# UNPACK #-}!PlaceholderRef EReturnType

-- | Create a monomorphic efect type for a function with the given parameters,
-- side effect, and return type.
funMonoEType :: [EParam] -> Effect -> EReturnType -> ERepType
funMonoEType params eff ret =
  case reverse params
  of [] -> internalError "funMonoEType: Nullary function"
     last_param:params' ->
       foldr add_param (make_function last_param) params'
  where
    make_function last_param =
      funT (paramParamType last_param is_mentioned) eff ret
      where
        is_mentioned =
          ret `mentionsT` paramVar last_param ||
          ret `mentionsT` paramVar last_param

    add_param param rng =
      funT (paramParamType param is_mentioned) emptyEffect (OwnRT $ discardTypeRepr rng)
      where
        is_mentioned = rng `mentionsT` paramVar param

-------------------------------------------------------------------------------
-- Coercions

-- | A coercion, which transforms one expression into another whose return
-- value is coerced to a different parameter passing convention.  The identity
-- coercion is represented as a distinct value.
newtype Coercion = Coercion (Maybe (EExp -> EExp))

instance Monoid Coercion where
  mempty = Coercion Nothing
  Coercion Nothing `mappend` c = c
  c `mappend` Coercion Nothing = c
  Coercion (Just f) `mappend` Coercion (Just g) = Coercion (Just (f . g))

coercion :: (EExp -> EExp) -> Coercion
coercion f = Coercion (Just f)

applyCoercion :: Coercion -> EExp -> EExp
applyCoercion (Coercion Nothing)  e = e
applyCoercion (Coercion (Just f)) e = f e

isIdCoercion :: Coercion -> Bool
isIdCoercion (Coercion Nothing) = True
isIdCoercion (Coercion _)       = False

-- | Create a coercion expression.
coercionExp :: (EReturnType -> EReturnType) -> (EExp -> EExp') -> Coercion
coercionExp rt t =
  Coercion $ Just $ \e -> EExp (expInfo e) (rt $ expReturn e) (t e)

-- | Coercions
genLoadValue, genTempLoadValue, genLoadOwned, genTempLoadOwned :: Coercion
genTempStoreValue, genTempStoreOwned :: RVar -> Coercion

genLoadValue = coercionExp coerce_return GenLoadValue
  where
    coerce_return (ReadRT _ t) = ValRT t
    coerce_return _ = internalError "genLoadValue"

genTempLoadValue = coercionExp coerce_return GenTempLoadValue
  where
    coerce_return (WriteRT _ t) = ValRT t
    coerce_return _ = internalError "genTempLoadValue"

genLoadOwned = coercionExp coerce_return GenLoadOwned
  where
    coerce_return (ReadRT _ t) = OwnRT t
    coerce_return _ = internalError "genLoadOwned"

genTempLoadOwned = coercionExp coerce_return GenTempLoadOwned
  where
    coerce_return (WriteRT _ t) = OwnRT t
    coerce_return _ = internalError "genTempLoadOwned"

genStoreValue rgn = coercionExp coerce_return GenStoreValue
  where
    coerce_return (ValRT t) = WriteRT rgn t
    coerce_return _ = internalError "genStoreValue"

genTempStoreValue rgn = coercionExp coerce_return GenTempStoreValue
  where
    coerce_return (ValRT t) = WriteRT rgn t
    coerce_return _ = internalError "genTempStoreValue"

genStoreOwned rgn = coercionExp coerce_return GenStoreOwned
  where
    coerce_return (OwnRT t) = WriteRT rgn t
    coerce_return _ = internalError "genStoreOwned"

genTempStoreOwned rgn = coercionExp coerce_return GenTempStoreOwned
  where
    coerce_return (OwnRT t) = WriteRT rgn t
    coerce_return _ = internalError "genTempStoreOwned"

-------------------------------------------------------------------------------
-- Evaluation of unified terms

forceEType :: EType -> IO EType
forceEType ty =
  case ty
  of AppT op args ->
       AppT `liftM` forceEType op `ap` mapM forceEType args
     InstT varcon effs -> InstT varcon `liftM` mapM evalEffect effs
     FunT pt eff rt ->
       FunT `liftM` forceEParamType pt `ap` evalEffect eff `ap`
       forceEReturnType rt
     VarT {} -> return ty
     ConT {} -> return ty
     LitT {} -> return ty

forceEParamType :: EParamType -> IO EParamType
forceEParamType pt =
  case pt
  of ValPT mv ty -> ValPT mv `liftM` forceEType ty
     OwnPT ty -> OwnPT `liftM` forceEType ty
     ReadPT v ty -> ReadPT `liftM` evalRVar v `ap` forceEType ty

forceEReturnType :: EReturnType -> IO EReturnType
forceEReturnType rt =
  case rt
  of ValRT ty -> ValRT `liftM` forceEType ty
     OwnRT ty -> OwnRT `liftM` forceEType ty
     ReadRT v ty -> ReadRT `liftM` evalRVar v `ap` forceEType ty
     WriteRT v ty -> WriteRT `liftM` evalRVar v `ap` forceEType ty

forceEParam (ValP v ty) = ValP v `liftM` forceEType ty
forceEParam (OwnP v ty) = OwnP v `liftM` forceEType ty
forceEParam (ReadP v rgn ty) = ReadP v `liftM` evalRVar rgn `ap` forceEType ty

forceEExp :: EExp -> IO EExp
forceEExp e = do
  rt <- forceEReturnType $ expReturn e
  e' <- force_exp $ expExp e
  case e' of
    Left placeholder_exp -> return placeholder_exp
    Right x -> return $ e {expReturn = rt, expExp = x}
  where
    -- A placeholder may be replaced by another expression
    force_exp expression@(RecPlaceholderE v ref) = do
           unassigned <- isEmptyMVar ref
           if unassigned
             then return $ Right expression
             else do new_exp <- forceEExp =<< readMVar ref
                     return $ Left new_exp

    force_exp expression = fmap Right $
      case expression
      of VarE {} -> return expression
         ConE {} -> return expression
         LitE l t -> LitE l `liftM` forceEType t
         TypeE t -> TypeE `liftM` forceEType t
         InstE op args -> InstE op `liftM` mapM evalEffect args
         CallE op args -> CallE `liftM` forceEExp op `ap` mapM forceEExp args
         FunE f -> FunE `liftM` forceEFun f
         DoE ty pc body -> DoE `liftM` forceEExp ty `ap` forceEExp pc `ap`
                           forceEExp body
         LetE lhs ty rhs body -> LetE lhs `liftM` forceEReturnType ty `ap`
                                 forceEExp rhs `ap` forceEExp body
         LetrecE defs body -> LetrecE `liftM` mapM forceEDef defs `ap`
                              forceEExp body
         CaseE scr alts -> CaseE `liftM` forceEExp scr `ap` mapM forceEAlt alts
         GenLoadValue e -> GenLoadValue `liftM` forceEExp e
         GenTempLoadValue e -> GenTempLoadValue `liftM` forceEExp e
         GenLoadOwned e -> GenLoadOwned `liftM` forceEExp e
         GenTempLoadOwned e -> GenTempLoadOwned `liftM` forceEExp e
         GenStoreValue e -> GenStoreValue `liftM` forceEExp e
         GenTempStoreValue e -> GenTempStoreValue `liftM` forceEExp e
         GenStoreOwned e -> GenStoreOwned `liftM` forceEExp e
         GenTempStoreOwned e -> GenTempStoreOwned `liftM` forceEExp e

forceEAlt (EAlt con ty_args params body) =
  EAlt con `liftM` mapM forceEType ty_args `ap` mapM forceEParam params `ap`
  forceEExp body

forceEFun fun = do
  params <- mapM forceEParam $ funParams fun
  rt <- forceEReturnType $ funReturnType fun
  eff <- evalEffect $ funEffect fun
  body <- forceEExp $ funBody fun
  return $ fun { funParams = params
               , funReturnType = rt
               , funEffect = eff
               , funBody = body
               }

-- | Force evaluation of unified expressions in the fields of a function 
-- that contribute to its type.  Evaluation is forced after generalization
-- so that instantiation works properly.
forceEFunTypeFields fun = do
  params <- mapM forceEParam $ funParams fun
  rt <- forceEReturnType $ funReturnType fun
  eff <- evalEffect $ funEffect fun
  return $ fun { funParams = params
               , funReturnType = rt
               , funEffect = eff
               }

forceEDef (EDef v f) = EDef v `liftM` forceEFun f

forceEDefTypeFields (EDef v f) = EDef v `liftM` forceEFunTypeFields f

-------------------------------------------------------------------------------
-- Pretty-printing

pprEExp :: EExp -> Doc
pprEExp e = pprEExp' (expExp e)

pprEExp' :: EExp' -> Doc
pprEExp' expression =
  case expression
  of VarE v -> Gluon.pprVar v
     ConE c -> text $ showLabel $ Gluon.conName c
     LitE l ty -> parens (SF.pprLit l <+> text ":" <+> pprEType ty)
     TypeE t -> parens (pprEType t)
     InstE c args ->
       let ctor = case c
                  of Left v -> Gluon.pprVar v
                     Right c -> text $ showLabel $ Gluon.conName c
       in parens $ sep $ ctor : map pprEffect args
     RecPlaceholderE v _ ->
       text "PLACEHOLDER" <+> braces (Gluon.pprVar v)
     CallE op args ->
       parens $ sep $ map pprEExp (op : args)
     FunE f -> pprEFun f
     DoE _ _ body ->
       text "do" <+> braces (pprEExp body)
     LetE lhs ty rhs body ->
       text "let" <+> (hang (Gluon.pprVar lhs <+> text ":" <+> pprEReturnType ty) 4 (pprEExp rhs)) $$
       pprEExp body
     LetrecE defs body ->
       text "letrec" $$ nest 4 (pprEDefs defs) $$ pprEExp body
     CaseE scr alts ->
       text "case" <+> pprEExp scr $$
       text "of" <+> vcat (map pprEAlt alts)
     GenLoadValue e ->
       text "LOAD_VALUE" <+> pprEExp e
     GenTempLoadValue e ->
       text "LOAD_TEMP_VALUE" <+> pprEExp e
     GenLoadOwned e ->
       text "LOAD_BOXED" <+> pprEExp e
     GenTempLoadOwned e ->
       text "LOAD_TEMP_BOXED" <+> pprEExp e
     GenStoreValue e ->
       text "STORE_VALUE" <+> pprEExp e
     GenTempStoreValue e ->
       text "STORE_TEMP_VALUE" <+> pprEExp e
     GenStoreOwned e ->
       text "STORE_BOXED" <+> pprEExp e
     GenTempStoreOwned e ->
       text "STORE_TEMP_BOXED" <+> pprEExp e

pprEParam :: EParam -> Doc
pprEParam param = parens $
  case param
  of ValP v t -> text "val" <+> Gluon.pprVar v <+> text ":" <+> pprEType t
     OwnP v t -> text "own" <+> Gluon.pprVar v <+> text ":" <+> pprEType t
     ReadP v r t -> text "bor" <+>
                    Gluon.pprVar v <> text "@" <> pprEffectVar r <+>
                    pprEType t

pprEAlt alt =
  let con = text $ showLabel $ Gluon.conName $ ealtCon alt
      args = map pprEType $ ealtTyArgs alt
      params = map pprEParam $ ealtParams alt
      body = pprEExp $ ealtBody alt
  in hang (sep (con : args ++ params) <> text ".") 4 body

pprEFun fun =
  let eparams =
        [pprEffectVar ev <+> text ": Effect" | ev <- funEffectParams fun]
      params = map pprEParam $ funParams fun
      rt = nest (-3) $ text "->" <+> pprEReturnType (funReturnType fun)
      eff = nest (-2) $ text "|" <+> pprEffect (funEffect fun)
      body = pprEExp $ funBody fun
      
      call = text "lambda" <+> sep (eparams ++ params ++ [rt, eff])
  in call <> text "." $$ nest 4 body

pprEDef (EDef v f) =
  Gluon.pprVar v <+> text "=" <+> pprEFun f

pprEDefs defs = vcat $ map pprEDef defs