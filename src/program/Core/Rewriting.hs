
{-# LANGUAGE FlexibleInstances, EmptyDataDecls, TypeFamilies #-}
module Core.Rewriting(rewrite)
where

import Prelude hiding(mapM)

import Control.Monad hiding(mapM)
import Data.IORef
import Data.Maybe
import Data.Traversable

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Gluon.Core.Level
import Gluon.Core(Rec, Var, Con, SynInfo, mkSynInfo, newAnonymousVariable)
import qualified Gluon.Core as Gluon
import qualified SystemF.Syntax as SF
import qualified SystemF.Builtins as SF
import Core.Syntax
import Globals

-- | Some effect types should be reconstructed, but we haven't implemented
--   that.  For those effect types, we use this.
unknown_effect :: RCType
unknown_effect = conCT (Gluon.builtin Gluon.the_EmpE)

data Rw

type RWVal = Value Rw
type RWType = CTypeOf Rw Rw
type RWCExp = CExpOf Rw Rw
type RWCFun = CFunOf Rw Rw
type RWCAlt = CAltOf Rw Rw

newtype instance Gluon.ExpOf Rw Rw = RWExp {fromRWExp :: Gluon.RExp}
newtype instance CTypeOf Rw Rw = RWType {fromRWType :: RCType}
newtype instance CFunOf Rw Rw = RWCFun {fromRWFun :: CFunOf Rec Rw}
newtype instance CAltOf Rw Rw = RWCAlt {fromRWCAlt :: CAltOf Rec Rw}

-- | Expressions that are handled by the rewriter are represented by
--   specific constructor terms.
data instance CExpOf Rw Rw =
    BindCall { rexpInfo   :: !SynInfo
             , bindCallEffect :: RCType 
             , bindCallProducedType :: RCType 
             , bindCallTransformedType :: RCType 
             , bindCallProducedRepr :: RWCExp 
             , bindCallTransformedRepr :: RWCExp 
             , bindCallProducer :: RWCExp 
             , bindCallTransformer :: RWCExp}
  | MapStreamCall { rexpInfo :: !SynInfo
                  , mapStreamCallEffect :: RCType
                  , mapStreamCallProducedType :: RCType
                  , mapStreamCallTransformedType :: RCType
                  , mapStreamCallProducedRepr :: RWCExp
                  , mapStreamCallTransformedRepr :: RWCExp
                  , mapStreamCallTransformer :: RWCExp
                  , mapStreamCallProducer :: RWCExp}
  | BuildListCall { rexpInfo :: !SynInfo
                  , buildListCallEffect :: RCType
                  , buildListCallType :: RCType
                  , buildListCallRepr :: RWCExp
                  , buildListCallProducer :: RWCExp
                  , buildListCallReturn :: RWCExp}
  | GenerateCall { rexpInfo :: !SynInfo
                 , generateCallEffect :: RCType
                 , generateCallType :: RCType
                 , generateCallRepr :: RWCExp
                 , generateCallCount :: RWCExp
                 , generateCallProducer :: RWCExp}
  | GenerateListCall { rexpInfo :: !SynInfo
                     , generateListCallEffect :: RCType
                     , generateListCallType :: RCType
                     , generateListCallRepr :: RWCExp
                     , generateListCallCount :: RWCExp
                     , generateListCallProducer :: RWCExp}
  | ReturnCall { rexpInfo :: !SynInfo
               , returnCallEffect :: RCType
               , returnCallType :: RCType
               , returnCallRepr :: RWCExp
               , returnCallFunction :: RWCExp}
  | OtherExp !(CExpOf Rec Rw)

mkRWVal :: Value Rec -> Value Rw
mkRWVal value =
  case value
  of ValueVarV v -> ValueVarV v
     OwnedVarV v -> OwnedVarV v
     ReadVarV addr v -> ReadVarV (RWExp addr) v
     WriteVarV addr v -> WriteVarV (RWExp addr) v
     ValueConV c -> ValueConV c
     OwnedConV c -> OwnedConV c
     LitV l -> LitV l
     TypeV t -> TypeV (RWType t)

mkRWLetBinder :: LetBinder Rec -> LetBinder Rw
mkRWLetBinder (ValB v) = ValB v
mkRWLetBinder (OwnB v) = OwnB v
mkRWLetBinder (LocalB a p) = LocalB a p
mkRWLetBinder (RefB a p) = RefB (RWExp a) p

mkRWParam :: CBind CParam Rec -> CBind CParam Rw
mkRWParam (param ::: ty) =
  let param' = case param
               of ValP v -> ValP v
                  OwnP v -> OwnP v
                  ReadP a p -> ReadP a p
  in param' ::: RWType ty

mkRWReturn :: CBind CReturn Rec -> CBind CReturn Rw
mkRWReturn (ret ::: ty) =
  let ret' = case ret
             of ValR -> ValR
                OwnR -> OwnR
                WriteR a p -> WriteR a p
                ReadR a p -> ReadR (RWExp a) p
  in ret' ::: RWType ty

mkRWCExp :: RCExp -> RWCExp
mkRWCExp expression =
  case unpackConAppE expression
  of Just (con, args, mrarg)
       | Just e <- mkRWCExpFromApplication inf con args mrarg -> e
     _ -> case expression
          of ValCE inf val ->
               OtherExp (ValCE inf (mkRWVal val))
             AppCE inf op args mrarg ->
               OtherExp $
               AppCE inf (mkRWCExp op) (map mkRWCExp args) (fmap mkRWCExp mrarg)
             LamCE inf f ->
               OtherExp $ LamCE inf (mkRWCFun f)
             LetCE inf (binder ::: lhs_type) rhs body ->
               let lhs_type' = RWType lhs_type
                   binder' = mkRWLetBinder binder
               in OtherExp $ LetCE inf (binder' ::: lhs_type') (mkRWCExp rhs) (mkRWCExp body)
             LetrecCE inf defs body ->
               OtherExp $ LetrecCE inf [CDef v (mkRWCFun f) | CDef v f <- defs] (mkRWCExp body)
             CaseCE inf scr alts ->
               OtherExp $ CaseCE inf (mkRWCExp scr) (map mkRWCAlt alts)
  where
    inf = cexpInfo expression

mkRWCExpFromApplication inf con args mrarg
  | con `SF.isPyonBuiltin` SF.the_oper_CAT_MAP,
    [ValCE {cexpVal = TypeV effect},
     ValCE {cexpVal = TypeV p_type},
     ValCE {cexpVal = TypeV t_type},
     producer_repr, transformer_repr, producer, transformer] <- args =
      expect_no_return_arg $ Just $
      BindCall { rexpInfo = inf
               , bindCallEffect = effect
               , bindCallProducedType = p_type
               , bindCallTransformedType = t_type
               , bindCallProducedRepr = mkRWCExp producer_repr
               , bindCallTransformedRepr = mkRWCExp transformer_repr
               , bindCallProducer = mkRWCExp producer
               , bindCallTransformer = mkRWCExp transformer}
  | con `SF.isPyonBuiltin` SF.the_fun_map_Stream,
    [ValCE {cexpVal = TypeV effect},
     ValCE {cexpVal = TypeV p_type},
     ValCE {cexpVal = TypeV t_type},
     p_repr, t_repr, transformer, producer] <- args =
      expect_no_return_arg $ Just $
      MapStreamCall { rexpInfo = inf
                    , mapStreamCallEffect = effect
                    , mapStreamCallProducedType = p_type
                    , mapStreamCallTransformedType = t_type
                    , mapStreamCallProducedRepr = mkRWCExp p_repr
                    , mapStreamCallTransformedRepr = mkRWCExp t_repr
                    , mapStreamCallTransformer = mkRWCExp transformer
                    , mapStreamCallProducer = mkRWCExp producer}
  | con `SF.isPyonBuiltin` SF.buildMember . SF.the_TraversableDict_list,
    [ValCE {cexpVal = TypeV effect},
     ValCE {cexpVal = TypeV val_type},
     val_repr, producer] <- args =
      Just $
      BuildListCall { rexpInfo = inf
                    , buildListCallEffect = effect
                    , buildListCallType = val_type
                    , buildListCallRepr = mkRWCExp val_repr
                    , buildListCallProducer = mkRWCExp producer
                    , buildListCallReturn = mkRWCExp rarg}
  | con `SF.isPyonBuiltin` SF.the_fun_generate,
    [ValCE {cexpVal = TypeV effect},
     ValCE {cexpVal = TypeV ty},
     repr, count, producer] <- args =
      expect_no_return_arg $ Just $
      GenerateCall { rexpInfo = inf
                   , generateCallEffect = effect
                   , generateCallType = ty
                   , generateCallRepr = mkRWCExp repr
                   , generateCallCount = mkRWCExp count
                   , generateCallProducer = mkRWCExp producer}
  | con `SF.isPyonBuiltin` SF.the_fun_return,
    [ValCE {cexpVal = TypeV effect},
     ValCE {cexpVal = TypeV ty},
     repr, f] <- args =
      expect_no_return_arg $ Just $
      ReturnCall { rexpInfo = inf
                 , returnCallEffect = effect
                 , returnCallType = ty
                 , returnCallRepr = mkRWCExp repr
                 , returnCallFunction = mkRWCExp f}
  | otherwise = Nothing
  where
    expect_no_return_arg k =
      case mrarg
      of Nothing -> k
         Just _ ->
           internalError "mkRWCExpFromApplication: Unexpected return argument"
    
    rarg =
      case mrarg
      of Just x -> x
         Nothing -> 
           internalError "mkRWCExpFromApplication: Expecting a return argument"

mkRWCAlt (CAlt inf con args params body) =
  let args' = map RWType args
      params' = map mkRWParam params
      body' = mkRWCExp body
  in RWCAlt $ CAlt inf con args' params' body'

mkRWCFun :: RCFun -> RWCFun
mkRWCFun (CFun inf params ret eff body) =
  let params' = map mkRWParam params
      ret' = mkRWReturn ret
      eff' = RWType eff
      body' = mkRWCExp body
  in RWCFun $ CFun inf params' ret' eff' body'

mkRWCModule :: CModule Rec -> CModule Rw
mkRWCModule mod =
  let defss = [[CDef v (mkRWCFun f) | CDef v f <- defs] | defs <- cmodDefs mod]
      exports = [CExport inf spec (mkRWCFun f)
                | CExport inf spec f <- cmodExports mod]
  in CModule { cmodName = cmodName mod
             , cmodDefs = defss
             , cmodExports = exports}

valRWCE inf val = OtherExp (ValCE inf val)
readPointerRWV inf addr ptr =
  valRWCE inf $ ReadVarV (RWExp $ Gluon.mkInternalVarE addr) ptr
writePointerRWV pos addr ptr =
  mkRWCExp $ writePointerRV pos (Gluon.mkInternalVarE addr) ptr
appRWCE inf op args rarg = OtherExp (AppCE inf op args rarg)

leaveRWVal :: Value Rw -> Value Rec
leaveRWVal value =
  case value
  of ValueVarV v -> ValueVarV v
     OwnedVarV v -> OwnedVarV v
     ReadVarV a p -> ReadVarV (fromRWExp a) p
     WriteVarV a p -> WriteVarV (fromRWExp a) p
     ValueConV v -> ValueConV v
     OwnedConV v -> OwnedConV v
     LitV l -> LitV l
     TypeV t -> TypeV (fromRWType t)

leaveRWBinder :: CBind LetBinder Rw -> CBind LetBinder Rec
leaveRWBinder (binder ::: ty) =
  let binder' = case binder
                of ValB v -> ValB v
                   OwnB v -> OwnB v
                   LocalB a p -> LocalB a p
                   RefB a p -> RefB (fromRWExp a) p
  in binder' ::: fromRWType ty

leaveRWCParam (param ::: ty) =
  let param' = case param
               of ValP v -> ValP v
                  OwnP v -> OwnP v
                  ReadP a v -> ReadP a v
  in param' ::: fromRWType ty
    
leaveRWCReturn (ret ::: ty) =
  let ret' = case ret
             of ValR -> ValR
                OwnR -> OwnR
                WriteR a p -> WriteR a p
                ReadR a v -> ReadR (fromRWExp a) v
  in ret' ::: fromRWType ty

leaveRWCExp :: RWCExp -> RCExp
leaveRWCExp expression =
  case expression
  of BindCall inf eff ptype ttype prepr trepr producer consumer ->
       rebuild_call inf (SF.pyonBuiltin SF.the_oper_CAT_MAP) 
       [eff, ptype, ttype] [prepr, trepr, producer, consumer]
       Nothing
     MapStreamCall inf eff ptype ttype prepr trepr transformer producer ->
       rebuild_call inf (SF.pyonBuiltin SF.the_fun_map_Stream)
       [eff, ptype, ttype] [prepr, trepr, transformer, producer]
       Nothing
     BuildListCall inf eff ty repr producer rarg ->
       rebuild_call inf (SF.pyonBuiltin $ SF.buildMember . SF.the_TraversableDict_list)
       [eff, ty] [repr, producer] (Just rarg)
     GenerateCall inf eff ty repr count producer ->
       rebuild_call inf (SF.pyonBuiltin SF.the_fun_generate)
       [eff, ty] [repr, count, producer] Nothing
     ReturnCall inf eff ty repr f ->
       rebuild_call inf (SF.pyonBuiltin SF.the_fun_return)
       [eff, ty] [repr, f] Nothing
     OtherExp (ValCE inf val) ->
       ValCE inf (leaveRWVal val)
     OtherExp (AppCE inf oper args rarg) ->
       AppCE inf (leaveRWCExp oper) (map leaveRWCExp args) (fmap leaveRWCExp rarg)
     OtherExp (LamCE inf f) ->
       LamCE inf (leaveRWCFun f)
     OtherExp (LetCE inf binder rhs body) ->
       LetCE inf (leaveRWBinder binder) (leaveRWCExp rhs) (leaveRWCExp body)
     OtherExp (LetrecCE inf defs body) ->
       LetrecCE inf [CDef v (leaveRWCFun f) | CDef v f <- defs] (leaveRWCExp body)
     OtherExp (CaseCE inf scr alts) ->
       CaseCE inf (leaveRWCExp scr) (map leaveRWCAlt alts)
  where
    -- Reconstruct an application from the parameters
    rebuild_call inf op types values mrarg =
      let types' = map (ValCE inf . TypeV) types 
          values' = map leaveRWCExp values
          mrarg' = fmap leaveRWCExp mrarg
      in AppCE inf (ValCE inf (OwnedConV op)) (types' ++ values') mrarg'

leaveRWCAlt (RWCAlt (CAlt inf con types params body)) =
  let types' = map fromRWType types
      params' = map leaveRWCParam params
      body' = leaveRWCExp body
  in CAlt inf con types' params' body'

leaveRWCFun (RWCFun (CFun inf params return eff body)) =
  let params' = map leaveRWCParam params
      return' = leaveRWCReturn return
      eff' = fromRWType eff
      body' = leaveRWCExp body
  in CFun inf params' return' eff' body'

leaveRWCModule mod =
  let defss = [[CDef v (leaveRWCFun f) | CDef v f <- defs]
              | defs <- cmodDefs mod]
      exports = [CExport inf spec (leaveRWCFun f)
                | CExport inf spec f <- cmodExports mod]
  in CModule { cmodName = cmodName mod
             , cmodDefs = defss
             , cmodExports = exports}

-------------------------------------------------------------------------------
-- The rewriting monad

data RWEnv =
  RWEnv { varIDSupply :: {-# UNPACK #-}!(IdentSupply Var)
        , somethingChangedFlag :: {-# UNPACK #-}!(IORef Bool)
        }

newtype RW a = RW {unRW :: RWEnv -> IO a}

-- | Run a rewriting.  Return a boolean to indicate whether anything was
--   rewritten.
runRW :: IdentSupply Var -> RW a -> IO (a, Bool)
runRW var_supply m = do
  change_flag <- newIORef False
  x <- unRW m (RWEnv var_supply change_flag)
  changed <- readIORef change_flag
  return (x, changed)

instance Functor RW where
  fmap f (RW g) = RW $ \env -> fmap f (g env)

instance Monad RW where
  return x = RW $ \_ -> return x
  m >>= k = RW $ \var_ids -> do x <- unRW m var_ids
                                unRW (k x) var_ids

instance Supplies RW (Ident Var) where
  fresh = RW $ \env -> supplyValue (varIDSupply env)

-- | Set a global flag indicating that something has been changed by a rewrite
--   rule.
somethingChanged :: RW ()
somethingChanged = RW $ \env -> writeIORef (somethingChangedFlag env) True

type Rewrite a = a -> RW a

-------------------------------------------------------------------------------

rewriteExp' expression =
  case expression
  of BindCall { rexpInfo = inf
              , bindCallEffect = eff
              , bindCallProducedType = ptype
              , bindCallTransformedType = ttype
              , bindCallProducedRepr = prepr
              , bindCallTransformedRepr = trepr
              , bindCallProducer = producer
              , bindCallTransformer = transformer} -> do
       producer' <- rewriteExp' producer
       transformer' <- rewriteExp' transformer
       let new_expr =
             expression { bindCallProducer = producer'
                        , bindCallTransformer = transformer'}
       fmap (fromMaybe new_expr) $
         rebuildMapStream' inf eff ptype ttype prepr trepr producer' transformer'
     MapStreamCall { rexpInfo = inf
                   , mapStreamCallEffect = eff
                   , mapStreamCallProducedType = ptype
                   , mapStreamCallTransformedType = ttype
                   , mapStreamCallProducedRepr = prepr
                   , mapStreamCallTransformedRepr = trepr
                   , mapStreamCallTransformer = transformer
                   , mapStreamCallProducer = producer} -> do
       producer' <- rewriteExp' producer
       transformer' <- rewriteExp' transformer
       let new_expr =
             expression { mapStreamCallProducer = producer'
                        , mapStreamCallTransformer = transformer'}
       fmap (fromMaybe new_expr) $
         rewriteMapStreamApp' inf eff ptype ttype prepr trepr producer' transformer'
     BuildListCall { rexpInfo = inf
                   , buildListCallEffect = eff
                   , buildListCallType = ty
                   , buildListCallRepr = repr
                   , buildListCallProducer = producer
                   , buildListCallReturn = ret} -> do
       producer' <- rewriteExp' producer
       ret' <- rewriteExp' ret
       let new_expr =
             expression { buildListCallProducer = producer'
                        , buildListCallReturn = ret'}
       fmap (fromMaybe new_expr) $
         rewriteBuildListApp' inf eff ty repr producer' ret'
     GenerateCall { rexpInfo = inf
                  , generateCallEffect = eff
                  , generateCallType = ty
                  , generateCallRepr = repr
                  , generateCallCount = count
                  , generateCallProducer = producer} -> do
       count' <- rewriteExp' count
       producer' <- rewriteExp' producer
       return $ expression { generateCallCount = count'
                           , generateCallProducer = producer'}
     GenerateListCall { rexpInfo = inf
                      , generateListCallEffect = eff
                      , generateListCallType = ty
                      , generateListCallRepr = repr
                      , generateListCallCount = count
                      , generateListCallProducer = producer} -> do
       count' <- rewriteExp' count
       producer' <- rewriteExp' producer
       return $ expression { generateListCallCount = count'
                           , generateListCallProducer = producer'}
     ReturnCall { rexpInfo = inf
                , returnCallEffect = eff
                , returnCallType = ty
                , returnCallRepr = repr
                , returnCallFunction = f} -> do
       f' <- rewriteExp' f
       return $ expression { returnCallFunction = f'}
     OtherExp expression' -> fmap OtherExp $ rewriteExp'' expression'

rewriteExp'' :: Rewrite (CExpOf Rec Rw)
rewriteExp'' expression =
  case expression
  of ValCE {} -> return expression
     AppCE inf op args rarg -> do
       op' <- rewriteExp' op
       args' <- mapM rewriteExp' args
       rarg' <- mapM rewriteExp' rarg
       return $ AppCE inf op' args' rarg'
     LamCE inf f -> do
       f' <- rewriteFun' f
       return $ LamCE inf f'
     LetCE inf binder rhs body -> do
       rhs' <- rewriteExp' rhs
       body' <- rewriteExp' body
       return $ LetCE inf binder rhs' body'
     LetrecCE inf defs body -> do
       defs' <- mapM rewriteDef' defs
       body' <- rewriteExp' body
       return $ LetrecCE inf defs' body'
     CaseCE inf scr alts -> do
       scr' <- rewriteExp' scr
       alts' <- mapM rewriteAlt' alts
       return $ CaseCE inf scr' alts'

rewriteAlt' :: Rewrite RWCAlt
rewriteAlt' (RWCAlt alt) = do
  body <- rewriteExp' $ caltBody alt
  return $ RWCAlt $ alt {caltBody = body}

rewriteFun' :: Rewrite RWCFun
rewriteFun' (RWCFun fun) = do
  body <- rewriteExp' $ cfunBody fun
  return $ RWCFun $ fun {cfunBody = body}

rewriteDef' :: Rewrite (CDef Rw)
rewriteDef' (CDef v f) = fmap (CDef v) (rewriteFun' f)

-- Rewrite applications of 'buildList'
rewriteBuildListApp' inf effect val_type val_repr producer rarg =
  case producer
  of GenerateCall { generateCallCount = generate_count
                  , generateCallProducer = generate_producer} ->
       return $ Just $ GenerateListCall inf effect val_type val_repr generate_count generate_producer
     _ -> return Nothing

-- Rewrite applications of 'mapStream'
rewriteMapStreamApp' inf eff p_type t_type p_repr t_repr transformer producer =
  case producer
  of GenerateCall { generateCallEffect = generate_effect
                  , generateCallCount = generate_count
                  , generateCallProducer = generate_producer} -> do
       fmap Just $
         rebuild_generate generate_effect generate_count generate_producer
     _ -> return Nothing
  where
    pos = getSourcePos inf

    -- Create a generate expression
    -- generate count (\i r. let tmp = f i tmp in g tmp r)
    rebuild_generate generate_effect generate_count generate_producer = do
      -- Variables for function arguments, temporary value, and return value
      index_var <- newAnonymousVariable ObjectLevel
      ret_addr <- newAnonymousVariable ObjectLevel
      ret_ptr <- newAnonymousVariable ObjectLevel
      tmp_addr <- newAnonymousVariable ObjectLevel
      tmp_ptr <- newAnonymousVariable ObjectLevel
      let produce_binder = LocalB tmp_addr tmp_ptr ::: RWType p_type
          produce_exp =
            appRWCE inf generate_producer [valRWCE inf (ValueVarV index_var)]
            (Just $ writePointerRWV pos tmp_addr tmp_ptr)
          transform_exp =
            appRWCE inf transformer [readPointerRWV inf tmp_addr tmp_ptr]
            (Just $ writePointerRWV pos ret_addr ret_ptr)
          new_generate_body =
            OtherExp $ LetCE { cexpInfo = inf
                             , cexpBinder = produce_binder
                             , cexpRhs = produce_exp
                             , cexpBody = transform_exp
                             }
          generate_fun =
            RWCFun $
            CFun { cfunInfo = inf
                 , cfunParams = [ValP index_var ::: RWType (conCT (SF.pyonBuiltin SF.the_int))]
                 , cfunReturn = WriteR ret_addr ret_ptr ::: RWType t_type
                 , cfunEffect = RWType unknown_effect
                 , cfunBody = new_generate_body}
      return $
        GenerateCall { rexpInfo = inf
                     , generateCallEffect = eff
                     , generateCallType = t_type
                     , generateCallRepr = t_repr
                     , generateCallCount = generate_count
                     , generateCallProducer = OtherExp $ LamCE inf generate_fun}

rebuildMapStream' inf eff p_type t_type p_repr t_repr producer transformer = do
  m_new_transformer <- make_new_transformer
  case m_new_transformer of
    Nothing -> return Nothing
    Just f -> return $ Just $
              MapStreamCall { rexpInfo = inf
                            , mapStreamCallEffect = eff
                            , mapStreamCallProducedType = p_type
                            , mapStreamCallTransformedType = t_type
                            , mapStreamCallProducedRepr = p_repr
                            , mapStreamCallTransformedRepr = t_repr
                            , mapStreamCallTransformer =
                              OtherExp $ LamCE inf f
                            , mapStreamCallProducer = producer}
  where
    pos = getSourcePos inf
    
    -- Deconstruct the transformer expression, which should be a function.
    -- Expect the body to be an application of 'return', else give up.
    -- Get the function used for returning and apply it to a newly created
    -- return argument.  Wrap the whole thing in a new function.
    make_new_transformer :: RW (Maybe RWCFun)
    make_new_transformer
      | OtherExp (LamCE inf (RWCFun trans_f)) <- transformer = do
        evaluator_var <- newAnonymousVariable ObjectLevel
        return_addr <- newAnonymousVariable ObjectLevel
        return_ptr <- newAnonymousVariable ObjectLevel
        let mevaluator = removeReturn' $ cfunBody trans_f
            [transformer_param] = cfunParams trans_f
        return $! case mevaluator
                  of Nothing -> Nothing
                     Just evaluator ->
                       Just $ make_transformer transformer_param
                              evaluator evaluator_var
                              return_addr return_ptr
      | otherwise = return Nothing
        
    make_transformer transformer_param evaluator evaluator_var return_addr return_ptr =
      let -- Generate the evaluator function
          evaluator_type =
            functionCT
            [ValPT Nothing ::: conCT (SF.pyonBuiltin SF.the_NoneType)]
            unknown_effect
            (WriteRT ::: t_type)
          evaluator_binder = OwnB evaluator_var :::
                             RWType (funCT evaluator_type)
                
          -- Apply the evaluator to arguments
          transform_call =
            appRWCE inf (valRWCE inf (OwnedVarV evaluator_var))
            [valRWCE inf (LitV SF.NoneL)]
            (Just $ mkRWCExp $ writePointerRV (getSourcePos inf)
             (Gluon.mkInternalVarE return_addr) return_ptr)
                
          transformer_body =
            OtherExp $ LetCE inf evaluator_binder evaluator transform_call
                  
      in RWCFun $ CFun { cfunInfo = inf
                       , cfunParams = [transformer_param]
                       , cfunReturn = WriteR return_addr return_ptr ::: RWType t_type
                       , cfunEffect = RWType unknown_effect
                       , cfunBody = transformer_body}

-- | Given an expression, try to remove an application of @return@ from its
--   result.  That is, if the expression's return value is @return a r e@ for 
--   some @e@, change the return value to be Just @e@.
--
--   We handle some simple cases: look through let/letrec/case.  Otherwise
--   give up.
removeReturn' :: RWCExp -> Maybe RWCExp
removeReturn' expression =
  case expression
  of ReturnCall {returnCallFunction = f} -> return f
     OtherExp (exp@(LetCE {cexpBody = body})) -> do
       body' <- removeReturn' body
       return $ OtherExp $ exp {cexpBody = body'}
     OtherExp (exp@(LetrecCE {cexpBody = body})) -> do
       body' <- removeReturn' body
       return $ OtherExp $ exp {cexpBody = body'}
     OtherExp (exp@(CaseCE {cexpAlternatives = alts})) -> do
       alts' <- mapM remove_alt_return alts
       return $ OtherExp $ exp {cexpAlternatives = alts'}
     _ -> Nothing
  where
    remove_alt_return (RWCAlt alt) = do
      body' <- removeReturn' (caltBody alt)
      return $ RWCAlt $ alt {caltBody = body'}

-------------------------------------------------------------------------------
-- Entry point

-- | Apply rewriting rules in a single pass through the module.
rewriteOnce :: CModule Rw -> RW (CModule Rw)
rewriteOnce mod = do
  defss' <- mapM (mapM rewriteDef') $ cmodDefs mod
  return $ mod {cmodDefs = defss'}

-- | Apply rewriting rules to a module as much as possible.
--
-- TODO: iterate per-function rather than globally
rewrite :: CModule Rec -> IO (CModule Rec)
rewrite mod = withTheVarIdentSupply $ \var_supply ->
  -- Keep rewriting until there are no more rewrite opportunitites
  let run_until_convergence x = do
        (x', changed) <- runRW var_supply $ rewriteOnce x
        if changed then run_until_convergence x' else return x'
  in do mod' <- run_until_convergence $ mkRWCModule mod
        return $ leaveRWCModule mod'
