
{-# LANGUAGE FlexibleInstances #-}
module Core.Rewriting(rewrite)
where

import Prelude hiding(mapM)

import Control.Monad hiding(mapM)
import Data.IORef
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

rewriteExp :: Rewrite RCExp
rewriteExp expression =
  case expression
  of ValCE {} -> return expression
     AppCE inf op args rarg -> rewriteApp inf op args rarg
     LamCE inf f -> do
       f' <- rewriteFun f
       return $ LamCE inf f'
     LetCE inf binder rhs body -> do
       rhs' <- rewriteExp rhs
       body' <- rewriteExp body
       return $ LetCE inf binder rhs' body
     LetrecCE inf defs body -> do
       defs' <- mapM rewriteDef defs
       body' <- rewriteExp body
       return $ LetrecCE inf defs' body'
     CaseCE inf scr alts -> do
       scr' <- rewriteExp scr
       alts' <- mapM rewriteAlt alts
       return $ CaseCE inf scr' alts'

rewriteAlt :: Rewrite RCAlt
rewriteAlt alt = do
  body <- rewriteExp $ caltBody alt
  return $ alt {caltBody = body}

rewriteFun :: Rewrite RCFun
rewriteFun fun = do
  body <- rewriteExp $ cfunBody fun
  return $ fun {cfunBody = body}

rewriteDef :: Rewrite (CDef Rec)
rewriteDef (CDef v f) = fmap (CDef v) (rewriteFun f)

-- | Rewrite a function application.
--
-- The function application is checked against various patterns.  If it 
-- matches, it is rewritten to a different expression.  Otherwise,
-- subexpressions are rewritten, and no further changes are made.
rewriteApp :: SynInfo -> RCExp -> [RCExp] -> Maybe RCExp -> RW RCExp
rewriteApp inf op args mrarg = do
  args' <- mapM rewriteExp args 
  mrarg' <- mapM rewriteExp mrarg
  dispatch args' mrarg'
  where
    dispatch args' mrarg' =
      case op
      of ValCE {cexpVal = OwnedConV con}
           | con `SF.isPyonBuiltin` SF.the_oper_CAT_MAP ->
               -- Rewrite (m >>= \x -> return (f x))
               -- to      (mapStream f m)
               case args'
               of [ValCE {cexpVal = TypeV effect},
                   ValCE {cexpVal = TypeV p_type},
                   ValCE {cexpVal = TypeV t_type},
                   producer_repr, transformer_repr,
                   producer, transformer] ->
                    try_rewrite $
                    rebuildMapStream inf effect p_type t_type
                    producer_repr transformer_repr
                    producer transformer
                  _ -> default_rewrite
           | con `SF.isPyonBuiltin` SF.the_fun_map_Stream ->
               -- Rewrites for "mapStream"
               case args'
               of [ValCE {cexpVal = TypeV effect},
                   ValCE {cexpVal = TypeV p_type},
                   ValCE {cexpVal = TypeV t_type},
                   producer_repr, transformer_repr,
                   transformer, producer] ->
                    try_rewrite $
                    rewriteMapStreamApp inf effect p_type t_type
                    producer_repr transformer_repr
                    transformer producer
                  _ -> default_rewrite
           | con `SF.isPyonBuiltin` SF.buildMember . SF.the_TraversableDict_list ->
               -- Rewrites for "buildList"
               case args'
               of [ValCE {cexpVal = TypeV effect},
                   ValCE {cexpVal = TypeV val_type},
                   val_repr, producer] ->
                    case mrarg
                    of Just rarg ->
                         try_rewrite $
                         rewriteBuildListApp inf effect val_type val_repr
                         producer rarg
                       _ -> unexpected_return_type
                  _ -> default_rewrite
                     
         _ -> default_rewrite
      where
        unexpected_return_type =
          internalError "rewriteApp: Unexpected return representation"

        -- Attempt to apply a rewrite rule.  If it succeeds, record that a
        -- rewrite happened and return its result.  Otherwise, rebuild the 
        -- expression.
        try_rewrite m = m >>= check 
          where 
            check Nothing = default_rewrite
            check (Just x) = do somethingChanged
                                return x

        default_rewrite = do
          -- Default: just rewrite subexpressions
          op' <- rewriteExp op
          return $ AppCE inf op' args' mrarg'

-- | Deconstruct a constructor application term
unpackConAppE :: RCExp -> Maybe (Con, [RCExp], Maybe RCExp)
unpackConAppE expression =
  case expression
  of AppCE { cexpOper = ValCE {cexpVal = OwnedConV con}
           , cexpArgs = args
           , cexpReturnArg = mrarg} -> Just (con, args, mrarg)
     _ -> Nothing

-- Rewrite applications of 'buildList'
rewriteBuildListApp inf effect val_type val_repr producer rarg =
  case unpackConAppE producer
  of Just (con, args, mrarg)
       | con `SF.isPyonBuiltin` SF.the_fun_generate ->
           case args
           of [_, _, _, generate_count, generate_producer] ->
                return $ Just $
                rebuild_generate_list generate_count generate_producer
     _ -> return Nothing
  where
    pos = getSourcePos inf
    type_inf = mkSynInfo pos TypeLevel
    
    generate_list_op = ValCE inf $ OwnedConV $
                       SF.pyonBuiltin SF.the_fun_generateList

    rebuild_generate_list generate_count generate_producer =
      AppCE { cexpInfo = inf
            , cexpOper = generate_list_op
            , cexpArgs = [ValCE type_inf $ TypeV effect,
                          ValCE type_inf $ TypeV val_type,
                          val_repr, generate_count, generate_producer]
            , cexpReturnArg = Just rarg}

-- Rewrite applications of 'mapStream'
rewriteMapStreamApp inf effect p_type t_type p_repr t_repr transformer producer =
  case unpackConAppE producer
  of Just (con, args, mrarg)
       | con `SF.isPyonBuiltin` SF.the_fun_generate ->
           case args
           of [ValCE {cexpVal = TypeV generate_effect}, _, _,
               generate_count, generate_producer] -> do
                fmap Just $
                  rebuild_generate
                  generate_effect generate_count generate_producer
     _ -> return Nothing
  where
    pos = getSourcePos inf
    type_inf = Gluon.mkSynInfo pos TypeLevel
    generate_op = ValCE (mkSynInfo noSourcePos ObjectLevel) $
                  OwnedConV (SF.pyonBuiltin SF.the_fun_generate)

    -- Create a generate expression
    -- generate count (\i r. let tmp = f i tmp in g tmp r)
    rebuild_generate generate_effect generate_count generate_producer = do
      -- Variables for function arguments, temporary value, and return value
      index_var <- newAnonymousVariable ObjectLevel
      ret_addr <- newAnonymousVariable ObjectLevel
      ret_ptr <- newAnonymousVariable ObjectLevel
      tmp_addr <- newAnonymousVariable ObjectLevel
      tmp_ptr <- newAnonymousVariable ObjectLevel
      let produce_binder = LocalB tmp_addr tmp_ptr ::: p_type
          produce_exp =
            AppCE { cexpInfo = inf
                  , cexpOper = generate_producer
                  , cexpArgs = [ValCE inf (ValueVarV index_var)]
                  , cexpReturnArg = Just $ writePointerRV pos (Gluon.mkInternalVarE tmp_addr) tmp_ptr}
          transform_exp =
            AppCE { cexpInfo = inf
                  , cexpOper = transformer
                  , cexpArgs = [ValCE inf $ ReadVarV (Gluon.mkInternalVarE tmp_addr) tmp_ptr]
                  , cexpReturnArg = Just $ writePointerRV pos (Gluon.mkInternalVarE ret_addr) ret_ptr}
          new_generate_body = LetCE { cexpInfo = inf
                                    , cexpBinder = produce_binder
                                    , cexpRhs = produce_exp
                                    , cexpBody = transform_exp
                                    }
          generate_fun =
            CFun { cfunInfo = inf
                 , cfunParams = [ValP index_var ::: conCT (SF.pyonBuiltin SF.the_int)]
                 , cfunReturn = WriteR ret_addr ret_ptr ::: t_type
                 , cfunEffect = unknown_effect
                 , cfunBody = new_generate_body}
          generate_call =
            AppCE { cexpInfo = inf
                  , cexpOper = generate_op
                  , cexpArgs = [ValCE type_inf (TypeV effect),
                                ValCE type_inf (TypeV t_type),
                                t_repr, generate_count, LamCE inf generate_fun]
                  , cexpReturnArg = Nothing}
      return generate_call

-- Construct the expression
--
-- mapStream (\x r -> let f = consumer_body in f None r) producer
rebuildMapStream inf effect p_type t_type p_repr t_repr producer transformer = do
  m_new_transformer <- make_new_transformer
  case m_new_transformer of
    Nothing -> return Nothing
    Just f ->
      let args = [type_value effect, type_value p_type, type_value t_type,
                  p_repr, t_repr, LamCE inf f, producer]
      in return $ Just $ AppCE inf map_stream_oper args Nothing
  where
    pos = getSourcePos inf
    type_value t = ValCE (mkSynInfo pos TypeLevel) (TypeV t)
    
    map_stream_oper = ValCE (mkSynInfo noSourcePos ObjectLevel) $
                      OwnedConV $ SF.pyonBuiltin SF.the_fun_map_Stream
    
    -- Deconstruct the transformer expression, which should be a function.
    -- Expect the body to be an application of 'return', else give up.
    -- Get the function used for returning and apply it to a newly created
    -- return argument.  Wrap the whole thing in a new function.
    make_new_transformer :: RW (Maybe RCFun)
    make_new_transformer
      | LamCE inf trans_f <- transformer = do
        evaluator_var <- newAnonymousVariable ObjectLevel
        return_addr <- newAnonymousVariable ObjectLevel
        return_ptr <- newAnonymousVariable ObjectLevel
        let mevaluator = removeReturn $ cfunBody trans_f
            [transformer_param] = cfunParams trans_f
        return $! case mevaluator
                  of Nothing -> Nothing
                     Just evaluator ->
                       Just $ make_transformer transformer_param
                              evaluator evaluator_var
                              return_addr return_ptr
      | otherwise = return Nothing
      where
        make_transformer transformer_param evaluator evaluator_var return_addr return_ptr =
          let -- Generate the evaluator function
              evaluator_type =
                functionCT
                [ValPT Nothing ::: conCT (SF.pyonBuiltin SF.the_NoneType)]
                unknown_effect
                (WriteRT ::: t_type)
              evaluator_binder = OwnB evaluator_var ::: funCT evaluator_type
              
              -- Apply the evaluator to arguments
              transform_call =
                AppCE inf (ValCE inf (OwnedVarV evaluator_var))
                [ValCE inf (LitV SF.NoneL)]
                (Just $ writePointerRV (getSourcePos inf)
                        (Gluon.mkInternalVarE return_addr) return_ptr)
              
              transformer_body =
                LetCE inf evaluator_binder evaluator transform_call
                
          in CFun { cfunInfo = inf
                  , cfunParams = [transformer_param]
                  , cfunReturn = WriteR return_addr return_ptr ::: t_type
                  , cfunEffect = unknown_effect
                  , cfunBody = transformer_body}

-- | Given an expression, try to remove an application of @return@ from its
--   result.  That is, if the expression's return value is @return a r e@ for 
--   some @e@, change the return value to be Just @e@.
--
--   We handle some simple cases: look through let/letrec/case.  Otherwise
--   give up.
removeReturn :: RCExp -> Maybe RCExp
removeReturn expression =
  case expression
  of ValCE {} -> mzero
     AppCE { cexpOper = ValCE {cexpVal = OwnedConV op}
           , cexpArgs = [eff_arg, type_arg, repr_arg, f_arg]}
       | op `SF.isPyonBuiltin` SF.the_fun_return ->
           return f_arg
     AppCE {} -> mzero
     LamCE {} -> mzero
     LetCE {cexpBody = body} -> do
       body' <- removeReturn body
       return $ expression {cexpBody = body'}
     LetrecCE {cexpBody = body} -> do
       body' <- removeReturn body
       return $ expression {cexpBody = body'}
     CaseCE {cexpAlternatives = alts} -> do
       alts' <- mapM remove_alt_return alts
       return $ expression {cexpAlternatives = alts'}
  where
    remove_alt_return alt = do
      body' <- removeReturn $ caltBody alt
      return $ alt {caltBody = body'}

-------------------------------------------------------------------------------
-- Entry point

-- | Apply rewriting rules in a single pass through the module.
rewriteOnce :: CModule Rec -> RW (CModule Rec)
rewriteOnce mod = do
  defss' <- mapM (mapM rewriteDef) $ cmodDefs mod
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
  in run_until_convergence mod
