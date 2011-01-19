{- | This module converts pattern matching to case statements before
-- parameter-passing convention specialization is run.
-} 

{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
module SystemF.ElimPatternMatching
       (eliminatePatternMatching)
where

import Prelude hiding(mapM)

import Control.Applicative
import Control.Monad hiding(mapM)
import Data.Traversable

import Gluon.Common.SourcePos
import Gluon.Common.Identifier
import Gluon.Common.Supply
import Gluon.Core(mkSynInfo)
import Gluon.Core.Level
import SystemF.Syntax
import Builtins.Builtins
import Type.Var
import Type.Type
import Globals
  
catEndo :: [a -> a] -> a -> a
catEndo fs x = foldr ($) x fs

-- | Convert all pattern matching to @case@ statements.  After conversion, 
-- the only patterns that remain are 'VarP' patterns.
eliminatePatternMatching :: RModule -> IO RModule
eliminatePatternMatching (Module module_name ds exports) =
  withTheNewVarIdentSupply $ \id_supply -> runPM id_supply $ do
    ds' <- mapM (mapM elimPMDef) ds
    return $ Module module_name ds' exports

-- | Get the type of a pattern
patternType :: RPat -> RType
patternType (WildP ty) = ty
patternType (VarP _ ty) = ty
patternType (TupleP ps) =
  let field_types = map (fromSFType . patternType) ps
      tuple_size = length ps
      tuple_con = pyonTupleTypeCon tuple_size
  in tuple_size `seq` SFType (varApp tuple_con field_types)

-- | The pattern matching elimination monad.  Run in IO so we can create new
-- variables
newtype PM a = PM (IdentSupply Var -> IO a)

instance Functor PM where
  fmap f (PM g) = PM (\s -> fmap f (g s))

instance Applicative PM where
  pure = return
  (<*>) = ap

instance Monad PM where
  return x = PM (\_ -> return x)
  PM m >>= k = PM (\supply -> do x <- m supply
                                 case k x of PM n -> n supply)

instance Supplies PM VarID where
  fresh = PM supplyValue

runPM supply (PM f) = f supply

-- | Create a new temporary variable
pmNewVar :: PM Var
pmNewVar = newAnonymousVar ObjectLevel

elimPMDef :: RDef -> PM RDef
elimPMDef (Def v f) = do f' <- elimPMFun f
                         return $ Def v f'

elimPMFun :: RFun -> PM RFun
elimPMFun fun@(Fun {funInfo = inf, funParams = params, funBody = body}) = do
  (params', transformer) <- elimPMPats (getSourcePos inf) params
  body' <- elimPMExp body
  return $ fun {funParams = params', funBody = transformer body'}

elimPMExp :: RExp -> PM RExp
elimPMExp expression =
  case expression
  of VarE {} -> return expression
     LitE {} -> return expression
     TyAppE inf op arg -> do
       op' <- elimPMExp op
       return $ TyAppE inf op' arg
     CallE inf op args ->
       CallE inf <$> elimPMExp op <*> traverse elimPMExp args
     FunE inf f -> FunE inf <$> elimPMFun f
     LetE { expInfo = inf
          , expBinder = pat
          , expValue = rhs
          , expBody = body} -> do
       -- Eliminate pattern-matching in the let expression
       (pat', transformer) <- elimPMPat (getSourcePos inf) pat
       rhs' <- elimPMExp rhs
       body' <- elimPMExp body
       return $ LetE { expInfo = inf
                     , expBinder = pat'
                     , expValue = rhs'
                     , expBody = transformer body'
                     }
     LetrecE inf defs body ->
       LetrecE inf <$> traverse elimPMDef defs <*> elimPMExp body
     CaseE inf scr alts ->
       CaseE inf <$> elimPMExp scr <*> traverse elimPMAlt alts

elimPMAlt :: RAlt -> PM RAlt
elimPMAlt alt = do
  body <- elimPMExp $ altBody alt
  return $ alt {altBody = body}

-- | Eliminate a pattern match.  Return a 'VarP' pattern and a transformation
-- on the code that uses the pattern-bound variables.
elimPMPat :: SourcePos -> RPat -> PM (RPat, RExp -> RExp)
elimPMPat _ pat@(WildP ty) = do
  -- Create a new variable for this pattern
  pat_var <- pmNewVar
  return (VarP pat_var ty, id)
  
elimPMPat _ pat@(VarP _ _) =
  -- No change
  return (pat, id)

elimPMPat pos pat@(TupleP ps) = do
  -- Eliminate sub-patterns
  (fields, transformer) <- elimPMPats pos ps
  let field_types = [t | VarP _ t <- fields]
  
  -- Create a new variable pattern to replace the tuple pattern 
  pat_var <- pmNewVar
  let new_pat_type = patternType pat
      new_pat = VarP pat_var new_pat_type
      tuple_size = length ps
  
  -- Create a 'case' statement for this pattern
  let transformer' code =
        let new_info = mkSynInfo pos ObjectLevel
            body = transformer code
            alt = Alt (pyonTupleCon tuple_size) field_types fields body
        in CaseE new_info (VarE new_info pat_var) [alt]

  return (VarP pat_var new_pat_type, transformer')

elimPMPats :: SourcePos -> [RPat] -> PM ([RPat], RExp -> RExp)
elimPMPats pos ps = do
  (ps', transformers) <- mapAndUnzipM (elimPMPat pos) ps
  return (ps', catEndo transformers)

