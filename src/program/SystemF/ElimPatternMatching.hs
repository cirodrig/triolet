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
eliminatePatternMatching :: Module SF -> IO (Module SF)
eliminatePatternMatching (Module module_name ds exports) =
  withTheNewVarIdentSupply $ \id_supply -> runPM id_supply $ do
    ds' <- mapM (mapM elimPMDef) ds
    return $ Module module_name ds' exports

-- | Get the type of a pattern
patternType :: PatSF -> Type
patternType (WildP ty) = ty
patternType (VarP _ ty) = ty
patternType (TupleP ps) =
  let field_types = map patternType ps
      tuple_size = length ps
      tuple_con = pyonTupleTypeCon tuple_size
  in varApp tuple_con field_types

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

elimPMDef :: Def SF -> PM (Def SF)
elimPMDef (Def v f) = do f' <- elimPMFun f
                         return $ Def v f'

elimPMFun :: FunSF -> PM FunSF
elimPMFun (FunSF fun@(Fun { funInfo = inf
                          , funParams = params
                          , funBody = body})) = do
  (params', transformer) <- elimPMPats (getSourcePos inf) params
  body' <- elimPMExp body
  return $ FunSF $ fun {funParams = params', funBody = transformer body'}

elimPMExp :: ExpSF -> PM ExpSF
elimPMExp expression =
  case fromExpSF expression
  of VarE {} -> return expression
     LitE {} -> return expression
     AppE inf op ty_args args -> do
       op' <- elimPMExp op 
       args' <- traverse elimPMExp args
       return $ ExpSF $ AppE inf op' ty_args args'
     LamE inf f -> do
       f' <- elimPMFun f
       return $ ExpSF $ LamE inf f'
     LetE { expInfo = inf
          , expBinder = pat
          , expValue = rhs
          , expBody = body} -> do
       -- Eliminate pattern-matching in the let expression
       (pat', transformer) <- elimPMPat (getSourcePos inf) pat
       rhs' <- elimPMExp rhs
       body' <- elimPMExp body
       return $ ExpSF $ LetE { expInfo = inf
                             , expBinder = pat'
                             , expValue = rhs'
                             , expBody = transformer body'
                             }
     LetrecE inf defs body -> do
       defs' <- traverse elimPMDef defs 
       body' <- elimPMExp body
       return $ ExpSF $ LetrecE inf defs' body'
     CaseE inf scr alts -> do
       scr' <- elimPMExp scr 
       alts' <- traverse elimPMAlt alts
       return $ ExpSF $ CaseE inf scr' alts'

elimPMAlt :: AltSF -> PM AltSF
elimPMAlt (AltSF alt) = do
  body <- elimPMExp $ altBody alt
  return $ AltSF $ alt {altBody = body}

-- | Eliminate a pattern match.  Return a 'VarP' pattern and a transformation
-- on the code that uses the pattern-bound variables.
elimPMPat :: SourcePos -> PatSF -> PM (PatSF, ExpSF -> ExpSF)
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
  let field_types = [TypSF t | VarP _ t <- fields]
  
  -- Create a new variable pattern to replace the tuple pattern 
  pat_var <- pmNewVar
  let new_pat_type = patternType pat
      new_pat = VarP pat_var new_pat_type
      tuple_size = length ps
  
  -- Create a 'case' statement for this pattern
  let transformer' code =
        let new_info = mkExpInfo pos
            body = transformer code
            alt = Alt (pyonTupleCon tuple_size) field_types fields body
        in ExpSF $ CaseE new_info (ExpSF $ VarE new_info pat_var) [AltSF alt]

  return (VarP pat_var new_pat_type, transformer')

elimPMPats :: SourcePos -> [PatSF] -> PM ([PatSF], ExpSF -> ExpSF)
elimPMPats pos ps = do
  (ps', transformers) <- mapAndUnzipM (elimPMPat pos) ps
  return (ps', catEndo transformers)

