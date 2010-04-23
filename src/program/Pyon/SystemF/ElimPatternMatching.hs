{- | This module converts pattern matching to case statements before
-- parameter-passing convention specialization is run.
-} 
module Pyon.SystemF.ElimPatternMatching
       (eliminatePatternMatching)
where

import Control.Monad

import Gluon.Common.SourcePos
import qualified Gluon.Core as Gluon
import Pyon.Globals
import Pyon.SystemF.Syntax
import Pyon.SystemF.Builtins
  
catEndo :: [a -> a] -> a -> a
catEndo fs x = foldr ($) x fs

-- | Convert all pattern matching to @case@ statements.  After conversion, 
-- the only patterns that remain are 'VarP' patterns.
eliminatePatternMatching :: RModule -> IO RModule
eliminatePatternMatching (Module ds exports) = do
  ds' <- mapM (mapM elimPMDef) ds
  return $ Module ds' exports

-- | Get the type of a pattern
patternType :: RPat -> RType
patternType (WildP ty) = ty
patternType (VarP _ ty) = ty
patternType (TupleP ps) =
  let field_types = map patternType ps
      tuple_size = length ps
      tuple_con = getPyonTupleType' tuple_size
  in tuple_size `seq`
     Gluon.mkConAppE noSourcePos tuple_con field_types

-- | The pattern matching elimination monad.  Run in IO so we can create new
-- variables
type PM = IO

-- | Create a new temporary variable
pmNewVar :: PM Var
pmNewVar = do
  var_id <- getNextVarIdent
  return $ Gluon.mkAnonymousVariable var_id Gluon.ObjectLevel

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
  of LetE { expInfo = inf
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
     _ -> traverseSFExp elimPMExp elimPMFun return expression 

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
  let field_vars = [v | VarP v _ <- fields]
      field_types = [t | VarP _ t <- fields]
  
  -- Create a new variable pattern to replace the tuple pattern 
  pat_var <- pmNewVar
  let new_pat_type = patternType pat
      new_pat = VarP pat_var new_pat_type
      tuple_size = length ps
  
  -- Create a 'case' statement for this pattern
  let transformer' code =
        let new_info = Gluon.mkSynInfo pos Gluon.ObjectLevel
            body = transformer code
            alt = Alt (getPyonTupleCon' tuple_size) field_types field_vars body
        in CaseE new_info (VarE new_info pat_var) [alt]

  return (VarP pat_var new_pat_type, transformer')

elimPMPats :: SourcePos -> [RPat] -> PM ([RPat], RExp -> RExp)
elimPMPats pos ps = do
  (ps', transformers) <- mapAndUnzipM (elimPMPat pos) ps
  return (ps', catEndo transformers)

