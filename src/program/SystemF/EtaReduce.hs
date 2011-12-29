{-| A specialized eta reduction transformation, to undo superfluous parameters 
inserted by the output-passing transformation.

When we see a function of the form @\x. f x@, where @x@ is an application of
@OutPT@, remove the function parameter.  If that's the only parameter, then 
eliminate the function entirely.
-}

module SystemF.EtaReduce(etaExpandModule)
where

import Prelude hiding(mapM)
import Control.Applicative
import Data.Maybe
import qualified Data.Set as Set
import Data.Traversable

import Common.Error
import Builtins.Builtins
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.Rename
import qualified Type.Rename as Rename
import Type.Type
import Globals

-------------------------------------------------------------------------------
-- Eta expansion

-- | Perform eta expansion within an expression.
--   Find functions that can be eta expanded, and expand them.
etaExpandExp (ExpM expression) = ExpM <$>
  case expression
  of VarE {} -> return expression
     LitE {} -> return expression
     ConE inf con fields ->
       ConE inf con <$> mapM etaExpandExp fields
     AppE inf op ty_args args ->
       AppE inf <$>
       etaExpandExp op <*> pure ty_args <*> mapM etaExpandExp args
     LamE inf f -> LamE inf <$> etaExpandFun f
     LetE inf b rhs body ->
       LetE inf b <$> etaExpandExp rhs <*> etaExpandExp body
     LetfunE inf defs body ->
       LetfunE inf <$> mapM etaExpandDef defs <*> etaExpandExp body
     CaseE inf scr alts ->
       CaseE inf <$> etaExpandExp scr <*> mapM expand_alt alts
     ExceptE {} ->
       -- Eta expansion has to change the statement's return type
       internalError "etaExpandExp: Not implemented for exception statements"
     CoerceE inf from_t to_t b ->
       CoerceE inf from_t to_t <$> etaExpandExp b
  where
    expand_alt (AltM alt) = do
      body <- etaExpandExp $ altBody alt
      return $ AltM $ alt {altBody = body}

etaExpandFun (FunM f) =
  -- Does this function return a value whose type has the form
  -- @OutPtr t -> s@?
  case funReturn f
  of FunT ret_dom ret_rng ->
       case fromVarApp ret_dom
       of Just (op, [arg]) | op `isPyonBuiltin` The_OutPtr ->
            eta_expand ret_dom ret_rng
          _ -> no_eta_expand
     _ -> no_eta_expand
  where
    eta_expand param_type return_type = do
      -- Create a new parameter
      out_var <- newAnonymousVar ObjectLevel
      let new_param = patM (out_var ::: param_type)
            
      -- Eta-expand the function body.
      -- Apply the result to the parameter variable.
      body <- etaExpandExp $ funBody f
      let app_body = ExpM $ AppE defaultExpInfo body []
                     [ExpM $ VarE defaultExpInfo out_var]

      return $ FunM $ f { funParams = funParams f ++ [new_param]
                        , funReturn = return_type
                        , funBody   = app_body}

    no_eta_expand = do
      body <- etaExpandExp $ funBody f
      return $ FunM $ f {funBody = body}

etaExpandDef d = mapMDefiniens etaExpandFun d

etaExpandGlobalDef d = mapMDefiniens etaExpandEntity d

etaExpandEntity (FunEnt f) = FunEnt <$> etaExpandFun f
etaExpandEntity (DataEnt d) = return $ DataEnt d -- Contains no functions

etaExpandExport e = do
  f <- etaExpandFun $ exportFunction e
  return $ e {exportFunction = f}

-- | Find all function definitions that return an initializer function, and 
--   eta-expand them by adding a new parameter for the return pointer.
--   This transformation is performed once, immediately after representation
--   inference.  Eta-reduction may reverse some eta expansions later.
etaExpandModule :: Module Mem -> IO (Module Mem)
etaExpandModule (Module modname imports defss exports) =
  withTheNewVarIdentSupply $ \id_supply -> runFreshVarM id_supply make_module
  where 
    make_module = do
      defss' <- mapM (mapM etaExpandGlobalDef) defss
      exports' <- mapM etaExpandExport exports
      return $ Module modname imports defss' exports'