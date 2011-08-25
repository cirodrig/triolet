{-| Annotated IR used for the local continuation-passing transformation.

The LCPS transformation reorganizes local functions in a way that
increases the number of functions that can be translated to local
procedures, which execute more efficiently than hoisted functions.

To perform the transformation, @let@-expressions must be labeled.
This module defines the labeled IR and insertion/removal of labels.

The LCPS transformation is described in the paper
\"Optimizing Nested Loops Using Local CPS Conversion\" by John Reppy,
in Proc. Higher-Order and Symbolic Computation 15, p. 161-180, 2002.
-}

module LowLevel.LocalCPSAnn where

import Prelude hiding(mapM)

import Control.Applicative hiding(empty)
import Control.Monad hiding(mapM, forM, join)
import Data.Traversable
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Maybe
import Data.Monoid
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import LowLevel.CodeTypes
import LowLevel.FreshVar
import LowLevel.Print
import LowLevel.Syntax
import Globals

-------------------------------------------------------------------------------

-- | A LCPS Statement.  This is like 'Stm' except that let-expressions are
--   annotated with a variable.  The variable stands for the body of the
--   let-expression; if the body is turned into a function, then that variable
--   becomes the function's name.
data LStm =
    LetLCPS [ParamVar] Atom !Var LStm
  | LetrecLCPS !(Group LFunDef) LStm
  | SwitchLCPS Val [LAlt]
  | ReturnLCPS Atom
  | ThrowLCPS Val

type LAlt = (Lit, LStm)
type LFunDef = Def LFun
type LFun = FunBase LStm

-- | Is the variable the name of a let-statement continuation from inside the
--   given expression?
containsLetContinuation :: LStm -> Var -> Bool
stm `containsLetContinuation` search_v = search stm
  where
    search (LetLCPS _ _ v s) = search_v == v || search s
    search (LetrecLCPS grp s) = any search_fun (groupMembers grp) || search s
    search (SwitchLCPS _ alts) = any (search . snd) alts
    search (ReturnLCPS _) = False
    search (ThrowLCPS _) = False
    
    search_fun (Def _ f) = search $ funBody f

annotateStm :: Stm -> FreshVarM LStm
annotateStm statement =
  case statement
  of LetE params rhs body -> do
       v <- newAnonymousVar (PrimType OwnedType)
       body' <- annotateStm body
       return $ LetLCPS params rhs v body'
     LetrecE defs body ->
       LetrecLCPS <$> traverse annotateFunDef defs <*> annotateStm body
     SwitchE scr alts ->
       SwitchLCPS scr <$> traverse do_alt alts
     ReturnE atom -> pure $ ReturnLCPS atom
     ThrowE val -> pure $ ThrowLCPS val
  where
    do_alt (k, stm) = (,) k <$> annotateStm stm

annotateFun :: Fun -> FreshVarM LFun
annotateFun f = changeFunBodyM annotateStm f

annotateFunDef :: FunDef -> FreshVarM LFunDef
annotateFunDef (Def v f) = Def v <$> annotateFun f

unAnnotate :: LStm -> Stm
unAnnotate statement =
  case statement
  of LetLCPS params rhs _ body -> LetE params rhs (unAnnotate body)
     LetrecLCPS defs body -> LetrecE (fmap do_def defs) (unAnnotate body)
     SwitchLCPS scr alts -> SwitchE scr (map do_alt alts)
     ReturnLCPS atom -> ReturnE atom
     ThrowLCPS val -> ThrowE val
  where
    do_def (Def v f) = Def v (unAnnotateFun f)
    do_alt (k, stm) = (k, unAnnotate stm)

unAnnotateFun :: LFun -> Fun
unAnnotateFun = changeFunBody unAnnotate

-------------------------------------------------------------------------------

pprLStm :: LStm -> Doc
pprLStm stmt = pprLabeledLStm empty stmt

-- | Pretty-print a statement, preceded by a label.  This code is a modified
--   version of 'pprStm'.
pprLabeledLStm :: Doc -> LStm -> Doc
pprLabeledLStm label stmt =
  case stmt
  of LetLCPS [] atom v body ->
       label <+> text "[] <-" <+> pprAtom atom $$
       pprLabeledLStm (pprVar v <+> text ":") body
     LetLCPS vars atom v body ->
       let binder = sep $ punctuate (text ",") $ map pprVarLong vars
           rhs = pprAtom atom
       in hang (label <+> binder <+> text "<-") 8 rhs $$
          pprLabeledLStm (pprVar v <+> text ":") body
     LetrecLCPS defs body ->
       label <+> text "let" <+> pprGroup pprLFunDef defs $$
       pprLStm body
     SwitchLCPS val alts ->
       label <+> text "switch" <> parens (pprVal val) $$
       nest 2 (vcat $ map print_alt alts)
     ReturnLCPS atom -> label <+> pprAtom atom
     ThrowLCPS val -> label <+> text "throw" <+> pprVal val
  where
    print_alt (lit, body) = hang (pprLit lit <> text ":") 6 (pprLStm body)

-- | Pretty-print a function definition.  This code is a modified
--   version of 'pprFunDef'.
pprLFunDef :: Def LFun -> Doc
pprLFunDef (Def v f) =
  let intro = if isPrimFun f then text "procedure" else text "function"
      uses = case funUses f
             of ZeroUses -> text "[0]"
                OneUse -> text "[1]"
                ManyUses -> empty
      inl = if funInlineRequest f then text "INLINE" else empty
      param_doc = map pprVarLong $ funParams f
      ret_doc = map pprValueType $ funReturnTypes f
      leader = pprVar v <> pprFunSignature param_doc ret_doc
      local_doc = if funFrameSize f == 0
                  then empty
                  else text "frame size:" <+> text (show $ funFrameSize f)
  in intro <+> uses <+> inl <+> leader <+> text "=" $$
     nest 4 local_doc $$
     nest 4 (pprLStm (funBody f))
