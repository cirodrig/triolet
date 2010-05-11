
module Pyon.Anf.Print
       (pprVal, pprStm, pprProc, pprModule)
where

import Text.PrettyPrint.HughesPJ

import Gluon.Common.Label
import Gluon.Core
import Pyon.Anf.Syntax

type Prec = Int
type PrecDoc = Prec -> Doc

-- Precedence values
prec_OUTER = 0
prec_APP   = 10

parenthesize :: Prec -> Doc -> PrecDoc
parenthesize prec doc context
  | prec >= context = doc
  | otherwise       = parens doc

infix 8 ##, #+

-- | Demand a precedence at least as great as that of the current context 
-- from the document
(##) :: Prec -> PrecDoc -> Doc
n ## pd = pd n

-- | Demand a precedence greater than that of the current context
(#+) :: Prec -> PrecDoc -> Doc
n #+ pd = pd (succ n)

-- | Format a curly-brace delimited block
block :: [Doc] -> Doc
block (line:lines) =
  vcat $ (text "{" <+> line : map (semi <+>) lines) ++ [text "}"]


-------------------------------------------------------------------------------

pprModule :: Module Rec -> Doc
pprModule (Module defss) =
  vcat $ map (block . map pprDef) defss

pprVal :: RVal -> Doc
pprVal v = prec_OUTER ## pprValPrec v

pprStm :: RStm -> Doc
pprStm s = prec_OUTER ## pprStmPrec s

pprValPrec :: RVal -> PrecDoc
pprValPrec val =
  case val
  of GluonV {valGluonTerm = e} ->
       \_ -> parens $ pprExp e
     AppV {valOper = op, valArgs = args} ->
       let op_doc = prec_APP ## pprValPrec op
           args_doc = vcat $ map (prec_APP #+) $ map pprValPrec args
       in parenthesize prec_APP $ op_doc <+> args_doc
     LamV {valProc = proc} -> \_ -> parens $ pprProc proc

pprStmPrec :: RStm -> PrecDoc
pprStmPrec statement =
  case statement
  of ReturnS {stmVal = val} ->
       parenthesize prec_OUTER $
       text "return" <+> pprVal val
     CallS {stmVal = val} ->
       pprValPrec val
     CaseS {stmScrutinee = scr, stmAlts = alts} | length alts /= 1 ->
       let alts_doc = map pprAlt alts
       in parenthesize prec_OUTER $
          text "case" <+> pprVal scr $$
          text "of" <+> vcat alts_doc
     
     -- Print other statements in block format
     _ -> \_ -> pprStmBlock statement

pprStmBlock :: RStm -> Doc
pprStmBlock stm = block $ pprMultilineStatement stm

pprMultilineStatement :: RStm -> [Doc]
pprMultilineStatement statement =
  case statement
  of LetS {stmBinder = binder, stmStm = stm1, stmBody = stm2} ->
       let binder_doc = pprBinder binder
           doc1 = prec_OUTER ## pprStmPrec stm1
       in hang (binder_doc <+> text "=") 4 doc1 : pprMultilineStatement stm2
     LetrecS {stmDefs = defs, stmBody = stm2} ->
       let defs_doc = vcat $ map pprDef defs
       in (text "letrec" $$ nest 4 defs_doc) : pprMultilineStatement stm2
     CaseS {stmScrutinee = scr, stmAlts = [alt]} ->
       let match_doc = hang (pprAltPattern alt <+> text "<-") 4 (pprVal scr)
       in match_doc : pprMultilineStatement (altBody alt)
     _ -> [prec_OUTER ## pprStmPrec statement]

pprAltPattern :: RAlt -> Doc
pprAltPattern alt =
  let con_doc = text $ showLabel $ conName $ altConstructor alt
      params_doc = sep $ map parens $ map pprBinder $ altParams alt
  in con_doc <+> params_doc

pprAlt :: RAlt -> Doc
pprAlt alt =
  hang (pprAltPattern alt <> text ".") 4 (pprStm $ altBody alt)

-- | Print the parameters, return type, and effect type of a procedure
pprProcSignature :: RProc -> Doc
pprProcSignature proc =
  let params_doc = map parens $ map pprBinder $ procParams proc
      return_doc = pprExp (procReturnType proc)
      effect_doc = pprExp (procEffectType proc)
  in cat (params_doc ++ [ nest (-3) $ text "->" <+> return_doc
                        , nest (-2) $ text "|" <+> effect_doc
                        ])

-- | Print a procedure as a lambda function
pprProc :: RProc -> Doc
pprProc proc =
  text "lambda" <+> pprProcSignature proc <> text "." $$
  nest 4 (pprStm $ procBody proc)

pprDef :: ProcDef Rec -> Doc
pprDef (ProcDef v proc) =
  pprVar v <+> pprProcSignature proc <+> text "=" $$
  nest 4 (pprStm $ procBody proc)

pprBinder :: RBinder () -> Doc
pprBinder (Binder v ty ()) = pprVar v <+> colon <+> pprExp ty