
module SystemF.Print
       (PrintFlags(..), defaultPrintFlags,
        pprLit, pprVar, pprPat, pprExp, pprFun, pprDef, pprModule,
        pprVarFlags, pprPatFlags, pprExpFlags, pprFunFlags, pprDefFlags
        )
where

import Data.Maybe
import Text.PrettyPrint.HughesPJ
import Gluon.Common.Identifier
import Gluon.Common.Label
import qualified Gluon.Core as Gluon
import qualified Gluon.Core.Print as Gluon
import SystemF.Builtins
import SystemF.Syntax

pprVar :: Var -> Doc
pprVar = pprVarFlags defaultPrintFlags

pprPat :: RPat -> Doc
pprPat = pprPatFlags defaultPrintFlags

pprExp :: RExp -> Doc
pprExp = pprExpFlags defaultPrintFlags

pprFun :: RFun -> Doc
pprFun = pprFunFlags defaultPrintFlags

pprDef :: RDef -> Doc
pprDef = pprDefFlags defaultPrintFlags

pprExport :: Export -> Doc
pprExport (Export _ v) = text "export" <+> pprVar v

pprModule :: RModule -> Doc
pprModule (Module defs exports) =
  vcat (map (braces . vcat . map pprDef) defs) $$
  vcat (map pprExport exports)

data PrintFlags =
  PrintFlags
  { printVariableIDs :: !Bool
  }

defaultPrintFlags =
  PrintFlags
  { printVariableIDs = True
  }

-- Helper function for printing tuple syntax
tuple :: [Doc] -> Doc
tuple xs = parens $ sep $ punctuate comma xs

pprVarFlags :: PrintFlags -> Var -> Doc
pprVarFlags flags v =
  let lab = case Gluon.varName v
            of Nothing -> text "_"
               Just label -> text (showLabel label)
      id = if printVariableIDs flags || isNothing (Gluon.varName v)
           then text $ '\'' : show (fromIdent $ Gluon.varID v)
           else empty
  in lab <> id

pprLit (IntL n) = text (show n)
pprLit (FloatL f) = text (show f)
pprLit (BoolL b) = text (show b)
pprLit NoneL = text "None"

pprPatFlags :: PrintFlags -> RPat -> Doc
pprPatFlags flags pat = 
  case pat
  of WildP ty  -> text "_" <+> colon <+> Gluon.pprExp ty
     VarP v ty -> pprVarFlags flags v <+> colon <+> Gluon.pprExp ty
     TupleP ps -> tuple $ map (pprPatFlags flags) ps

pprTyPatFlags :: PrintFlags -> RTyPat -> Doc
pprTyPatFlags flags (TyPat v ty) =
  Gluon.pprVar v <+> colon <+> Gluon.pprExp ty

pprBinderFlags :: PrintFlags -> Gluon.RBinder () -> Doc
pprBinderFlags flags (Gluon.Binder v ty ()) =
  pprVarFlags flags v <+> colon <+> Gluon.pprExp ty

pprExpFlags :: PrintFlags -> RExp -> Doc
pprExpFlags flags expression = pprExpFlagsPrec flags precOuter expression

-- Precedences for expression printing.
-- If an expression has precedence P, and it's shown in a context with
-- precedence Q > P, then it needs parentheses.
parenthesize prec doc context
  | context > prec = parens doc
  | otherwise      = doc

precOuter = 0                   -- Outermost precedence; commas; parentheses
precTyAnnot = 1                 -- Type annotation (x : t)
precTyApp = 10                  -- Type application (f @ x)
precApp = 10                    -- Application (f x)

pprTypeAnnotation :: Doc -> Doc -> Int -> Doc
pprTypeAnnotation val ty context = 
  parenthesize precTyAnnot (val <+> colon <+> ty) context

pprExpFlagsPrec :: PrintFlags -> Int -> RExp -> Doc
pprExpFlagsPrec flags prec expression =
  case expression
  of VarE {expVar = v} ->
         pprVarFlags flags v
     ConE {expCon = c} ->
         text (showLabel $ Gluon.conName c)
     LitE {expLit = l, expType = t} ->
         pprTypeAnnotation (pprLit l) (Gluon.pprExp t) prec
     TyAppE {expOper = e, expTyArg = t} ->
         let eDoc = pprExpFlagsPrec flags precTyApp e
             tDoc = Gluon.pprExp t
             doc = eDoc <+> text "@" <> tDoc
         in parenthesize precTyApp doc prec
     CallE {expOper = e, expArgs = es} ->
         let args = tuple $ map (pprExpFlagsPrec flags precOuter) es
             oper = pprExpFlagsPrec flags precApp e
         in sep [oper, nest 4 args]
     FunE {expFun = f} ->
         pprFunFlags flags f
     LetE {expBinder = pat, expValue = rhs, expBody = body} ->
         let e1 = hang (pprPatFlags flags pat <+> equals) 2
                  (pprExpFlags flags rhs)
             e2 = pprExpFlags flags body
         in text "let" <+> e1 $$ e2
     LetrecE {expDefs = ds, expBody = body} ->
         let defsText = vcat $ map (pprDefFlags flags) ds
             e = pprExpFlags flags body
         in text "letrec" $$ nest 2 defsText $$ text "in" <+> e
     CaseE {expScrutinee = e, expAlternatives = [alt1, alt2]} 
         | altConstructor alt1 == pyonBuiltin the_True &&
           altConstructor alt2 == pyonBuiltin the_False ->
             pprIf flags e (altBody alt1) (altBody alt2)
         | altConstructor alt2 == pyonBuiltin the_True &&
           altConstructor alt1 == pyonBuiltin the_False ->
             pprIf flags e (altBody alt2) (altBody alt1)
     CaseE {expScrutinee = e, expAlternatives = alts} ->
       let doc = text "case" <+> pprExpFlagsPrec flags precOuter e $$
                 text "of" <+> vcat (map (pprAltFlags flags) alts)
       in parenthesize precOuter doc prec

pprIf flags cond tr fa =
  let condText = pprExpFlags flags cond
      trText = pprExpFlags flags tr
      faText = pprExpFlags flags fa
  in text "if" <+> condText $$
     text "then" <+> trText $$
     text "else" <+> faText


pprAltFlags :: PrintFlags -> Alt Rec -> Doc
pprAltFlags flags (Alt { altConstructor = c
                       , altTyArgs = ty_args
                       , altParams = params
                       , altBody = body
                       }) =
  let ty_args_doc = map (text "@" <>) $ map Gluon.pprExp ty_args
      params_doc = map (parens . pprBinderFlags flags) params
      pattern =
        text (showLabel $ Gluon.conName c) <+> hsep (ty_args_doc ++ params_doc)
      body_doc = pprExpFlagsPrec flags precOuter body 
  in hang (pattern <> text ".") 2 body_doc

-- UTF-8 for lowercase lambda
lambda = text [toEnum 0xCE, toEnum 0xBB]

-- Print the function parameters, as they would appear in a lambda expression
-- or function definition.
pprFunParameters :: Bool -> PrintFlags -> RFun -> Doc
pprFunParameters isLambda flags fun = sep param_doc
  where
    param_doc =
      -- Type parameters
      map ty_param (funTyParams fun) ++
      -- Value parameters
      map (parens . pprPatFlags flags) (funParams fun) ++
      -- Return type
      [introduce_return_type $ Gluon.pprExp (funReturnType fun)]

    introduce_return_type t
      | isLambda  = nest (-3) $ text "->" <+> t
      | otherwise = nest (-2) $ colon <+> t

    ty_param p = text "@" <> parens (pprTyPatFlags flags p)

pprFunFlags :: PrintFlags -> RFun -> Doc
pprFunFlags flags fun =
  let params = pprFunParameters True flags fun
      body = pprExpFlags flags $ funBody fun
  in hang (lambda <+> params <> text ".") 4 body

pprDefFlags flags (Def v fun) =
  let params = pprFunParameters False flags fun
      body = pprExpFlags flags $ funBody fun
  in hang (pprVarFlags flags v <+> params <+> equals) 4 body