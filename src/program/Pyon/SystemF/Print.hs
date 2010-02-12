
module Pyon.SystemF.Print
       (PrintFlags(..), defaultPrintFlags,
        pprVar, pprPat, pprExp, pprFun, pprDef, pprModule,
        pprVarFlags, pprPatFlags, pprExpFlags, pprFunFlags, pprDefFlags
        )
where

import Data.Maybe
import Text.PrettyPrint.HughesPJ
import Gluon.Common.Identifier
import Gluon.Common.Label
import qualified Gluon.Core as Gluon
import qualified Gluon.Core.Print as Gluon
import Pyon.SystemF.Syntax

pprVar :: Var -> Doc
pprVar = pprVarFlags defaultPrintFlags

pprPat :: Pat -> Doc
pprPat = pprPatFlags defaultPrintFlags

pprExp :: Exp -> Doc
pprExp = pprExpFlags defaultPrintFlags

pprFun :: Fun -> Doc
pprFun = pprFunFlags defaultPrintFlags

pprDef :: Def -> Doc
pprDef = pprDefFlags defaultPrintFlags

pprModule :: Module -> Doc
pprModule (Module defs) = vcat $ map pprDef defs

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
  let lab = case varName v
            of Nothing -> text "_"
               Just label -> text (showLabel label)
      id = if printVariableIDs flags || isNothing (varName v)
           then text $ '\'' : show (fromIdent $ varID v)
           else empty
  in lab <> id

pprLit (IntL n) = text (show n)
pprLit (FloatL f) = text (show f)
pprLit (BoolL b) = text (show b)
pprLit NoneL = text "None"

pprPatFlags :: PrintFlags -> Pat -> Doc
pprPatFlags flags pat = 
  case pat
  of WildP ty  -> text "_" <+> colon <+> Gluon.pprExp ty
     VarP v ty -> pprVarFlags flags v <+> colon <+> Gluon.pprExp ty
     TupleP ps -> tuple $ map (pprPatFlags flags) ps

pprTyPatFlags :: PrintFlags -> TyPat -> Doc
pprTyPatFlags flags (TyPat v ty) =
  Gluon.pprVar v <+> colon <+> Gluon.pprExp ty

pprExpFlags :: PrintFlags -> Exp -> Doc
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

pprExpFlagsPrec :: PrintFlags -> Int -> Exp -> Doc
pprExpFlagsPrec flags prec expression =
  case expression
  of VarE {expVar = v} ->
         pprVarFlags flags v
     ConE {expCon = c} ->
         text (showLabel $ Gluon.conName c)
     LitE {expLit = l, expType = t} ->
         pprTypeAnnotation (pprLit l) (Gluon.pprExp t) prec
     UndefinedE {expType = t} ->
         pprTypeAnnotation (text "_") (Gluon.pprExp t) prec
     TupleE {expFields = ts} ->
         tuple $ map (pprExpFlagsPrec flags precOuter) ts
     TyAppE {expOper = e, expTyArg = t} ->
         let eDoc = pprExpFlagsPrec flags precTyApp e
             tDoc = Gluon.pprExp t
             doc = eDoc <+> text "@" <> tDoc
         in parenthesize precTyApp doc prec
     CallE {expOper = e, expArgs = es} ->
         let args = tuple $ map (pprExpFlagsPrec flags precOuter) es
             oper = pprExpFlagsPrec flags precApp e
         in sep [oper, nest 4 args]
     IfE {expCond = cond, expTrueCase = tr, expFalseCase = fa} ->
         let condText = pprExpFlags flags cond
             trText = pprExpFlags flags tr
             faText = pprExpFlags flags fa
         in text "if" <+> condText $$
            text "then" <+> trText $$
            text "else" <+> faText
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
     DictE { expClass = cls
           , expType = ty
           , expSuperclasses = scs
           , expMethods = ms } ->
         let clsText = parens $ Gluon.pprExp ty
             scsText = tuple $ map (pprExpFlags flags) scs
             msText = tuple $ map (pprExpFlags flags) ms
         in text "dict" <> cat [clsText, scsText, msText]
     MethodSelectE { expClass = cls
                   , expType = ty
                   , expMethodIndex = index
                   , expArg = arg } ->
       let clsText = parens $ Gluon.pprExp ty
           indexText = parens $ text (show index)
           argText = parens $ pprExpFlags flags arg
       in text "method" <> cat [clsText, indexText, argText]

-- UTF-8 for lowercase lambda
lambda = text [toEnum 0xCE, toEnum 0xBB]

pprFunFlags :: PrintFlags -> Fun -> Doc
pprFunFlags flags fun =
  let params = map pprTyParam (funTyParams fun) ++
               [tuple $ map (pprPatFlags flags) (funParams fun)]
      body = pprExpFlags flags $ funBody fun
  in hang (lambda <+> sep params <> text ".") 4 body
  where
    pprTyParam p = text "@" <> parens (pprTyPatFlags flags p)

pprDefFlags flags (Def v fun) =
  let params = map pprTyParam (funTyParams fun) ++
               [tuple $ map (pprPatFlags flags) (funParams fun)]
      body = pprExpFlags flags $ funBody fun
  in hang (pprVarFlags flags v <+> sep params <+> equals) 4 body
  where
    pprTyParam p = text "@" <> parens (pprTyPatFlags flags p)
