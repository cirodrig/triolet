
module Pyon.SystemF.Print
       (PrintFlags(..), defaultPrintFlags,
        pprVar, pprPat, pprExp, pprFun, pprDef,
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

tuple :: [Doc] -> Doc
tuple xs = parens $ sep $ punctuate comma xs

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

data PrintFlags =
  PrintFlags
  { printVariableIDs :: !Bool
  }

defaultPrintFlags =
  PrintFlags
  { printVariableIDs = True
  }

pprVarFlags :: PrintFlags -> Var -> Doc
pprVarFlags flags v =
  let lab = case varName v
            of Nothing -> empty
               Just label -> text (showLabel label)
      id = if printVariableIDs flags || isNothing (varName v)
           then text $ '#' : show (fromIdent $ varID v)
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
pprExpFlags flags expression =
  case expression
  of VarE v -> pprVarFlags flags v
     ConE c -> text (showLabel $ Gluon.conName c)
     LitE l t -> parens $ pprLit l <+> colon <+> Gluon.pprExp t
     UndefinedE t -> text "_" <+> colon <+> Gluon.pprExp t
     TupleE ts -> tuple $ map (pprExpFlags flags) ts
     TyAppE e t -> parens $ pprExpFlags flags e <+> Gluon.pprExp t
     CallE e es -> let args = tuple $ map (pprExpFlags flags) es
                   in cat [pprExpFlags flags e, nest 4 args]
     IfE cond tr fa -> let condText = pprExpFlags flags cond
                           trText = pprExpFlags flags tr
                           faText = pprExpFlags flags fa
                       in text "if" <+> condText $$
                          text "then" <+> trText $$
                          text "else" <+> faText
     FunE f -> pprFunFlags flags f
     LetE pat rhs body -> let e1 = hang (pprPatFlags flags pat <+> equals) 2
                                        (pprExpFlags flags rhs)
                              e2 = pprExpFlags flags body
                          in text "let" <+> e1 $$ e2
     LetrecE ds body -> let defsText = vcat $ map (pprDefFlags flags) ds
                            e = pprExpFlags flags body
                        in text "letrec" $$ nest 2 defsText $$ text "in" <+> e
     DictE cls ty scs ms -> let clsText = Gluon.pprExp ty
                                scsText = tuple $ map (pprExpFlags flags) scs
                                msText = tuple $ map (pprExpFlags flags) ms
                            in text "dict" <> cat [clsText, scsText, msText]
     MethodSelectE cls ty index arg ->
       let clsText = Gluon.pprExp ty
           indexText = parens $ text (show index)
           argText = parens $ pprExpFlags flags arg
       in text "method" <> cat [clsText, indexText, argText]

-- UTF-8 for lowercase lambda
lambda = text [toEnum 0xCE, toEnum 0xBB]

pprFunFlags :: PrintFlags -> Fun -> Doc
pprFunFlags flags fun =
  let params = map (parens . pprTyPatFlags flags) (funTyParams fun) ++
               map (parens . pprPatFlags flags) (funParams fun)
      body = pprExpFlags flags $ funBody fun
  in hang (lambda <+> sep params <> text ".") 4 body

pprDefFlags flags (Def v fun) =
  let params = map (parens . pprTyPatFlags flags) (funTyParams fun) ++
               map (parens . pprPatFlags flags) (funParams fun)
      body = pprExpFlags flags $ funBody fun
  in hang (pprVarFlags flags v <+> sep params <+> equals) 4 body
