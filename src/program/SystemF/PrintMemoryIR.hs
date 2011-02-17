
module SystemF.PrintMemoryIR where

import Text.PrettyPrint.HughesPJ

import Common.PrecDoc
import Common.Label
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Type

pprParenList xs = parens $ sep $ punctuate (text ",") xs

pprLit :: Lit -> Doc
pprLit (IntL n _) = text (show n)
pprLit (FloatL n _) = text (show n)

pprParamRepr repr =
  let repr_word = pprParamReprWord repr
  in case repr
     of ValPT (Just v) -> repr_word <> braces (pprVar v) 
        _ -> repr_word

pprParamType :: ParamType -> Doc
pprParamType pt = unparenthesized $ pprParamTypePrec pt

pprParamTypePrec :: ParamType -> PrecDoc
pprParamTypePrec (repr ::: ty) =
  pprParamRepr repr <+> pprType ty `hasPrec` appPrec

pprReturnType rt = unparenthesized $ pprReturnTypePrec rt

pprReturnTypePrec (repr ::: ty) =
  pprReturnRepr repr <+> pprType ty `hasPrec` appPrec

pprRet (RetM ret) = pprReturnTypePrec ret

pprTyPat :: TyPat Mem -> Doc
pprTyPat (TyPatM v t) = pprVar v <+> text ":" <+> pprType t

pprPat :: PatM -> Doc
pprPat pat =
  case pat
  of MemVarP v pt uses -> 
       pprUses uses <+> pprVar v <+> text ":" <+> pprParamType pt
     MemWildP pt -> 
       text "_" <+> text ":" <+> pprParamType pt
     LocalVarP v t e uses ->
       text "local" <+> pprUses uses <+>
       pprVar v <+> text ":" <+> pprType t <+> parens (pprExp e)

pprUses One = text "[1]"
pprUses Many = empty

pprExp :: ExpM -> Doc
pprExp e = unparenthesized $ pprExpPrec e

pprExpPrec (ExpM expression) =
  case expression
  of VarE _ v -> hasAtomicPrec $ pprVar v
     LitE _ l -> hasAtomicPrec $ pprLit l
     AppE _ op ty_args args ->
       let op_doc = pprExpPrec op ?+ appPrec
           ty_args_doc = [pprTypePrec t ?+ outerPrec | TypM t <- ty_args]
           args_doc = [pprExpPrec arg ?+ outerPrec | arg <- args]
       in hang op_doc 8 (pprParenList (ty_args_doc ++ args_doc)) `hasPrec` appPrec
     LamE _ f -> pprFunPrec f
     LetE _ pat rhs body ->
       let pat_doc = pprPat pat
           rhs_doc = pprExpPrec rhs ?+ outerPrec
           body_doc = pprExpPrec body ?+ outerPrec
       in hang (pat_doc <+> text "=") 4 rhs_doc $$ body_doc `hasPrec` stmtPrec
     LetfunE _ defs body ->
       let defs_doc = map pprDef $ defGroupMembers defs
           body_doc = pprExp body
       in text "letfun" $$ nest 2 (vcat defs_doc) $$ body_doc
          `hasPrec` stmtPrec
     CaseE _ scr alts ->
       let case_doc = text "case" <+> pprExpPrec scr ? stmtPrec 
           of_doc = text "of" <+> vcat (map pprAlt alts)
       in case_doc $$ of_doc `hasPrec` stmtPrec

pprAlt (AltM alt) =
  let con_doc = pprVar $ altConstructor alt
      args_doc = pprParenList [pprType t | TypM t <- altTyArgs alt]
      ex_types_doc = map (parens . pprTyPat) $ altExTypes alt
      params_doc = map (parens . pprPat) $ altParams alt
      body_doc = pprExp $ altBody alt
  in con_doc <+> sep (args_doc : ex_types_doc ++ params_doc) <> text "." $$
     nest 2 body_doc

pprFun f = unparenthesized $ pprFunPrec f

pprFunPrec (FunM fun) =
  let ty_params_doc = map pprTyPat $ funTyParams fun
      params_doc = map pprPat $ funParams fun
      return_doc = pprRet (funReturn fun) ?+ funPrec
      body_doc = pprExpPrec (funBody fun) ? stmtPrec
      sig_doc = sep [pprParenList (ty_params_doc ++ params_doc),
                     nest (-3) $ text "->" <+> return_doc]
  in text "lambda" <+> sig_doc <> text "." $$ nest 4 body_doc
     `hasPrec` stmtPrec

pprDef (Def v f) = hang (pprVar v) 2 (pprFun f)

pprExport (Export _ _ f) =
  text "export" <+> pprFun f

pprModule (Module modname defs exports) =
  text "module" <+> text (showModuleName modname) $$
  vcat (map pprDef $ concatMap defGroupMembers defs) $$
  vcat (map pprExport exports)