
module SystemF.PrintMemoryIR where

import Text.PrettyPrint.HughesPJ

import Common.Label
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Type

pprParenList xs = parens $ sep $ punctuate (text ",") xs

pprLit :: Lit -> Doc
pprLit (IntL n _) = text (show n)
pprLit (FloatL n _) = text (show n)

pprParamRepr repr =
  case repr
  of ValPT (Just v) -> text "val" <> braces (pprVar v) 
     ValPT Nothing -> text "val"
     BoxPT -> text "box"
     ReadPT -> text "read"
     WritePT -> text "write"
     OutPT -> text "out"
     SideEffectPT -> text "sideeffect"

pprReturnRepr repr =
  case repr
  of ValRT -> text "val"
     BoxRT -> text "box"
     ReadRT -> text "read"
     WriteRT -> text "write"
     OutRT -> text "out"
     SideEffectRT -> text "sideeffect"

pprParamType :: ParamType -> Doc
pprParamType (repr ::: ty) = pprParamRepr repr <+> pprType ty

pprReturnType (repr ::: ty) = pprReturnRepr repr <+> pprType ty

pprRet (RetM ret) = pprReturnType ret

pprTyPat :: TyPat Mem -> Doc
pprTyPat (TyPatM v t) = pprVar v <+> text ":" <+> pprType t

pprPat :: PatM -> Doc
pprPat (MemVarP v pt) = pprVar v <+> text ":" <+> pprParamType pt
pprPat (LocalVarP v t e) =
  text "local" <+> pprVar v <+> text ":" <+> pprType t <+> parens (pprExp e)

pprExp :: ExpM -> Doc
pprExp (ExpM expression) =
  case expression
  of VarE _ v -> pprVar v
     LitE _ l -> pprLit l
     AppE _ op ty_args args ->
       let op_doc = pprExp op
           ty_args_doc = [pprType t | TypM t <- ty_args]
           args_doc = map pprExp args
       in hang (pprExp op) 8 (pprParenList (ty_args_doc ++ args_doc))
     LamE _ f -> pprFun f
     LetE _ pat rhs body ->
       let pat_doc = pprPat pat
           rhs_doc = pprExp rhs
           body_doc = pprExp body
       in hang (pat_doc <+> text "=") 4 rhs_doc $$ body_doc
     LetrecE _ defs body ->
       let defs_doc = map pprDef defs
           body_doc = pprExp body
       in text "letrec" $$ nest 2 (vcat defs_doc) $$ body_doc
     CaseE _ scr alts ->
       text "case" <+> pprExp scr $$
       text "of" <+> vcat (map pprAlt alts)

pprAlt (AltM alt) =
  let con_doc = pprVar $ altConstructor alt
      args_doc = pprParenList [pprType t | TypM t <- altTyArgs alt]
      params_doc = map (parens . pprPat) $ altParams alt
      body_doc = pprExp $ altBody alt
  in con_doc <+> sep (args_doc : params_doc) <> text "." $$
     nest 2 body_doc

pprFun (FunM fun) =
  let ty_params_doc = map pprTyPat $ funTyParams fun
      params_doc = map pprPat $ funParams fun
      return_doc = pprRet $ funReturn fun
      body_doc = pprExp $ funBody fun
  in text "lambda" <+> sep [pprParenList (ty_params_doc ++ params_doc),
                            nest (-3) $ text "->" <+> return_doc] <> text "." $$
     nest 4 body_doc

pprDef (Def v f) = hang (pprVar v) 2 (pprFun f)

pprExport (Export _ _ f) =
  text "export" <+> pprFun f

pprModule (Module modname defs exports) =
  text "module" <+> text (showModuleName modname) $$
  vcat (map pprDef $ concat defs) $$
  vcat (map pprExport exports)