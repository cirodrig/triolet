
module SystemF.PrintMemoryIR
       (pprLit,
        pprDmd,
        pprSpecificity,
        pprTypM,
        pprTyPat,
        pprPat,
        pprPatternMatch,
        pprExp,
        pprExpPrec,
        pprAlt,
        pprFun,
        pprFunPrec,
        pprDef,
        pprDefGroup,
        pprExport,
        pprModule
       )
where

import Text.PrettyPrint.HughesPJ

import Common.PrecDoc
import Common.Label
import SystemF.Demand
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Type

defIndent = 2
letIndent = 2
appIndent = 4
caseIndent = 6

pprParenList xs = parens $ sep $ punctuate (text ",") xs

pprTyArgs ts = [text "@" <> pprTypePrec t ?+ appPrec | t <- ts]
pprExTypeArgs ts = [text "&" <> pprTypePrec t ?+ appPrec | t <- ts]
pprExTypeBinders ts = [text "&" <> parens (pprVar v <+> text ":" <+> pprType t)
                      | (v ::: t) <- ts]


pprLit :: Lit -> Doc
pprLit (IntL n _) = text (show n)
pprLit (FloatL n _) = text (show n)

pprDmd :: Dmd -> Doc
pprDmd (Dmd m s) =
  text (showMultiplicity m) <> text ":" <> pprSpecificity s

pprSpecificity Used = text "U"
pprSpecificity Inspected = text "I"
pprSpecificity (Decond mono_type spcs) = 
  let type_doc =
        case mono_type
        of VarDeCon con ty_args ex_types ->
             let types_doc = pprTyArgs ty_args
                 ex_doc    = pprExTypeBinders ex_types
             in parens $ sep (pprVar con : types_doc ++ ex_doc)
           TupleDeCon ty_args ->
             let types_doc = [pprType t | t <- ty_args]
             in parens $ sep $ punctuate (text ",") types_doc
  in text "D" <> braces (type_doc <> text ":" <> cat (map pprSpecificity spcs))

pprSpecificity (Written spc) = text "W" <> pprSpecificity spc
pprSpecificity (Read (HeapMap m)) =
  text "R" <> parens (cat $ punctuate (text ",") cells)
  where
    cells = [text "()" <+> text "|->" <+> pprSpecificity s | (v, s) <- m]
pprSpecificity Unused = text "0"

pprTypM (TypM t) = pprType t

pprTyPat :: TyPat Mem -> Doc
pprTyPat (TyPatM (v ::: t)) = pprVar v <+> text ":" <+> pprType t

pprPat :: PatM -> Doc
pprPat (PatM (v ::: pt) uses) =
  brackets (pprDmd uses) <+> pprVar v <+> text ":" <+> pprType pt

pprExp :: ExpM -> Doc
pprExp e = unparenthesized $ pprExpPrec e

pprExpPrec (ExpM expression) =
  case expression
  of VarE _ v -> hasAtomicPrec $ pprVar v
     LitE _ l -> hasAtomicPrec $ pprLit l
     ConE _ (CInstM (VarCon op ty_args ex_types)) args ->
       let op_doc = text "<" <> pprVar op <> text ">"
           ty_args_doc = pprTyArgs ty_args
           ex_types_doc = pprExTypeArgs ex_types
           args_doc = [pprExpPrec arg ?+ appPrec | arg <- args]
       in hang op_doc appIndent (sep $ ty_args_doc ++ ex_types_doc ++ args_doc)
          `hasPrec` appPrec

     ConE _ (CInstM (TupleCon _)) args ->
       hasAtomicPrec $ pprParenList (map pprExp args)

     AppE _ op ty_args args ->
       let op_doc = pprExpPrec op ?+ appPrec
           ty_args_doc = [text "@" <> pprTypePrec t ?+ appPrec | TypM t <- ty_args]
           args_doc = [pprExpPrec arg ?+ appPrec | arg <- args]
       in hang op_doc appIndent (sep $ ty_args_doc ++ args_doc) `hasPrec` appPrec

     LamE _ f -> pprFunPrec f
     LetE _ pat rhs body ->
       let pat_doc = pprPat pat
           rhs_doc = pprExpPrec rhs ?+ outerPrec
           body_doc = pprExpPrec body ?+ outerPrec
       in hang (pat_doc <+> text "=") letIndent rhs_doc $$ body_doc `hasPrec` stmtPrec
     LetfunE _ defs body ->
       let defs_doc = pprDefGroup defs
           body_doc = pprExp body
       in text "letfun" <+> defs_doc $$ body_doc
          `hasPrec` stmtPrec
     CaseE _ scr [altm@(AltM alt)] ->
       let binder_doc = text "let" <+> pprPatternMatch altm <+> text "="
           scr_doc = pprExp scr
           body_doc = pprExp (altBody alt)
       in hang binder_doc caseIndent scr_doc $$ body_doc `hasPrec` stmtPrec
     CaseE _ scr alts ->
       let case_doc = text "case" <+> pprExpPrec scr ? stmtPrec 
           of_doc = text "of" <+> vcat (map pprAlt alts)
       in case_doc $$ of_doc `hasPrec` stmtPrec
     ExceptE _ rt ->
       text "except" <+> pprType rt `hasPrec` stmtPrec
     CoerceE _ from_t to_t body ->
       let coercion_doc = pprType (fromTypM from_t) <+> text "=>" <+> pprType (fromTypM to_t)
           b_doc = pprExp body
       in hang (text "coerce" <+> parens coercion_doc) letIndent b_doc `hasPrec` appPrec


pprPatternMatch (AltM (Alt (DeCInstM (VarDeCon con ty_args ex_types)) params _)) =
  let con_doc = pprVar con
      args_doc = pprTyArgs ty_args
      ex_types_doc = pprExTypeBinders ex_types
      params_doc = map (parens . pprPat) params
  in hang con_doc appIndent (sep $ args_doc ++ ex_types_doc ++ params_doc)

pprPatternMatch (AltM (Alt (DeCInstM (TupleDeCon _)) params _)) =
  pprParenList (map pprPat params)

pprAlt altm@(AltM alt) =
  hang (pprPatternMatch altm <> text ".") defIndent $
  pprExp (altBody alt)

pprFun f = unparenthesized $ pprFunPrec f

pprFunPrec (FunM fun) =
  let ty_params_doc = map pprTyPat $ funTyParams fun
      params_doc = map pprPat $ funParams fun
      return_doc = pprTypePrec (fromTypM $ funReturn fun) ?+ funPrec
      body_doc = pprExpPrec (funBody fun) ? stmtPrec
      sig_doc = sep [pprParenList (ty_params_doc ++ params_doc),
                     nest (-3) $ text "->" <+> return_doc]
  in hang (text "lambda" <+> sig_doc <> text ".") defIndent body_doc
     `hasPrec` stmtPrec

pprDef (Def v ann f) =
  hang (pprVar v <+> ann_doc <+> text "=") defIndent $
  pprFun f
  where
    ann_doc =
      let phase_doc =
            case defAnnInlinePhase ann
            of InlNormal -> empty
               x -> text (show x)
          inl_doc =
            if defAnnInlineRequest ann
            then text "inline"
            else empty
          join_doc =
            if defAnnJoinPoint ann
            then text "join_point"
            else empty
          uses_doc = text $ showMultiplicity (defAnnUses ann)
      in brackets $ sep $
         punctuate (text ",") $
         filter (not . isEmpty) [inl_doc, join_doc, phase_doc, uses_doc]

pprDefGroup :: DefGroup (Def Mem) -> Doc
pprDefGroup dg =
  case dg
  of NonRec _ -> text "nonrec {" $$ nest 2 members $$ text "}"
     Rec _ -> text "rec {" $$ nest 2 members $$ text "}"
  where
    members = vcat $ map pprDef $ defGroupMembers dg

pprExport (Export _ _ f) =
  text "export" <+> pprFun f

pprModule (Module modname imports defs exports) =
  text "module" <+> text (showModuleName modname) $$
  {-text "imports {" $$
  nest 2 (vcat (map pprDef imports)) $$
  text "}" $$-}
  vcat (map pprDefGroup defs) $$
  vcat (map pprExport exports)