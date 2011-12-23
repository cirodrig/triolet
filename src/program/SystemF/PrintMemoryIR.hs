
module SystemF.PrintMemoryIR
       (PprFlags(..),
        defaultPprFlags, briefPprFlags, tersePprFlags,
        pprLit,
        pprDmd,
        pprSpecificity,
        pprTyPat,
        pprPat,
        pprPatternMatch,
        pprExp,
        pprExpPrec,
        pprAlt,
        pprFun,
        pprFunPrec,
        pprFDef,
        pprFDefGroup,
        pprExport,
        pprModule,
        pprModuleFlags,
       )
where

import Text.PrettyPrint.HughesPJ

import Common.PrecDoc
import Common.Label
import SystemF.Demand
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Type

data PprFlags =
  PprFlags
  { -- | Include function type arguments in the output.
    --   Function type arguments can usually, but not always, be inferred
    --   from their value arguments.
    showTypeArguments :: !Bool

    -- | Include type annotations in the output even when the annotations 
    --   are redundant.
  , showInferableTypes :: !Bool

    -- | Include demand annotations in the pretty-printed output
  , showDemands :: !Bool
  }

defaultPprFlags = PprFlags True True True

briefPprFlags = PprFlags True True False

tersePprFlags = PprFlags False False False

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

pprTyPat :: TyPat -> Doc
pprTyPat (TyPat (v ::: t)) = pprVar v <+> text ":" <+> pprType t

pprPat :: PatM -> Doc
pprPat pat = pprPatFlags False defaultPprFlags pat

pprPatFlags inferable_type flags (PatM (v ::: pt) uses) =
  let demand_doc =
        if showDemands flags
        then brackets (pprDmd uses)
        else empty
      type_doc =
        if inferable_type && not (showInferableTypes flags)
        then empty
        else text ":" <+> pprType pt
  in demand_doc <+> pprVar v <+> type_doc

pprExp :: ExpM -> Doc
pprExp e = unparenthesized $ pprExpPrec e

pprExpPrec e = pprExpPrecFlags defaultPprFlags e

pprExpFlags f e = pprExpPrecFlags f e ? outerPrec

pprExpPrecFlags flags (ExpM expression) =
  case expression
  of VarE _ v -> hasAtomicPrec $ pprVar v
     LitE _ l -> hasAtomicPrec $ pprLit l
     ConE _ (VarCon op ty_args ex_types) args ->
       con op ty_args ex_types args `hasPrec` appPrec

     ConE _ (TupleCon _) args ->
       hasAtomicPrec $ pprParenList (map (pprExpFlags flags) args)

     AppE _ op ty_args args ->
       app op ty_args args `hasPrec` appPrec

     LamE _ f -> pprFunPrecFlags True flags f
     LetE _ pat rhs body ->
       let pat_doc = pprPatFlags True flags pat
           rhs_doc = continue rhs ? stmtPrec
           body_doc = continue body ? stmtPrec
       in hang (pat_doc <+> text "=") letIndent rhs_doc $$ body_doc
          `hasPrec` stmtPrec
     LetfunE _ defs body ->
       let defs_doc = pprFDefGroupFlags flags defs
           body_doc = continue body ? stmtPrec
       in text "letfun" <+> defs_doc $$ body_doc
          `hasPrec` stmtPrec
     CaseE _ scr [AltM alt] ->
       let binder_doc = text "let" <+> pprAltPatternFlags flags alt <+> text "="
           scr_doc = continue scr ? stmtPrec
           body_doc = continue (altBody alt) ? stmtPrec
       in hang binder_doc caseIndent scr_doc $$ body_doc `hasPrec` stmtPrec
     CaseE _ scr alts ->
       let case_doc = text "case" <+> continue scr ? stmtPrec 
           of_doc = text "of" <+> vcat (map (pprAltFlags flags) alts)
       in case_doc $$ of_doc `hasPrec` stmtPrec
     ExceptE _ rt ->
       text "except" <+> pprType rt `hasPrec` stmtPrec
     CoerceE _ from_t to_t body ->
       let coercion_doc = pprType from_t <+> text "=>" <+> pprType to_t
           b_doc = continue body ?+ appPrec
       in hang (text "coerce" <+> parens coercion_doc) letIndent b_doc
          `hasPrec` appPrec
  where
    continue e = pprExpPrecFlags flags e

    con op ty_args ex_types args =
      let op_doc = text "<" <> pprVar op <> text ">"
          ty_args_doc = pprTyArgs ty_args
          ex_types_doc = pprExTypeArgs ex_types
          args_doc = [continue arg ?+ appPrec | arg <- args]
          visible_args_doc =
            if showInferableTypes flags
            then ty_args_doc ++ ex_types_doc ++ args_doc
            else ex_types_doc ++ args_doc
       in hang op_doc appIndent (sep visible_args_doc)

    app op ty_args args =
      let op_doc = continue op ?+ appPrec
          ty_args_doc = [text "@" <> pprTypePrec t ?+ appPrec | t <- ty_args]
          args_doc = [continue arg ?+ appPrec | arg <- args]
          visible_args_doc =
            if showTypeArguments flags
            then ty_args_doc ++ args_doc
            else args_doc
      in hang op_doc appIndent (sep visible_args_doc)

pprAltPatternFlags flags alt =
  pprPatternMatchFlags flags (altCon alt) (altParams alt)

pprPatternMatch decon params =
  pprPatternMatchFlags defaultPprFlags decon params

pprPatternMatchFlags f (VarDeCon con ty_args ex_types) params =
  let con_doc = pprVar con
      args_doc = pprTyArgs ty_args
      ex_types_doc = pprExTypeBinders ex_types
      params_doc = map (parens . pprPatFlags True f) params
      visible_args_doc =
        if showInferableTypes f
        then args_doc ++ ex_types_doc ++ params_doc
        else ex_types_doc ++ params_doc
  in hang con_doc appIndent (sep visible_args_doc)

pprPatternMatchFlags f (TupleDeCon _) params =
  pprParenList (map (pprPatFlags True f) params)

pprAlt altm = pprAltFlags defaultPprFlags altm

pprAltFlags f (AltM alt) =
  hang (pprAltPatternFlags f alt <> text ".") defIndent $
  pprExpFlags f (altBody alt)

pprFun f = unparenthesized $ pprFunPrecFlags False defaultPprFlags f

pprFunPrec f = pprFunPrecFlags False defaultPprFlags f

-- | Pretty-print a function.  If it's a lambda function, the function doesn't
--   need type annotations.
pprFunPrecFlags is_lambda flags (FunM fun) =
  let ty_params_doc = map pprTyPat $ funTyParams fun
      params_doc = map (pprPatFlags is_lambda flags) $ funParams fun
      return_doc = pprTypePrec (funReturn fun) ?+ funPrec
      body_doc = pprExpPrecFlags flags (funBody fun) ? stmtPrec
      sig_doc = sep [pprParenList (ty_params_doc ++ params_doc),
                     nest (-3) $ text "->" <+> return_doc]
  in hang (text "lambda" <+> sig_doc <> text ".") defIndent body_doc
     `hasPrec` stmtPrec

pprFDef def = pprFDefFlags defaultPprFlags def

pprFDefFlags flags (Def v ann f) =
  hang (pprVar v <+> ann_doc <+> text "=") defIndent $
  pprFunPrecFlags False flags f ? outerPrec
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
          conlike_doc =
            if defAnnConlike ann
            then text "conlike"
            else empty
          join_doc =
            if defAnnJoinPoint ann
            then text "join_point"
            else empty
          uses_doc = text $ showMultiplicity (defAnnUses ann)
      in brackets $ sep $
         punctuate (text ",") $
         filter (not . isEmpty) [inl_doc, join_doc, phase_doc, uses_doc]

pprFDefGroup :: DefGroup (FDef Mem) -> Doc
pprFDefGroup dg = pprFDefGroupFlags defaultPprFlags dg

pprFDefGroupFlags flags dg =
  case dg
  of NonRec _ -> text "nonrec {" $$ nest 2 members $$ text "}"
     Rec _ -> text "rec {" $$ nest 2 members $$ text "}"
  where
    members = vcat $ map (pprFDefFlags flags) $ defGroupMembers dg

pprExport e = pprExportFlags defaultPprFlags e

pprExportFlags flags (Export _ _ f) =
  text "export" <+> pprFunPrecFlags False flags f ? outerPrec

pprModule m = pprModuleFlags defaultPprFlags m

pprModuleFlags flags (Module modname imports defs exports) =
  text "module" <+> text (showModuleName modname) $$
  {-text "imports {" $$
  nest 2 (vcat (map pprDef imports)) $$
  text "}" $$-}
  vcat (map (pprFDefGroupFlags flags) defs) $$
  vcat (map (pprExportFlags flags) exports)