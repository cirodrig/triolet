
module SystemF.PrintMemoryIR
       (PprFlags(..),
        defaultPprFlags, briefPprFlags, tersePprFlags,
        pprLit,
        pprDmd,
        pprCallDmd,
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
        pprGDef,
        pprExport,
        pprModule,
        pprModuleFlags,
       )
where

import Text.PrettyPrint.HughesPJ

import Common.ConPattern
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

    -- | Include imports in the output
  , showImports :: !Bool
  }

defaultPprFlags = PprFlags True True True False

briefPprFlags = PprFlags True True False False

tersePprFlags = PprFlags False False False False

defIndent = 2
letIndent = 2
appIndent = 4
caseIndent = 6

pprParenList xs = parens $ sep $ punctuate (text ",") xs

pprList xs = brackets $ sep $ punctuate (text ",") xs

pprTyArgs ts = [text "@" <> pprTypePrec t ?+ appPrec | t <- ts]
pprExTypeArgs ts = [text "&" <> pprTypePrec t ?+ appPrec | t <- ts]
pprExTypeBinders ts = [text "&" <> parens (pprVar v <+> text ":" <+> pprType t)
                      | (v ::: t) <- ts]


pprLit :: Lit -> Doc
pprLit (IntL n (VarT v)) 
  | v == intV  = text (show n)
  | v == uintV = text (show n ++ "U")
  | otherwise  = parens $ text "<unknown integer type>" <+> text (show n)
pprLit (FloatL n _) = text (show n)

pprDmd :: Dmd -> Doc
pprDmd (Dmd m s) =
  text (showMultiplicity m) <> text ":" <> pprSpecificity s

pprSpecificity Used = text "U"
pprSpecificity Inspected = text "I"
pprSpecificity Copied = text "C"
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
  in text "D" <> braces (type_doc <> text ":" <> cat (map pprDmd spcs))

pprSpecificity (Called n mv spc) =
  -- If last parameter takes a variable, show it as a lambda function
  let (n_args, body) =
        case mv
        of Nothing -> (n, pprSpecificity spc)
           Just v  -> let lambda_term =
                            text "lambda" <+> pprVar v <> text "." <+>
                            pprSpecificity spc
                      in (n-1, lambda_term)
  in if n_args == 0
     then body
     else text "A" <> text (show n_args) <+> parens body

pprSpecificity (Read m) =
  text "R" <> pprHeapMap m
pprSpecificity Unused = text "0"

pprHeapMap (HeapMap m) = parens (cat $ punctuate (text ",") cells)
  where
    cells = [pprVar v <+> text "|->" <+> pprSpecificity s | (v, s) <- m]

pprCallDmd :: CallDmd -> Doc
pprCallDmd CallUnused   = text "D"
pprCallDmd (CallUsed 0) = text "U"
pprCallDmd (CallUsed n) = text $ "A(" ++ show n ++ ")"

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
     ConE _ (VarCon op ty_args ex_types) sps ty_obj args ->
       con op ty_args ex_types sps ty_obj args `hasPrec` appPrec

     ConE _ (TupleCon _) [] Nothing args ->
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
     CaseE _ scr sps [AltM alt] ->
       let sps_doc = pprList $ map (pprExpFlags flags) sps
           alt_doc = pprAltPatternFlags flags alt
           binder_doc = text "let" <+> sps_doc <+> alt_doc <+> text "="
           scr_doc = continue scr ? stmtPrec
           body_doc = continue (altBody alt) ? stmtPrec
       in hang binder_doc caseIndent scr_doc $$ body_doc `hasPrec` stmtPrec
     CaseE _ scr sps alts ->
       let sps_doc = pprList $ map (pprExpFlags flags) sps
           case_doc = text "case" <+> sep [continue scr ? stmtPrec, sps_doc]
           of_doc = text "of" <+> vcat (map (pprAltFlags flags) alts)
       in case_doc $$ of_doc `hasPrec` stmtPrec
     ExceptE _ rt ->
       text "except" <+> pprType rt `hasPrec` stmtPrec
     CoerceE _ from_t to_t body ->
       let coercion_doc = pprType from_t <+> text "=>" <+> pprType to_t
           b_doc = continue body ?+ appPrec
       in hang (text "coerce" <+> parens coercion_doc) letIndent b_doc
          `hasPrec` appPrec
     ArrayE _ t es ->
       let es_doc = punctuate comma [continue e ? outerPrec | e <- es]
       in text "array" <+> pprTypePrec t ?+ appPrec <+> braces (fsep es_doc) `hasPrec` appPrec
  where
    continue e = pprExpPrecFlags flags e

    con op ty_args ex_types sps ty_obj args =
      let op_doc = text "<" <> pprVar op <> text ">"
          ty_args_doc = pprTyArgs ty_args
          ty_obj_doc = case ty_obj
                       of Nothing -> empty
                          Just e  -> brackets $ continue e ? outerPrec
          ex_types_doc = pprExTypeArgs ex_types
          sps_doc = pprList $ map (pprExpFlags flags) sps
          args_doc = [continue arg ?+ appPrec | arg <- args]
          visible_args_doc =
            if showInferableTypes flags
            then ty_args_doc ++ ex_types_doc ++ [sps_doc] ++ [ty_obj_doc] ++ args_doc
            else ex_types_doc ++ [sps_doc] ++ [ty_obj_doc] ++ args_doc
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
  pprPatternMatchFlags flags (altCon alt) (altTyObject alt) (altParams alt)

pprPatternMatch decon tyob_param params =
  pprPatternMatchFlags defaultPprFlags decon tyob_param params

pprPatternMatchFlags f (VarDeCon con ty_args ex_types) tyob_param params =
  let con_doc = pprVar con
      args_doc = pprTyArgs ty_args
      ex_types_doc = pprExTypeBinders ex_types
      tyob_param_doc = maybe empty (brackets . pprPatFlags True f) tyob_param
      params_doc = map (parens . pprPatFlags True f) params
      visible_args_doc =
        if showInferableTypes f
        then args_doc ++ ex_types_doc ++ [tyob_param_doc] ++ params_doc
        else ex_types_doc ++ [tyob_param_doc] ++ params_doc
  in hang con_doc appIndent (sep visible_args_doc)

pprPatternMatchFlags f (TupleDeCon _) tyob_param params =
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

pprDefAnn :: DefAnn -> Doc
pprDefAnn ann =
  brackets $ sep $ punctuate (text ",") $
  filter (not . isEmpty) [inl_doc, pattern_doc, join_doc, phase_doc, call_doc, uses_doc]
  where
    phase_doc =
      case defAnnInlinePhase ann
      of InlNormal -> empty
         x -> text (show x)
    inl_doc =
      case defAnnInlineRequest ann
      of InlConservatively -> empty
         x -> text (show x)
    pattern_doc =
      case defAnnInlinePattern ann
      of Nothing -> empty
         Just ps -> text (showConPatterns ps)
    conlike_doc =
      if defAnnConlike ann
      then text "conlike"
      else empty
    join_doc =
      if defAnnJoinPoint ann
      then text "join_point"
      else empty
    uses_doc = pprDmd (defAnnUses ann)
    call_doc = if defAnnCalled ann then text "called" else empty

pprFDef def = pprFDefFlags defaultPprFlags def

pprFDefFlags flags (Def v ann f) =
  hang (pprVar v <+> pprDefAnn ann <+> text "=") defIndent $
  pprFunPrecFlags False flags f ? outerPrec

pprFDefGroup :: DefGroup (FDef Mem) -> Doc
pprFDefGroup dg = pprFDefGroupFlags defaultPprFlags dg

pprFDefGroupFlags flags dg = pprDefGroupFlags pprFDefFlags flags dg
pprGDefGroupFlags flags dg = pprDefGroupFlags pprGDefFlags flags dg

pprDefGroupFlags ppr_member flags dg =
  case dg
  of NonRec _ -> text "nonrec {" $$ nest 2 members $$ text "}"
     Rec _ -> text "rec {" $$ nest 2 members $$ text "}"
  where
    members = vcat $ map (ppr_member flags) $ defGroupMembers dg

pprGDef def = pprGDefFlags defaultPprFlags def

pprGDefFlags flags (Def v ann (FunEnt f)) =
  pprFDefFlags flags (Def v ann f)

pprGDefFlags flags (Def v ann (DataEnt d)) =
  hang (pprVar v <+> colon <+> ty_doc <+> pprDefAnn ann <+> equals) 4 $
  pprExpFlags flags (constExp d)
  where
    ty_doc = pprType $ constType d

pprExport e = pprExportFlags defaultPprFlags e

pprExportFlags flags (Export _ _ f) =
  text "export" <+> pprFunPrecFlags False flags f ? outerPrec

pprModule m = pprModuleFlags defaultPprFlags m

pprModuleFlags flags (Module modname imports defs exports) =
  text "module" <+> text (showModuleName modname) $$
  (if showImports flags then import_doc else empty) $$
  vcat (map (pprGDefGroupFlags flags) defs) $$
  vcat (map (pprExportFlags flags) exports)
  where
    import_doc = text "imports {" $$
                 nest 2 (vcat (map (pprGDefFlags flags) imports)) $$
                 text "}"
