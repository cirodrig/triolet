
module Core.Print
where
  
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Label
import Gluon.Core
import Export
import Core.Syntax
import qualified SystemF.Syntax as SystemF

pprPassConv :: Representation -> Doc
pprPassConv Value = text "val"
pprPassConv Boxed = text "box"
pprPassConv Referenced = text "ref"

pprParamT :: CBind CParamT Rec -> Doc
pprParamT (param ::: ty) =
  let param_doc =
        case param
        of ValPT mv -> text "val" <+> maybe empty pprVar mv
           OwnPT    -> text "own"
           ReadPT a -> text "bor" <+> pprVar a
  in param_doc <+> colon <+> parens (pprType ty)

pprReturnT :: CBind CReturnT Rec -> Doc
pprReturnT (return ::: ty) =
  let return_doc =
        case return
        of ValRT -> text "val"
           OwnRT -> text "own"
           WriteRT -> text "write"
           ReadRT a -> text "bor" <+> pprExp a
  in return_doc <+> colon <+> parens (pprType ty)

pprParam :: CBind CParam Rec -> Doc
pprParam (param ::: ty) =
  let param_doc =
        case param
        of ValP v    -> text "val" <+> pprVar v
           OwnP v    -> text "own" <+> pprVar v
           ReadP a v -> text "bor" <+> pprVar v <> text "@" <> pprVar a
  in param_doc <+> colon <+> parens (pprType ty)

pprReturn :: CBind CReturn Rec -> Doc
pprReturn (return ::: ty) =
  let return_doc =
        case return
        of ValR -> text "val"
           OwnR -> text "own"
           WriteR a p -> text "write" <+> pprVar p <> text "@" <> pprVar a
           ReadR a p -> text "bor" <+> pprVar p <> text "@" <> pprExp a
  in return_doc <+> colon <+> parens (pprType ty)

pprLetBinder :: CBind LetBinder Rec -> Doc
pprLetBinder (b ::: ty) =
  let binder_doc =
        case b
        of ValB v -> text "val" <+> pprVar v
           OwnB v -> text "own" <+> pprVar v
           LocalB a p -> text "local" <+> pprVar p <> text "@" <> pprVar a
           RefB a p -> text "bor" <+> pprVar p <> text "@" <> pprExp a
  in binder_doc <+> text ":" <+> parens (pprType ty)

pprType :: RCType -> Doc
pprType ty =
  case ty
  of ExpCT t -> pprExp t
     AppCT op args ->
       sep $ parens (pprType op) : map (nest 2 . parens . pprType) args
     FunCT f -> pprFunType f

pprFunType :: RCFunType -> Doc
pprFunType ty =
  let (params, ret) = arrowClauses ty
  in sep (map ppr_param params ++ [ret])
  where
    ppr_param (param_doc, eff_doc) = param_doc <+> text "->" <+> eff_doc

arrowClauses :: RCFunType -> ([(Doc, Doc)], Doc)
arrowClauses ty =
  case ty
  of ArrCT param eff rng ->
       let param_doc = pprParamT param
           eff_doc = ppr_effect eff
       in case arrowClauses rng
          of (params_doc, rng_doc) ->
               ((param_doc, eff_doc) : params_doc, rng_doc)
     RetCT ret ->
       let ret_doc = pprReturnT ret
       in ([], ret_doc)
  where
    ppr_effect eff 
      | is_empty_effect eff = empty
      | otherwise = text "<<" <> pprType eff <> text ">>"

    is_empty_effect eff =
      case eff
      of ExpCT (ConE {expCon = c}) -> c == builtin the_EmpE
         _ -> False
         
pprValue :: Value Rec -> Doc         
pprValue val =
  case val
  of ValueVarV v  -> parens $ text "val" <+> pprVar v
     OwnedVarV v  -> parens $ text "own" <+> pprVar v
     ReadVarV a p -> parens $ text "bor" <+> pprVar p <> text "@" <> pprExp a
     WriteVarV a p -> parens $ text "write" <+> pprVar p <> text "@" <> pprExp a
     ValueConV c -> text $ showLabel $ conName c
     OwnedConV c -> text $ showLabel $ conName c
     ReadConV a p -> parens $ text "bor" <+> (text $ showLabel $ conName p) <> text "@" <> pprExp a
     LitV l -> case l
               of SystemF.IntL n _ -> text $ show n
                  SystemF.FloatL d _ -> text $ show d
                  --SystemF.BoolL b -> text $ show b
                  --SystemF.NoneL -> text "None"
     TypeV ty -> parens $ pprType ty

pprCExp :: RCExp -> Doc
pprCExp exp =
  case exp
       of ValCE {cexpVal = v} -> pprValue v
          AppCE {cexpOper = op, cexpArgs = args, cexpReturnArg = ra} ->
            parens $ sep $
            pprCExp op : map (nest 2) (map pprCExp args ++ [maybe empty pprCExp ra])
          LamCE {cexpFun = f} -> parens $ pprCFun f
          LetCE {cexpBinder = b, cexpRhs = rhs, cexpBody = body} ->
            let let_doc = hang (text "let" <+> pprLetBinder b <+> text "=") 6 $
                          pprCExp rhs
            in let_doc $$ pprCExp body
          LetrecCE {cexpDefs = defs, cexpBody = body} ->
            let defs_doc = vcat $ map pprCDef defs
            in hang (text "letrec") 4 defs_doc $$ pprCExp body
          CaseCE {cexpScrutinee = scr, cexpAlternatives = alts} ->
            let scr_doc = pprCExp scr
                alts_doc = vcat $ map pprCAlt alts
            in text "case" <+> scr_doc $$
               text "of" <+> alts_doc

pprCAlt :: RCAlt -> Doc
pprCAlt alt =
  let con_doc = text $ showLabel $ conName $ caltConstructor alt
      ty_args = map pprType $ caltTyArgs alt
      params  = map pprParam $ caltParams alt
      body    = pprCExp $ caltBody alt
  in hang (con_doc <+> fsep (ty_args ++ params) <> text ".") 4 body

pprCFun :: RCFun -> Doc
pprCFun fun =
  let params = map parens $ map pprParam $ cfunParams fun
      ret = pprReturn $ cfunReturn fun
      eff = pprType $ cfunEffect fun
      body = pprCExp $ cfunBody fun
      intro = text "lambda" <+>
              sep (params ++ [nest (-3) $ text "->" <+> ret,
                              nest (-2) $ text "|" <+> eff]) <> text "."
  in hang intro 4 body

pprCDef :: CDef Rec -> Doc
pprCDef (CDef v f) =
  hang (pprVar v <+> text "=") 4 (pprCFun f)

pprCExport :: CExport Rec -> Doc
pprCExport (CExport _ (ExportSpec lang name) f) = 
  let export_language = case lang
                        of CCall -> text "ccall"
      export_name = text $ show name
  in text "export" <+> export_language <+> export_name <+> text "=" $$
     pprCFun f

pprCModule :: CModule Rec -> Doc
pprCModule (CModule module_name defss exports) =
  text "module" <+> text (showModuleName module_name) $$
  vcat (map (vcat . map pprCDef) defss) $$ vcat (map pprCExport exports)