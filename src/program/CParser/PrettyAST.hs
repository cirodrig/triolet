{-| Pretty-printing instances for AST data structures
-}

{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
module CParser.PrettyAST() where

import Text.PrettyPrint.HughesPJ

import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Core(Var, conName)
import CParser.Pretty
import CParser.AST

pprWithHeading heading_name x = hang (text (heading_name ++ ":")) 2 (ppr x)

pprDocWithHeading heading_name doc = hang (text (heading_name ++ ":")) 2 doc

-- | Source positions are not shown when pretty-printing located objects 
instance Pretty a => Pretty (Located a) where ppr x = ppr (unLoc x)

instance Pretty [Char] where ppr s = text s
instance Pretty Var where ppr v = text (show v)
instance Pretty Lit where 
  ppr lit = case lit of
              IntL i -> text (show i)
              FloatL f -> text (show f)

-- Typically Variable Name & its unique Integer ID
instance Pretty ResolvedVar where
  ppr (ResolvedVar var mlbl _) =
    case mlbl
    of Just lbl -> text (showLabel lbl) <+> parens (text $ show var)
       Nothing  -> text (show var) <+> text "(No label)"

-- Variable Name, ID, and Level
instance Pretty LIVar where
  ppr (LIVar v) = text (show v)
  ppr (LICon c) = text (labelUnqualifiedName $ conName c)
  ppr (LIKind k) = text "<KIND>"

instance Pretty (Identifier ix) => Pretty (Type ix) where
  ppr iden =
    case iden
    of VarT var ->
         text "(VarT)" <+> ppr var
       LitT lit ->
         text "(LitT)" <+> ppr lit
       AppT oper args ->
       -- Not related to Pycore; $$ chosen to represent Application
         braces $
         text " " <> ppr oper <+> text "$$" <+> vcat (map ppr args) <> text " "
       FunT param maybeEff range ->
         let param_doc = pprWithHeading "Parameter" param
             eff_doc = case maybeEff
                       of Nothing -> empty
                          Just eff -> pprWithHeading "Effect" eff
             range_doc = pprWithHeading "ReturnType" range
         in pprDocWithHeading "FunT" (param_doc $$ eff_doc $$ range_doc)
               

instance Pretty (Identifier ix) => Pretty (ParamType ix) where
  ppr param =
    case param
    of ValuePT maybePvar ptype ->
         let param_doc =
               case maybePvar
               of Nothing   -> empty
                  Just pvar -> pprWithHeading "Variable" pvar
         in text "--Value PT--" $$
            param_doc $$
            pprWithHeading "Type" ptype
       BoxedPT ptype ->
         text "--Boxed PT--" $$
         pprWithHeading "Type" ptype
       ReferencedPT paddr ptype ->
         text "--Referenced PT--" $$
         pprWithHeading "Address" paddr $$
         pprWithHeading "Type" ptype

instance Pretty (Identifier ix) => Pretty (ReturnType ix) where
  ppr (ReturnType repr rtype) =
    let repr_doc = text $ case repr
                          of Value -> "--Value RT--"
                             Boxed -> "--Boxed RT--"
                             Reference -> "--Reference RT--"
    in repr_doc $$ pprWithHeading "Type" rtype

instance Pretty (Identifier ix) => Pretty (Decl ix) where
  ppr dec =
    case dec
    of BoxedDecl dvar dtype ->
         show_decl "BoxedDecl" $
         pprWithHeading "Variable" dvar $$ pprWithHeading "Type" dtype
       DataDecl daddr dptr dtype ->
         show_decl "DataDecl" $
         pprWithHeading "Address" daddr $$
         pprWithHeading "Pointer" dptr $$
         pprWithHeading "Type" dtype
    where
      show_decl heading content =
        hang (text $ "*** " ++ heading ++ " ***") 1 content

instance Pretty (Identifier ix) => Pretty (Module ix) where
  ppr (Module declList) =
    case declList
    of [] -> text "Empty Module"
       _ -> (text "Module:") $$ vcat (map ppr declList)
