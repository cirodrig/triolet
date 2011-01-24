{-| Pretty-printing instances for AST data structures
-}

{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
module CParser.PrettyAST() where

import Text.PrettyPrint.HughesPJ

import Common.Identifier
import Common.Label
import CParser.Pretty
import CParser.AST
import Type.Type(Var, Repr(..))

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
    of Just lbl -> case labelLocalName lbl
                   of Left nm -> text nm <+> parens (text $ show var)
       Nothing  -> text (show var) <+> text "(No label)"

instance Pretty (Identifier ix) => Pretty (Type ix) where
  ppr iden =
    case iden
    of VarT var ->
         text "(VarT)" <+> ppr var
       AppT oper args ->
       -- Not related to Pycore; $$ chosen to represent Application
         braces $
         text " " <> ppr oper <+> text "$$" <+> vcat (map ppr args) <> text " "
       FunT param range ->
         let param_doc = pprWithHeading "Parameter" param
             range_doc = pprWithHeading "ReturnType" range
         in pprDocWithHeading "FunT" (param_doc $$ range_doc)
               
instance Pretty Repr where
  ppr Value = text "val"
  ppr Boxed = text "box"
  ppr Referenced = text "ref"

instance Pretty (Identifier ix) => Pretty (ParamType ix) where
  ppr (ParamType param_repr ptype) =
    case param_repr
    of ValuePT Nothing -> ordinary "val" 
       ValuePT (Just pvar) -> text "val" <+> ppr pvar <+> text ":" <+> ppr ptype
       BoxedPT -> ordinary "box"
       ReadPT -> ordinary "read"
       WritePT -> ordinary "write"
    where
      ordinary txt = text txt <+> ppr ptype

instance Pretty (Identifier ix) => Pretty (ReturnType ix) where
  ppr (ReturnType repr rtype) =
    let repr_doc = text $ case repr
                          of ValueRT -> "--Value RT--"
                             BoxedRT -> "--Boxed RT--"
                             ReadRT -> "--Read RT--"
                             WriteRT -> "--Write RT--"
    in repr_doc $$ pprWithHeading "Type" rtype

instance Pretty (Identifier ix) => Pretty (DataConDecl ix) where
  ppr (DataConDecl v ty params args rng) =
    pprWithHeading "Variable" v $$
    pprWithHeading "Type" ty $$
    (vcat $ map ppr params) $$ 
    (vcat $ map ppr args) $$ 
    pprWithHeading "Constructed type" rng

instance Pretty (Identifier ix) => Pretty (Decl ix) where
  ppr dec =
    case dec
    of VarDecl dvar dtype ->
         show_decl "Variable" $
         pprWithHeading "Variable" dvar $$ pprWithHeading "Type" dtype
       DataDecl dvar repr dtype cons ->
         show_decl "Data type" $
         pprWithHeading "Variable" dvar $$
         pprWithHeading "Type" dtype $$
         pprWithHeading "Representation" repr $$
         nest 2 (vcat $ map ppr cons)
    where
      show_decl heading content =
        hang (text $ "*** " ++ heading ++ " ***") 1 content

instance Pretty (Identifier ix) => Pretty (Module ix) where
  ppr (Module declList) =
    case declList
    of [] -> text "Empty Module"
       _ -> (text "Module:") $$ vcat (map ppr declList)
