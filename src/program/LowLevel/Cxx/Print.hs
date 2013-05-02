
module LowLevel.Cxx.Print(prettyPrintHeaderFile)
where

import Text.PrettyPrint.HughesPJ

import LowLevel.Cxx.AST

class Ppr a where ppr :: a -> Doc

pprCommaList :: Ppr a => [a] -> Doc
pprCommaList xs = hsep $ punctuate comma $ map ppr xs

pprSemiList :: Ppr a => [a] -> Doc
pprSemiList xs = vcat [ppr x <> semi | x <- xs]

instance Ppr TmplName where
  ppr (PlainName nm) =
    text nm
  ppr (TmplName nm args) =
    text nm <> text "<" <+> pprCommaList args <+> text ">"

instance Ppr QName where
  ppr (Qualified nm name) = ppr nm <> text "::" <> ppr name
  ppr (Unqualified nm)    = ppr nm

instance Ppr Qualifier where
  ppr ExternCQual = text "extern \"C\""

-- | Pretty-print a type.  As per C's printing rules, the type is always
--   printed around something, which could be an empty document.
pprTypeDerivation :: Doc -> Type -> Doc
pprTypeDerivation target (NameType nm) =
  ppr nm <+> target
pprTypeDerivation target (FunType params ret) =
  pprTypeDerivation (target <> parens (pprCommaList params)) ret

instance Ppr Type where ppr t = pprTypeDerivation empty t

instance Ppr Expression where
  ppr (IdentExpr nm) = ppr nm
  ppr (CallExpr op args) = ppr op <> parens (pprCommaList args)
  ppr (DotExpr e n) = parens (ppr e) <> text "." <> text n
  ppr (CastExpr ty e) = parens (ppr ty) <> parens (ppr e)

instance Ppr Statement where
  ppr (DeclStmt decl m_init) =
    let initializer = case m_init
                      of Nothing -> empty
                         Just e -> text "=" <+> ppr e
    in ppr decl <+> initializer
  ppr (ExprStmt e) = ppr e
  ppr (ReturnStmt e) = text "return" <+> ppr e

instance Ppr Decl where
  ppr (Decl quals nm ty) =
    sep (map ppr quals) <+> pprTypeDerivation (text nm) ty

instance Ppr FunDef where
  ppr (FunDef quals rt name params body) =
    sep (map ppr quals) $$
    ppr rt <+> text name <+> parens (pprCommaList params) $$
    text "{" $$
    nest 4 (pprSemiList body) $$
    text "}"

instance Ppr HeaderFile where
  ppr (HeaderFile decls defs) =
    text preamble $$ pprSemiList decls $$ vcat (map ppr defs)
    where
      preamble = "#include <TrioletData.h>"

prettyPrintHeaderFile :: HeaderFile -> String
prettyPrintHeaderFile f = show $ ppr f