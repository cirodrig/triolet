{-| Control flow analysis of parsed code.

-}

{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
module Parser.Control where

import Compiler.Hoopl
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Language.Python.Common.Pretty as Python
import qualified Language.Python.Common.PrettyAST as Python
import Text.PrettyPrint.HughesPJ

import Common.SourcePos
import Parser.ParserSyntax hiding(Stmt(..))

-- | A control flow source.
--   A source consists of a block label and an outgoing path.
data Source = Source !Label !FlowPath deriving(Eq, Show)

data FlowPath = JumpPath | TruePath | FalsePath deriving(Eq, Show)

-- | An outgoing control flow path.
--
--   SSA annotates a control flow path with variable IDs.
data Flow id = Flow 
               { flowLabel :: !Label 
               , flowSSA :: !(Maybe [Var id])
               }

noSSAFlow :: Label -> Flow id
noSSAFlow l = Flow l Nothing

-- | A control flow node.  Performs an action, has inputs and outputs.
data Stmt id e x where
    --   Assign LHS the value of RHS
    Assign :: Parameter id -> LExpr id -> Stmt id O O

    --   A group of function definitions.
    --   Definition groups are annotated with their live-in variables
    --   during live variable analysis.  The live-in variables is the
    --   union of the functions' live-ins, minus the functions themselves.
    DefGroup :: [LCFunc id] -> !MLiveness -> Stmt id O O

    --   Assert that some propositions hold
    Assert :: [LExpr id] -> Stmt id O O

    --   Type annotation
    Require :: Var id -> LExpr id -> Stmt id O O

    --   A control flow target, for incoming control flow.
    --
    --   Targets are annotated with parameters during SSA analysis.
    Target :: Label -> !(Maybe [Var id]) -> Stmt id C O
    
    --   Conditional branch
    If :: LExpr id -> Flow id -> Flow id -> Stmt id O C
    
    --   Direct jump
    Jump :: Flow id -> Stmt id O C
    
    --   Return from function
    Return :: LExpr id -> Stmt id O C

instance NonLocal (Stmt id) where
  entryLabel (Target l _) = l
  successors (If _ t f)   = [flowLabel t, flowLabel f]
  successors (Jump l)     = [flowLabel l]
  successors (Return _)   = []

newtype LStmt id e x = LStmt (Loc (Stmt id e x))

instance NonLocal (LStmt id) where
  entryLabel x = entryLabel $ unLStmt x
  successors x = successors $ unLStmt x

unLStmt :: LStmt id e x -> Stmt id e x
unLStmt (LStmt (Loc _ s)) = s

lStmt :: SourcePos -> Stmt id e x -> LStmt id e x
lStmt pos s = LStmt (Loc pos s)

type family FuncBody id

type instance FuncBody AST = CFG AST C C

-- | A control flow based function definition
data CFunc id =
  CFunc
  { cfSignature        :: !(FunSig id)
  , cfLivenesses       :: !MLivenesses
  , cfEntry            :: !Label
  , cfBody             :: FuncBody id
  }

type LCFunc id = Loc (CFunc id)

type CFG id e x = Graph (LStmt id) e x

-- | Get the outgoing edges of a block
blockOutEdges :: Block (LStmt id) C C -> [(Source, Label)]
blockOutEdges block = let
  !block_label = entryLabel block
  !(_, _, JustC last) = blockToNodeList block
  paths = case unLStmt last
          of If _ t f -> [(TruePath, flowLabel t), (FalsePath, flowLabel f)]
             Jump l   -> [(JumpPath, flowLabel l)]
             Return _ -> []
  in [(Source block_label path, succ_label) | (path, succ_label) <- paths]

-------------------------------------------------------------------------------
-- Printing

class Ppr a where
  ppr :: a -> Doc

-- | Locations are not shown when pretty-printing
instance Ppr a => Ppr (Loc a) where ppr (Loc _ x) = ppr x

instance Ppr Literal where
  ppr (IntLit n)       = text (show n)
  ppr (FloatLit d)     = text (show d)
  ppr (ImaginaryLit d) = text (show d ++ "j")
  ppr (BoolLit True)   = text "True"
  ppr (BoolLit False)  = text "False"
  ppr NoneLit          = text "None"

instance Ppr (Var AST) where
  ppr v = text (varName v ++ '\'' : show (varID v))

pprCommaList xs = punctuate comma $ map ppr xs

instance Ppr (Var a) => Ppr (Parameter a) where
  ppr (Parameter v Nothing)  = ppr v
  ppr (Parameter v (Just e)) = ppr v <+> colon <+> ppr e
  ppr (TupleParam ps) = parens (fsep $ pprCommaList ps)

instance Ppr (Var a) => Ppr (Expr a) where
  ppr (Variable v) = ppr v
  ppr (Literal l) = ppr l
  ppr (Tuple es) = parens $ fsep $ pprCommaList es
  ppr (List es) = brackets $ fsep $ pprCommaList es
  ppr (Unary op e) = parens $ Python.pretty op <> ppr e
  ppr (Binary op e1 e2) = parens $ ppr e1 <+> Python.pretty op <+> ppr e2
  ppr (Subscript e es) = ppr e <> brackets (fsep $ pprCommaList es)
  ppr (Slicing e ss)   = ppr e <> brackets (fsep $ pprCommaList ss)
  ppr (ListComp iter)  = brackets $ ppr iter
  ppr (Generator iter) = parens $ ppr iter
  ppr (Call e es) = ppr e <> parens (fsep $ pprCommaList es)
  ppr (Cond c t f) = parens $
                     ppr t <+> text "if" <+> ppr c <+> text "else" <+> ppr f
  ppr (Lambda ps e) = text "lambda" <+> sep (pprCommaList ps) <> colon <+>
                      ppr e
  ppr (Let p e b) = text "let" <+> ppr p <+> equals <+> ppr e <+>
                    text "in" <+> ppr b

instance Ppr (Var a) => Ppr (Slice a) where
  ppr (SliceSlice _ l u s) =
    let l_doc = maybe empty ppr l
        u_doc = maybe empty ppr u
    in case s
       of Nothing -> l_doc <> colon <> u_doc
          Just s1 -> l_doc <> colon <> u_doc <> colon <> maybe empty ppr s1

  ppr (ExprSlice e) = ppr e

instance Ppr (Var a) => Ppr (IterFor a) where
  ppr iter = let (b, i) = pprIterFor iter in b <+> sep i

pprIterFor (IterFor _ ps e c) =
  let !(b, i) = pprComp c
      clause = text "for" <+> hsep (pprCommaList ps) <+> text "in" <+> ppr e
  in (b, clause : i)

pprIterIf (IterIf _ e c) =
  let !(b, i) = pprComp c
      clause = text "if" <+> ppr e
  in (b, clause : i)

pprIterLet (IterLet _ p e c) =
  let !(b, i) = pprComp c
      clause = text "let" <+> ppr p <+> equals <+> ppr e
  in (b, clause : i)

pprComp (CompFor i) = pprIterFor i
pprComp (CompIf i) = pprIterIf i
pprComp (CompLet i) = pprIterLet i
pprComp (CompBody e) = (ppr e, [])

instance Ppr (Var a) => Ppr (FunSig a) where
  ppr (FunSig name ann pragma params r_ann) = let
    annotation = case ann
                 of Nothing -> empty
                    Just a  -> text "<forall annotation>"
    r_annotation = case r_ann
                   of Nothing -> empty
                      Just a  -> text "->" <+> ppr a
    parameters = parens (sep $ pprCommaList params) <+> r_annotation
    in annotation $$ text "def" <+> ppr name <> parameters

instance (Ppr (Var a), Ppr (FuncBody a)) => Ppr (CFunc a) where
  ppr func = let
    signature = ppr (cfSignature func) <> colon
    entry_point = text "goto" <+> ppr (cfEntry func)
    body = ppr (cfBody func)
    in signature <+> entry_point $$ body

instance (Ppr (Var a), Ppr (FuncBody a)) => Ppr (Graph' Block (LStmt a) C C) where
  ppr (GMany NothingO blocks NothingO) =
    vcat [ppr l $$ nest 2 (ppr b) | (l, b) <- mapToList blocks]

instance Ppr (Var a) => Ppr (Flow a) where
  ppr (Flow l Nothing)   = ppr l
  ppr (Flow l (Just vs)) = ppr l <+> text "with" <+> hsep (pprCommaList vs)

instance Ppr Source where ppr s = text (show s)

instance Ppr Label where ppr l = text (show l)

-- | Blocks are pretty-printable.
--   The statements in a block are listed vertically.
instance (Ppr (Var a), Ppr (FuncBody a)) => Ppr (Block (LStmt a) C C) where
  ppr b = foldBlockNodesB prepend_node b empty
    where
      prepend_node :: forall e x. LStmt a e x -> Doc -> Doc
      prepend_node n d = ppr n $$ d

pprLiveness s = hang (text "liveness:") 4 $ fsep [ppr v | v <- Set.toList s]

instance (Ppr (Var a), Ppr (FuncBody a)) => Ppr (LStmt a e x) where
  ppr stmt = 
    case unLStmt stmt
    of Assign p e    -> hang (ppr p <+> equals) 4 (ppr e)
       DefGroup fs l -> let lv_doc = maybe empty pprLiveness l
                            fs_doc = vcat $ map ppr fs
                        in hang (text "defgroup:") 4 (lv_doc $$ fs_doc)
       Assert es     -> text "assert" <+> sep (pprCommaList es)
       Require v t   -> text "require" <+> ppr v <+> colon <+> ppr t
       Target l ps   -> let ps_doc = case ps
                                     of Nothing -> empty
                                        Just vs -> text "with" <+>
                                                   sep (pprCommaList vs)
                        in text "<target>" <+> ppr l <+> ps_doc
       If c t f      -> text "if" <+> ppr c $$
                        text "then" <+> ppr t $$
                        text "else" <+> ppr f
       Jump l        -> text "goto" <+> ppr l
       Return e      -> text "return" <+> ppr e
