{-| Lexical analysis routines.  The actual lexing rules are in "Lexer". 
-}

{-# LANGUAGE DeriveDataTypeable #-}
module CParser.LexData where

import Control.Exception
import Data.Typeable

import Gluon.Common.SourcePos

-- | A token produced by lexical analysis
data Token = Token !SourcePos !Tok

-- | A token produced by lexical analysis
data Tok =
    IntTok {-# UNPACK #-} !Integer
  | FloatTok {-# UNPACK #-} !Double
  | IdentTok String
  | OperTok String
  | LBraceTok
  | RBraceTok
  | LBracketTok
  | RBracketTok
  | LParenTok
  | RParenTok
  | CommaTok
  | DotTok
  | EqualTok
  | PipeTok
  | SemiTok
  | ColonTok
  | ArrowTok
  | BoxTok
  | LetTok
  | LetrecTok
  | RefTok
  | WildTok
  | ValTok
    deriving(Eq)

showTok :: Tok -> String
showTok t =
    case t
    of IntTok n     -> show n
       FloatTok n   -> show n
       IdentTok s   -> "'" ++ s ++ "'"
       OperTok s    -> "(" ++ s ++ ")"
       LBraceTok    -> "left brace"
       RBraceTok    -> "right brace"
       LBracketTok  -> "left bracket"
       RBracketTok  -> "right bracket"
       LParenTok    -> "left parenthesis"
       RParenTok    -> "right parenthesis"
       CommaTok     -> "comma"
       DotTok       -> "dot"
       EqualTok     -> "equal"
       PipeTok      -> "vertical bar"
       SemiTok      -> "semicolon"
       ColonTok     -> "colon"
       ArrowTok     -> "arrow"
       BoxTok       -> "'box'"
       LetTok       -> "'let'"
       LetrecTok    -> "'letrec'"
       RefTok       -> "'ref'"
       WildTok      -> "underscore"
       ValTok       -> "'val'"

showToken :: Token -> String
showToken (Token _ t) = showTok t

data LexerError = LexerError !SourcePos String
                deriving(Typeable)

instance Show LexerError where
  show (LexerError pos msg) =
    "Unexpected token in input at " ++ show pos ++ ":\n" ++ msg

instance Exception LexerError

-------------------------------------------------------------------------------
-- User actions

-- Type of a user action
newtype Lex = Lex {runLex :: SourcePos -> String -> Int -> LexResult}

data LexResult =
    TokenResult !Token
  | PushComment | PopComment

-- Default routines for source position handling.
--
-- The parameter creates a bare token from a string.  This function then
-- adds source line information onto the bare token.
posn :: (String -> Int -> Tok) -> Lex
posn f = Lex $ \posn text n -> TokenResult $ Token posn $! f text n

-- Emit a token at the current position
posnTok :: Tok -> Lex
posnTok t = Lex $ \posn _ _ -> TokenResult $ Token posn t

-- Functions to create tokens.
-- The lexical analyzer rules should accept only valid strings, so that
-- calls to 'read' never fail.
mkFloat, mkInt, mkIdent :: String -> Int -> Tok
mkFloat s _ = FloatTok (fst $ head $ reads s)
mkInt s _   = IntTok (fst $ head $ reads s)
mkIdent s n = IdentTok (take n s)
mkOper s n  = OperTok (take n s)

beginComment, endComment :: Lex
beginComment = Lex $ \_ _ _ -> PushComment
endComment = Lex $ \_ _ _ -> PopComment

parseError :: String -> Lex
parseError msg = Lex $ \pos _ _ -> throw $ LexerError pos msg

