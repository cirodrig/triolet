{-| Lexical analysis routines.  The actual lexing rules are in "Lexer". 
-}

{-# LANGUAGE DeriveDataTypeable #-}
module CParser2.LexData where

import Control.Exception
import Data.Typeable

import Common.SourcePos

-- | A token produced by lexical analysis
data Token = Token !SourcePos !Tok

-- | A token produced by lexical analysis
data Tok =
    IntTok {-# UNPACK #-} !Integer
  | IdentTok String
  | LBraceTok
  | RBraceTok
  | LBracketTok
  | RBracketTok
  | LParenTok
  | RParenTok
  | AtTok
  | BackslashTok
  | CommaTok
  | DotTok
  | EqualTok
  | PipeTok
  | SemiTok
  | ColonTok
  | ArrowTok
  | AttributeTok
  | CaseTok
  | DataTok
  | ElseTok
  | ExceptTok
  | IfTok
  | InTok
  | LetfunTok
  | OfTok
  | ThenTok
  | TypeTok
  | WildTok
    deriving(Eq)

showTok :: Tok -> String
showTok t =
    case t
    of IntTok n     -> show n
       IdentTok s   -> "'" ++ s ++ "'"
       LBraceTok    -> "left brace"
       RBraceTok    -> "right brace"
       LBracketTok  -> "left bracket"
       RBracketTok  -> "right bracket"
       LParenTok    -> "left parenthesis"
       RParenTok    -> "right parenthesis"
       AtTok        -> "at sign"
       BackslashTok -> "backslash"
       CommaTok     -> "comma"
       DotTok       -> "period"
       EqualTok     -> "equal"
       PipeTok      -> "vertical bar"
       SemiTok      -> "semicolon"
       ColonTok     -> "colon"
       ArrowTok     -> "arrow"
       AttributeTok -> "'attribute'"
       CaseTok      -> "'case'"
       DataTok      -> "'data'"
       ElseTok      -> "'else'"
       ExceptTok    -> "'except'"
       IfTok        -> "'if'"
       InTok        -> "'in'"
       LetfunTok    -> "'letfun'"
       OfTok        -> "'of'"
       ThenTok      -> "'then'"
       TypeTok      -> "'type'"
       WildTok      -> "underscore"

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
mkInt, mkIdent :: String -> Int -> Tok
mkInt s _   = IntTok (fst $ head $ reads s)
mkIdent s n = IdentTok (take n s)

beginComment, endComment :: Lex
beginComment = Lex $ \_ _ _ -> PushComment
endComment = Lex $ \_ _ _ -> PopComment

parseError :: String -> Lex
parseError msg = Lex $ \pos _ _ -> throw $ LexerError pos msg

