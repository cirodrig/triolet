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
    IntTok !Integer
  | UIntTok !Integer
  | FloatTok {-# UNPACK #-} !Double
  | IdentTok !String
  | OperTok !String
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
  | BoxedInfoTok
  | CaseTok
  | CoerceTok
  | DataTok
  | ElseTok
  | ExceptTok
  | ForallTok
  | IfTok
  | InTok
  | LetTok
  | LetfunTok
  | OfTok
  | ThenTok
  | TypeTok
  | UnboxedInfoTok
  | WildTok
    deriving(Eq)

showTok :: Tok -> String
showTok t =
    case t
    of IntTok n     -> show n
       UIntTok n    -> show n ++ "U"
       FloatTok n   -> show n
       IdentTok s   -> "'" ++ s ++ "'"
       OperTok s    -> "operator '" ++ s ++ "'"
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
       BoxedInfoTok -> "'boxedinfo'"
       CaseTok      -> "'case'"
       CoerceTok    -> "'coerce'"
       DataTok      -> "'data'"
       ElseTok      -> "'else'"
       ExceptTok    -> "'except'"
       ForallTok    -> "'forall'"
       IfTok        -> "'if'"
       InTok        -> "'in'"
       LetTok       -> "'let'"
       LetfunTok    -> "'letfun'"
       OfTok        -> "'of'"
       ThenTok      -> "'then'"
       TypeTok      -> "'type'"
       UnboxedInfoTok -> "'unboxedinfo'"
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

-- | Take part of a string and force evaluation, so that the string is
--   not retained.
takeForce n s = let s' = take n s
                in length s' `seq` s'

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
mkInt, mkUInt, mkFloat, mkIdent, mkOper :: String -> Int -> Tok
mkInt s n = case reads (take n s)
            of (n, []) : _ -> IntTok n
               _ -> throw $ LexerError noSourcePos "Cannot parse integer"
mkUInt s n = case reads (take (n-1) s)
            of (n, []) : _ -> UIntTok n
               _ -> throw $ LexerError noSourcePos "Cannot parse integer"
mkFloat s n = case reads (take n s)
              of (n, []) : _ -> FloatTok n
                 _ -> throw $ LexerError noSourcePos "Cannot parse float"
mkIdent s n = IdentTok (takeForce n s)
mkOper s n  = OperTok (takeForce n s)

beginComment, endComment :: Lex
beginComment = Lex $ \_ _ _ -> PushComment
endComment = Lex $ \_ _ _ -> PopComment

parseError :: String -> Lex
parseError msg = Lex $ \pos _ _ -> throw $ LexerError pos msg

