
{
module CParser2.Lexer
    (LexerError(..),
     Token(..), Tok(..), showTok, showToken,
     lexify
    )
where

import Control.Exception

import Gluon.Common.SourcePos
import CParser2.LexData

}

-------------------------------------------------------------------------------

$e		= [eE]
$digit		= 0-9
$alpha		= [a-zA-Z_]
$alnum		= [a-zA-Z_0-9]
$eol		= [\n\0]		-- line terminators
$notml          = [^\-\{]               -- not the start of a meaningful token
                                        -- inside a multiline comment

$oper		= [\-\+\*\/\<\>=\~\!\?\#:\@\$\%\^\&\|]

@signed		= \-? $digit+
@word		= $alpha $alnum *
@eow		= ~$alnum | $eol	-- end of word
@operator	= $oper +
@eoo		= ~$oper | $eol		-- end of operator
@line		= ~$eol*		-- consume a line
@notdash        = [^\-] | $eol		-- not a dash character
@notrbrace      = [^\}] | $eol          -- not a right brace

-- characters in a multiline comment
@multlinecom    = \{ @notdash | \- @notrbrace | $notml

-- startcodes
--  0:		normal
--  mlc:	multi-line coment

rules :- ----------------------------------------------------------------------

-- Whitespace and comments

	$white+			;
<mlc>	@multlinecom+		;

-- Treat the null character as whitespace.
-- A null character is inserted at the end of a file by the lexical analyzer.
	\0			;

<0>	\-\- @line $eol		;

	\{\-			{ beginComment }
<mlc>	\-\}			{ endComment }
<0>	\-\}			{ parseError "Unexpected comment terminator" }

-- Numbers

<0,att>	@signed			{ posn mkInt }
<0,att>	@signed \. $digit+ ( $e @signed ) ?
				{ posn mkFloat }

-- Identifiers

<0>	"box" / @eow		{ posnTok BoxTok }
<0>     "data" / @eow		{ posnTok DataTok }
<0>	"let" / @eow		{ posnTok LetTok }
<0>	"letrec" / @eow		{ posnTok LetrecTok }
<0>	"read" / @eow		{ posnTok ReadTok }
<0>	"ref" / @eow		{ posnTok RefTok }
<0>	"val" / @eow		{ posnTok ValTok }
<0>	"write" / @eow		{ posnTok WriteTok }
<0>	"_" / @eow		{ posnTok WildTok }
<0>	@word			{ posn mkIdent }

-- Symbols

<0>	\{			{ posnTok LBraceTok }
<0>	\}			{ posnTok RBraceTok }
<0>	\[			{ posnTok LBracketTok }
<0>	\]			{ posnTok RBracketTok }
<0>	\(			{ posnTok LParenTok }
<0>	\)			{ posnTok RParenTok }
<0>	\,			{ posnTok CommaTok }
<0>	\.			{ posnTok DotTok }
<0>	\;			{ posnTok SemiTok }

<0>	\-\> / @eoo		{ posnTok ArrowTok }
<0>	\= / @eoo		{ posnTok EqualTok }
<0>	\| / @eoo		{ posnTok PipeTok }
<0>	: / @eoo		{ posnTok ColonTok }
<0>	@operator		{ posn mkOper }

-------------------------------------------------------------------------------

{


-- Things used by alex

-- The lexer state
data AlexInput =
    AlexInput
    { alexInputPos      :: {-# UNPACK #-} !SourcePos
    , alexInputPrevChar :: {-# UNPACK #-} !Char
    , alexInputText     :: String
    }

-- Function to get the next character from input
alexGetChar :: AlexInput -> Maybe (Char, AlexInput)
alexGetChar inp =
    case alexInputText inp
    of (c:cs) -> Just (c, advance inp c cs)
       []     -> Nothing
    where
      advance inp c cs =
          inp { alexInputPos      = advancePosition c $ alexInputPos inp
              , alexInputPrevChar = c
              , alexInputText     = cs
              }
      advancePosition '\n' pos =
          setSourceColumn 1 $ setSourceLine (1 + fj (sourceLine pos)) pos

      advancePosition '\t' pos =
          setSourceColumn (8 + fj (sourceColumn pos)) pos

      advancePosition _ pos =
          setSourceColumn (1 + fj (sourceColumn pos)) pos

      fj (Just x) = x
      fj Nothing  = error "Lost source information in lexer"

-------------------------------------------------------------------------------
-- Main Alex hooks

-- The main routine, which gets a stream of tokens.
-- On error, it throws an exception.
-- For lexing to work properly, the file needs to end with a non-identifier,
-- non-whitespace character, so we append a null character to the stream.
lexify :: FilePath -> String -> [Token]
lexify path text =
    let initialState = AlexInput (fileSourcePos path 1 1) ' ' (text ++ "\0")
    in scan initialState [0]

scan inp scs@(sc : scs') =
    case alexScan inp sc
    of AlexEOF | sc == 0   -> []
               | sc == mlc -> let msg = "end of file inside multi-line comment"  
                              in throwLexerError msg
               | otherwise -> throwLexerError "unexpected end of file"
       AlexError inp'      -> let c = head $ alexInputText inp
                                  msg = "unexpected character " ++ show c
                              in throwLexerError msg
       AlexSkip inp' l     -> scan inp' scs
       AlexToken inp' n a  -> case runLex a (alexInputPos inp)
                                            (alexInputText inp)
                                            n
                              of TokenResult t   -> t : scan inp' scs
                                 PushComment     -> scan inp' (mlc : scs)
                                 PopComment      -> scan inp' scs'
    where
      throwLexerError msg = throw $ LexerError (alexInputPos inp) msg

}