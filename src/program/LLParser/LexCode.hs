
{-# LANGUAGE ViewPatterns #-}
module LLParser.LexCode
       (Token(..),
        showToken,
        T(..),
        showT,
        Action(runAction),
        Input(..),
        fileInput,
        AlexInput,
        alexGetChar,
        alexInputPrevChar,
        idTok, intTok, tok,
        lineDirective
       )
where

import Data.Char
import Gluon.Common.SourcePos

-- | A token produced by lexical analysis
data Token =
    IdTok String
  | IntTok !Integer
  | FloatTok !Double
  | LBraceTok
  | RBraceTok
  | LParenTok
  | RParenTok
  | AssignTok
  | ArrowTok
  | SemiTok
  | CommaTok
  | EqualTok
  | DotTok
  | FieldTok
  | AtTok
  | StarTok
  | AlignofTok
  | AsTok
  | BytesTok
  | CallTok
  | DataTok
  | ElseTok
  | FunctionTok
  | IfTok
  | Int8Tok
  | Int16Tok
  | Int32Tok
  | Int64Tok
  | NullTok
  | OwnedTok
  | PointerTok
  | PrimCallTok
  | ProcedureTok
  | RecordTok
  | SizeofTok
  | UInt8Tok
  | UInt16Tok
  | UInt32Tok
  | UInt64Tok
    deriving(Eq)

showToken :: Token -> String
showToken (IdTok s) = show s
showToken (IntTok n) = show n
showToken (FloatTok d) = show d
showToken LBraceTok = "left brace"
showToken RBraceTok = "right brace"
showToken LParenTok = "left parenthesis"
showToken RParenTok = "right parenthesis"
showToken AssignTok = "equal sign"
showToken ArrowTok = "arrow"
showToken SemiTok = "semicolon"
showToken CommaTok = "comma"
showToken EqualTok = "equal operator"
showToken DotTok = "dot"
showToken FieldTok = "field operator"
showToken AtTok = "at operator"
showToken StarTok = "asterisk"
showToken AlignofTok = "'alignof'"
showToken AsTok = "'as'"
showToken BytesTok = "'bytes'"
showToken CallTok = "'call'"
showToken DataTok = "'data'"
showToken ElseTok = "'else'"
showToken FunctionTok = "'function'"
showToken IfTok = "'if'"
showToken Int8Tok = "'int8'"
showToken Int16Tok = "'int16'"
showToken Int32Tok = "'int32'"
showToken Int64Tok = "'int64'"
showToken NullTok = "'null'"
showToken OwnedTok = "'owned'"
showToken PointerTok = "'pointer'"
showToken PrimCallTok = "'primcall'"
showToken ProcedureTok = "'procedure'"
showToken RecordTok = "'record'"
showToken SizeofTok = "'sizeof'"
showToken UInt8Tok = "'uint8'"
showToken UInt16Tok = "'uint16'"
showToken UInt32Tok = "'uint32'"
showToken UInt64Tok = "'uint64'"

-- | A token labeled with a source position
data T = T !SourcePos !Token

showT (T _ tok) = showToken tok

-- | The lexer's input state
data Input =
  Input
  { inputString :: String
  , inputPrevChar :: !Char
  , inputPos :: !SourcePos
  }

-- | Use contents of a file as the lexer's input
fileInput :: FilePath -> String -> Input
fileInput path contents =
  Input { inputString = contents
        , inputPrevChar = '\n'
        , inputPos = fileSourcePos path 1 1
        }

-- | Given a character and the source position where the character begins,
-- determine the position where the next character begins.
advancePosition '\n' pos =
  case sourceLine pos
  of Just l -> setSourceColumn 1 $ setSourceLine (l+1) pos

advancePosition c pos =
  case sourceColumn pos
  of Just c -> setSourceColumn (c+1) pos

-- * Types and functions expected by Alex

type AlexInput = Input

alexGetChar input = 
  case inputString input
  of (c:cs) ->
       let pos' = advancePosition c (inputPos input)
       in Just (c, Input cs c pos')
     [] -> Nothing

alexInputPrevChar input = inputPrevChar input

-- * Lexer actions

type Scanner = Input -> Int -> [T]

-- | A lexer action.  The action takes the remaining input, current startcode,
-- and size of consumed input, and returns a list of tokens.  If an action 
-- does not consume the entire input, it will call the scanner to consume the
-- rest of the input.
newtype Action =
  Action {runAction :: Scanner  -- ^ Continuation
                    -> Input    -- ^ Old input
                    -> Input    -- ^ New input
                    -> Int      -- ^ Startcode
                    -> Int      -- ^ Input size
                    -> [T]}

-- | Output one token
{-# INLINE token #-}
token f = Action $ \scanner old_inp inp sc n ->
  T (inputPos old_inp) (f (inputString old_inp) n) : scanner inp sc

idTok :: Action
idTok = token $ \text n -> IdTok (take n text)

intTok :: Action
intTok = token $ \text n -> IntTok (read $ take n text)

tok :: Token -> Action
tok t = token $ \_ _ -> t

-- | Consume a CPP line directive.  The directive is used to update the
-- current source position.
lineDirective :: Action
lineDirective = Action $ \scanner old_inp inp sc n ->
  let directive = take n $ inputString old_inp
      inp' = inp {inputPos = source_position directive}
  in scanner inp' sc
  where
    -- The directive reports the line number of the _next_ line.  Subtract
    -- 1 to get the current line.
    source_position directive = fileSourcePos filename (line - 1) 1
      where
        -- Remove the initial '#' from directive
        directive1 = eatSpaces $ tail directive
      
        -- Get line number
        (line, eatSpaces -> directive2):_ = reads directive1
      
        -- Get file name
        (filename, _):_ = reads directive2

    eatSpaces s = dropWhile isSpace s