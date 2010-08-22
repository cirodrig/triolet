
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
        idTok, intTok, floatTok, stringTok, tok,
        lineDirective
       )
where

import Data.Char
import Gluon.Common.SourcePos

-- | A token produced by lexical analysis
data Token =
    IdTok !String
  | IntTok !Integer
  | FltTok !Double
  | StringTok !String
  | LBraceTok
  | RBraceTok
  | LParenTok
  | RParenTok
  | AssignTok
  | ArrowTok
  | SemiTok
  | CommaTok
  | EqualTok
  | NotEqualTok
  | LessThanTok
  | LessEqualTok
  | GreaterThanTok
  | GreaterEqualTok
  | DotTok
  | FieldTok
  | AtTok
  | DerefTok
  | PlusTok
  | MinusTok
  | PointerPlusTok
  | PercentTok
  | StarTok
  | DerefPlusTok
  | WildTok
  | AlignofTok
  | AsTok
  | BoolTok
  | BytesTok
  | CallTok
  | DataTok
  | DoubleTok
  | ElseTok
  | ExternTok
  | FalseTok
  | FloatTok
  | FunctionTok
  | IfTok
  | ImportTok
  | Int8Tok
  | Int16Tok
  | Int32Tok
  | Int64Tok
  | LoadTok
  | ModuleTok
  | NullTok
  | OwnedTok
  | PointerTok
  | PrimCallTok
  | ProcedureTok
  | RecordTok
  | SizeofTok
  | TrueTok
  | UInt8Tok
  | UInt16Tok
  | UInt32Tok
  | UInt64Tok
    deriving(Eq)

showToken :: Token -> String
showToken (IdTok s) = show s
showToken (IntTok n) = show n
showToken (FltTok d) = show d
showToken (StringTok s) = show s
showToken LBraceTok = "left brace"
showToken RBraceTok = "right brace"
showToken LParenTok = "left parenthesis"
showToken RParenTok = "right parenthesis"
showToken AssignTok = "equal sign"
showToken ArrowTok = "arrow"
showToken SemiTok = "semicolon"
showToken CommaTok = "comma"
showToken EqualTok = "equality operator"
showToken NotEqualTok = "disequality operator"
showToken LessThanTok = "less-than operator"
showToken LessEqualTok = "'<=' operator"
showToken GreaterThanTok = "greater-than operator"
showToken GreaterEqualTok = "'>=' operator"
showToken DotTok = "dot"
showToken FieldTok = "field operator"
showToken AtTok = "at operator"
showToken DerefTok = "exclamation mark"
showToken PlusTok = "plus"
showToken MinusTok = "minus"
showToken PointerPlusTok = "'^+'"
showToken PercentTok = "percent sign"
showToken StarTok = "asterisk"
showToken DerefPlusTok = "'!+'"
showToken WildTok = "wildcard"
showToken AlignofTok = "'alignof'"
showToken AsTok = "'as'"
showToken BoolTok = "'bool'"
showToken BytesTok = "'bytes'"
showToken CallTok = "'call'"
showToken DataTok = "'data'"
showToken DoubleTok = "'double'"
showToken ElseTok = "'else'"
showToken ExternTok = "'extern'"
showToken FalseTok = "'false'"
showToken FloatTok = "'float'"
showToken FunctionTok = "'function'"
showToken IfTok = "'if'"
showToken ImportTok = "'import'"
showToken Int8Tok = "'int8'"
showToken Int16Tok = "'int16'"
showToken Int32Tok = "'int32'"
showToken Int64Tok = "'int64'"
showToken LoadTok = "'load'"
showToken ModuleTok = "'module'"
showToken NullTok = "'null'"
showToken OwnedTok = "'owned'"
showToken PointerTok = "'pointer'"
showToken PrimCallTok = "'primcall'"
showToken ProcedureTok = "'procedure'"
showToken RecordTok = "'record'"
showToken SizeofTok = "'sizeof'"
showToken TrueTok = "'true'"
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

floatTok :: Action
floatTok = token $ \text n -> FltTok (read $ take n text)

stringTok :: Action
stringTok = token $ \text n -> StringTok (read $ take n text)

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