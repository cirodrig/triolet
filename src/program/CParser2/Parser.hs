
module CParser2.Parser(parseFile)
where

import Data.Maybe
import qualified Text.ParserCombinators.Parsec as PS
import qualified Text.ParserCombinators.Parsec.Prim as PS

import Text.Parsec.Expr

import Control.Applicative(Applicative(..), (<*), (*>), (<$>), (<**>))
import Control.Monad

import Text.ParserCombinators.Parsec((<|>), (<?>), unexpected, choice,
                                     option, optionMaybe, many, many1, endBy,
                                     sepEndBy, sepBy, sepBy1)

import CParser2.AST
import CParser2.Lexer
import Common.SourcePos as PySrcPos

-- | The parser type
type P a = PS.GenParser Token () a

-- Helper functions to get the character position into a usable form
toParsecSourcePos :: PySrcPos.SourcePos -> PS.SourcePos -> PS.SourcePos
toParsecSourcePos p template =
    flip PS.setSourceName (fj $ PySrcPos.sourceFile p) $
    flip PS.setSourceLine (fj $ PySrcPos.sourceLine p) $
    flip PS.setSourceColumn (fj $ PySrcPos.sourceColumn p) template
    where
      fj :: Maybe a -> a
      fj (Just x) = x
      fj Nothing  = internalError "Lost source position in parser"

fromParsecSourcePos :: PS.SourcePos -> PySrcPos.SourcePos
fromParsecSourcePos p =
    fileSourcePos (PS.sourceName p) (PS.sourceLine p) (PS.sourceColumn p)

nextPosition parsec_p _ (Token p _:_) = toParsecSourcePos p parsec_p
nextPosition parsec_p (Token p _) _   = toParsecSourcePos p parsec_p

internalError :: String -> a
internalError msg = error $ "Internal error:\n" ++ msg

locatePosition :: P SourcePos
locatePosition = fmap fromParsecSourcePos PS.getPosition

located :: P t -> P (Located t)
located p = do
 -- Get the current source position
 loc <- locatePosition
 -- Parse a 't', by running the parser you received
 unloc <- p
 -- Put the position and 't' into a 'Located t'
 return $ L loc unloc

-------------------------------------------------------------------------------
-- * Primitive parsers

-- | Succeed iff the specified token appears next in the input stream.
match :: Tok -> P ()
match t = PS.tokenPrim showToken nextPosition matchAndReturn
    where
      matchAndReturn (Token _ t')
          | t == t'   = Just ()
          | otherwise = Nothing

-- | Return the identifier name that appears next in the input stream; fail if
-- not an identifier.
identifier :: P String
identifier = PS.tokenPrim showToken nextPosition matchAndReturn
    where
      matchAndReturn (Token _ (IdentTok s)) = Just s
      matchAndReturn _                      = Nothing

-- | Return the integer that appears next in the input stream; fail if
-- not an integer.
int :: P Integer
int = PS.tokenPrim showToken nextPosition matchAndReturn
    where
      matchAndReturn (Token _ (IntTok n)) = Just n
      matchAndReturn _                    = Nothing

eof :: P ()
eof = PS.getInput >>= acceptEOF
    where
      acceptEOF []    = return ()
      acceptEOF (x:_) = unexpected (showToken x) <?> "end of file"

-- Matched Parentheses
parens :: P a -> P a
parens = PS.between (match LParenTok) (match RParenTok)

-- Matched braces
braces :: P a -> P a
braces = PS.between (match LBraceTok) (match RBraceTok)

-- Matched brackets
brackets :: P a -> P a
brackets = PS.between (match LBracketTok) (match RBracketTok)

semi :: P ()
semi = match SemiTok

after :: P terminator -> P b -> P b
q `after` p = p <* q

(<*#) :: P a -> Tok -> P a
p <*# t = p <* match t

commaList :: P a -> P [a]
commaList p = parens $ p `sepBy` match CommaTok

-------------------------------------------------------------------------------
-- * Attributes

attributeList :: P [Attribute]
attributeList = option [] (match AttributeTok >> commaList attr)

attr :: P Attribute
attr = do
  name <- identifier
  fromMaybe (fail "Unrecognized attribute") $ lookup name attr_table
  where
    attr_table =
      [("abstract", return AbstractAttr)]

-------------------------------------------------------------------------------
-- * Type parsing

-- | Parse a type
pType :: P PLType
pType = dependent_function <|> function
  where
    dependent_function = do
      pos <- locatePosition
      dom <- PS.try (parens pDomains)
      match ArrowTok
      rng <- pType
      return $ foldr (\x y -> L pos (AllT x y)) rng dom

    -- Parse a function or application
    function = do
      loc <- locatePosition
      ty <- pAppType
      function_rest loc ty <|> return ty
    
    function_rest pos domain = do
      match ArrowTok
      rng <- pType
      return $ L pos (FunT domain rng)

-- | Parse a type application
pAppType :: P PLType
pAppType = fmap mk_apps $ many1 pTypeAtom
  where
    mk_apps (t:ts) = foldl mk_app t ts
    mk_app t1 t2 = L (getSourcePos t1) (AppT t1 t2)

-- | Parse an atomic type: an int, variable, or parenthesized expression
pTypeAtom :: P PLType
pTypeAtom = int_type <|> var_type <|> parens pType
  where
    int_type = located $ IntIndexT <$> int
    var_type = located $ VarT <$> identifier

pDomain :: P PDomain
pDomain = do
  v <- identifier
  match ColonTok
  ty <- pType
  return (Domain v ty)

-- | Parse one or more variable bindings that may appear on the LHS of a 
--   function arrow.  The multiple variable binding case @(a b : T) -> c@
--   is shorthand for @(a : T) -> (b : T) -> c@.
pDomains :: P [PDomain]
pDomains = do
  vs <- many1 identifier
  match ColonTok
  ty <- pType
  return [Domain v ty | v <- vs]

-------------------------------------------------------------------------------
-- * Declarations

pDataDecl :: P PLDecl
pDataDecl = located $ do
  match DataTok
  tycon <- identifier
  match ColonTok
  kind <- pType
  attrs <- attributeList
  datacons <- braces $ pDataConDecl `sepEndBy` match SemiTok
  return $ Decl tycon $ DataEnt kind datacons attrs
  
pDataConDecl :: P (LDataConDecl Parsed)
pDataConDecl = located $ do
  datacon <- identifier
  params <- commaList pDomain
  ex_types <- commaList pDomain
  args <- commaList pType
  return $ DataConDecl datacon params ex_types args

pTypeDecl :: P PLDecl
pTypeDecl = located $ do
  match TypeTok
  tycon <- identifier
  match ColonTok
  kind <- pType
  return $ Decl tycon $ TypeEnt kind Nothing

pVarDecl :: P PLDecl
pVarDecl = located $ do
  v <- identifier
  match ColonTok
  kind <- pType
  return $ Decl v $ VarEnt kind

pDecl = pDataDecl <|> pTypeDecl <|> pVarDecl <?>
        "type, data, or variable declaration"

pModule :: P PModule
pModule = Module <$> pDecl `sepEndBy` match SemiTok <* eof


-- | Parse a sequence of tokens.  Returns an AST.
parseFile :: FilePath -> [Token] -> IO PModule
parseFile path tokens =
  case PS.runParser pModule () path tokens
  of Left err -> do
       print err
       fail "Parsing failed"
     Right m -> do
       return m
       
