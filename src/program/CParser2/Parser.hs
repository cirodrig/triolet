
{-# LANGUAGE ViewPatterns #-}
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
-- * Expressions
  
pExp :: P PLExp
pExp = caseE <|> ifE <|> lamE <|> letfunE <|> exceptE <|> appExp <?> "expression"

caseE :: P PLExp
caseE = located $ do
  match CaseTok
  scrutinee <- pExp
  match OfTok
  alts <- alt_list <|> one_alt
  return $ CaseE scrutinee alts
  where
    one_alt = (:[]) <$> pAlt
    alt_list = braces $ pAlt `sepBy` match SemiTok

ifE :: P PLExp
ifE = located $ do
  match IfTok
  scrutinee <- pExp
  then_pos <- locatePosition
  match ThenTok
  x <- pExp
  else_pos <- locatePosition
  match ElseTok
  y <- pExp
  return $ CaseE scrutinee [ L then_pos $ Alt "True" [] [] [] x
                           , L else_pos $ Alt "False" [] [] [] y]

lamE :: P PLExp
lamE = located $ do
  match BackslashTok
  tparams <- typeParameters
  params <- parameters
  match ArrowTok
  range <- pType 
  match DotTok
  body <- pExp
  return $ LamE (Fun tparams params range body)

letfunE :: P PLExp
letfunE = located $ do
  match LetfunTok
  defs <- def_list <|> one_def
  match InTok
  body <- pExp
  return $ LetfunE defs body
  where
    one_def = (:[]) <$> def
    def_list = braces $ def `sepBy` match SemiTok

exceptE :: P PLExp
exceptE = located $ do
  match ExceptTok
  match AtTok
  t <- pTypeAtom
  return $ ExceptE t

def :: P (LDef Parsed)
def = located $ do
  v <- identifier
  (ty_params, params, range) <- funSignature
  match EqualTok
  body <- pExp
  return $ Def v (Fun ty_params params range body)

-- | An expression involving application or something with higher precedence
appExp :: P PLExp
appExp = do
  loc <- locatePosition
  operator <- atomicExp 
  apply loc operator
  where
    -- Apply to any operands we can find.
    -- This function is recursive to handle multiple (left-associative)
    -- applications.
    apply loc f = type_app <|> app <|> return f
      where
        type_app = do
          match AtTok
          operand <- pTypeAtom  -- Non-atomic types must be parenthesized

          -- Parse additional operands
          apply loc (L loc $ TAppE f operand)
        
        app = do
          operand <- atomicExp  -- Non-atomic expressions must be parenthesized
          apply loc (L loc $ AppE f operand)

atomicExp = varE <|> intE <|> parens pExp

varE :: P PLExp
varE = located (VarE <$> identifier) <?> "variable"

intE :: P PLExp
intE = located (IntE <$> int) <?> "integer"

-- | Parse a case alternative
pAlt :: P PLAlt
pAlt = located $ do
  con <- identifier
  targs <- many type_arg
  tparams <- typeParameters
  params <- parameters
  match DotTok
  body <- pExp
  return $ Alt con targs tparams params body
  where
    type_arg = PS.try (match AtTok >> pTypeAtom)

typeParameters :: P [PDomain]
typeParameters = fmap concat $ many (match AtTok >> parens pDomains)

parameters :: P [PDomain]
parameters = fmap concat $ many (parens pDomains)

-- | Parse a function signature.
--
-- > @(t1 : k1) @(t2 : k2) ... (x1 : T1) (x2 : T2) ... -> T
funSignature :: P ([PDomain], [PDomain], PLType)
funSignature = do
  tparams <- typeParameters
  params <- parameters
  match ArrowTok
  range <- pType
  return (tparams, params, range)

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
  -- If the second token is a colon, then this is a variable declaration 
  -- Otherwise it might be some other kind of declaration
  v <- PS.try (identifier <* match ColonTok)
  kind <- pType
  return $ Decl v $ VarEnt kind

pFunDecl :: P PLDecl
pFunDecl = do
  pos <- locatePosition
  v <- identifier
  (ty_params, params, range) <- funSignature
  match EqualTok
  body <- pExp
  return $ L pos $ Decl v $ FunEnt (L pos (Fun ty_params params range body))

pDecl = pDataDecl <|> pTypeDecl <|> pVarDecl <|> pFunDecl <?>
        "type, data, variable, or function declaration"

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
       
