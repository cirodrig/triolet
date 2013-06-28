
module LLParser.Parser(parseFile)
where

import Control.Applicative hiding((<|>))
import Control.Monad
import Data.List
import Text.ParserCombinators.Parsec hiding(string)
import qualified Text.ParserCombinators.Parsec.Pos as Parsec
import Text.ParserCombinators.Parsec.Expr

import qualified Common.SourcePos
import Common.Label
import LowLevel.Types
import LowLevel.Record(Mutability(..))
import LLParser.Lexer
import LLParser.AST

type P a = GenParser T () a

toParsecPos :: Common.SourcePos.SourcePos -> Parsec.SourcePos
toParsecPos pos =
  let Just filename = Common.SourcePos.sourceFile pos 
      Just line = Common.SourcePos.sourceLine pos
      Just col = Common.SourcePos.sourceColumn pos
  in Parsec.newPos filename line col

fromParsecPos :: Parsec.SourcePos -> Common.SourcePos.SourcePos
fromParsecPos pos =
  let filename = Parsec.sourceName pos 
      line = Parsec.sourceLine pos
      col = Parsec.sourceColumn pos
  in Common.SourcePos.fileSourcePos filename line col

tPos (T pos _) = pos
tToken (T _ t) = t

nextParsecPos _ _ (t:_) = toParsecPos $ tPos t
nextParsecPos _ t []    = toParsecPos $ tPos t

matchAny :: [Token] -> P ()
matchAny ts = tokenPrim showT nextParsecPos match_any
  where
    match_any t' | any (tToken t' ==) ts = Just ()
                 | otherwise = Nothing

match :: Token -> P ()
match t = tokenPrim showT nextParsecPos match_token <?> showToken t
  where
    match_token t' | t == tToken t' = Just ()
                   | otherwise      = Nothing

name :: P String
name = tokenPrim showT nextParsecPos get_name
  where
    get_name t =
      case tToken t
      of IdTok s [] -> Just s
         _          -> Nothing

identifier :: P Identifier
identifier = do (n, tags) <- tokenPrim showT nextParsecPos get_identifier
                tags' <- mapM convert_tag tags
                return $ Identifier n tags'
  where
    get_identifier t =
      case tToken t
      of IdTok s tags -> Just (s, tags)
         _            -> Nothing

    convert_tag tag =
      case stringLabelTag tag
      of Just t | not $ isEntryPointTag t -> return t
         _ -> fail $ "'" ++ tag ++ "' is not a valid tag"

fromIdentifier :: Identifier -> P String
fromIdentifier (Identifier name []) = return name
fromIdentifier _ = mzero <?> "identifier"

string :: P String
string = tokenPrim showT nextParsecPos get_string
  where
    get_string t = case tToken t
                        of StringTok s -> Just s
                           _ -> Nothing

parseModuleName :: P ModuleName
parseModuleName = do
  components <- name `sepBy1` match DotTok
  return $ ModuleName $ intercalate "." components

fullyQualifiedName :: P (ModuleName, Identifier)
fullyQualifiedName = do
  (dotted_prefix, end) <- dotname
  when (null dotted_prefix) $ fail "must provide a fully-qualified name"
  let mod = ModuleName (intercalate "." dotted_prefix)
  return (mod, end)
  where
    dotname = go id
      where
        go hd =
          let dotted_prefix = do n <- try (name <* match DotTok)
                                 go (hd . (n:))
              end = do i <- identifier
                       return (hd [], i)
          in dotted_prefix <|> end

integer :: P Integer
integer = tokenPrim showT nextParsecPos get_int
  where
    get_int t = case tToken t
                of IntTok n -> Just n
                   _ -> Nothing

floating :: P Double
floating = tokenPrim showT nextParsecPos get_int
  where
    get_int t = case tToken t
                of FltTok n -> Just n
                   _ -> Nothing

parens :: P a -> P a
parens p = do
  match LParenTok
  x <- p
  match RParenTok
  return x

parenList :: P a -> P [a]
parenList p = parens $ p `sepBy` match CommaTok

braces :: P a -> P a
braces p = do
  match LBraceTok
  x <- p
  match RBraceTok
  return x

-- | Override the default Show behavior of 'String'
newtype ShowString = ShowString String

instance Show ShowString where show (ShowString s) = s

endOfFile :: P ()
endOfFile = notFollowedBy $ tokenPrim showT nextParsecPos anything
  where
    anything t = Just $ ShowString $ showT t

-------------------------------------------------------------------------------

parseType :: P (Type Parsed)
parseType = prim_type <|> record_type <?> "type"
  where
    prim_type = choice [match tok >> return (PrimT typ)
                       | (tok, typ) <- primtypes]
    primtypes = [ (BoolTok, BoolType)
                , (CursorTok, CursorType)
                , (Int8Tok, IntType Signed S8)
                , (Int16Tok, IntType Signed S16)
                , (Int32Tok, IntType Signed S32)
                , (Int64Tok, IntType Signed S64)
                , (UInt8Tok, IntType Unsigned S8)
                , (UInt16Tok, IntType Unsigned S16)
                , (UInt32Tok, IntType Unsigned S32)
                , (UInt64Tok, IntType Unsigned S64)
                , (UnitTok, UnitType)
                , (FloatTok, FloatType S32)
                , (DoubleTok, FloatType S64)
                , (OwnedTok, OwnedType)
                , (PointerTok, PointerType)]

    record_type = do
      nm <- name
      let rt = mkNamedT nm :: Type Parsed
      try (type_app rt) <|> return rt
      where
        type_app rt = do
          args <- parseTypeArgs
          return $ AppT rt args

-- | Parse a type of a global object.  The only valid types
-- are \'owned\' or \'pointer\'.
parseGlobalType :: P PrimType
parseGlobalType = owned_type <|> pointer_type <?> "'owned' or 'pointer' type"
  where
    owned_type = match OwnedTok >> return OwnedType
    pointer_type = match PointerTok >> return PointerType

-- | Parse a type argument list.
parseTypeArgs :: P [TypeArg Parsed]
parseTypeArgs = parenList type_arg
  where
    type_arg = (match ValueTok >> fmap ExprArg expr) <|> fmap TypeArg parseType

field :: P (Field Parsed)
field = do
  liftM3 Field parseType fields cast <?> "field offset specifier"
  where
    fields = many1 fieldSpec
    cast = optionMaybe (match AsTok >> parseType)

fieldSpec = record_field <|> array_index <?> "field specifier"
  where
    record_field = do
      match DotTok
      field_name <- name
      return $ RecordFS field_name
    
    array_index = do
      match LBracketTok
      ix <- expr
      match RBracketTok
      return $ ArrayFS ix

-- | Operators recognized by the parser
operators =
  [ [ Prefix (unaryOp NotTok NotOp)
    , Prefix (unaryOp ComplementTok ComplementOp)]
  , [ Infix (binaryOp StarTok MulOp) AssocLeft
    , Infix (binaryOp PercentTok ModOp) AssocNone
    , Infix (binaryOp IntegerDivideTok IntDivOp) AssocNone
    , Infix (binaryOp DivideTok DivOp) AssocNone]
  , [ Prefix (unaryOp MinusTok NegateOp)]
  , [ Infix (binaryOp DerefPlusTok AtomicAddOp) AssocNone
    , Infix (binaryOp PointerPlusTok PointerAddOp) AssocLeft
    , Infix (binaryOp PointerMinusTok PointerSubOp) AssocLeft
    , Infix (binaryOp PlusTok AddOp) AssocLeft
    , Infix (binaryOp MinusTok SubOp) AssocLeft]
  , [ Infix (binaryOp EqualTok CmpEQOp) AssocNone
    , Infix (binaryOp NotEqualTok CmpNEOp) AssocNone
    , Infix (binaryOp LessThanTok CmpLTOp) AssocNone
    , Infix (binaryOp LessEqualTok CmpLEOp) AssocNone
    , Infix (binaryOp GreaterThanTok CmpGTOp) AssocNone
    , Infix (binaryOp GreaterEqualTok CmpGEOp) AssocNone]
  , [ Infix (binaryOp AndTok AndOp) AssocLeft]
  , [ Infix (binaryOp OrTok OrOp) AssocLeft]
  ]
  where
    binaryOp tok op = match tok >> return (\x y -> BinaryE op x y)
    unaryOp tok op = match tok >> return (\x -> UnaryE op x)

expr = buildExpressionParser operators fieldExpr

fieldExpr :: P (Expr Parsed)
fieldExpr = do
  e <- castExpr
  postfixes e
  where
    postfixes e =
      (match AtTok >> offset_expr e >>= postfixes) <|>
      (match FieldTok >> deref_expr e >>= postfixes) <|>
      return e

    -- Parse the rest of an offset expression "e @ field"
    offset_expr e = do
      f <- field
      return $ FieldE e f
    
    -- Parse the rest of a dereference expression "e @! field"
    deref_expr e = do
      f <- field
      return $ LoadFieldE e f
      
castExpr :: P (Expr Parsed)
castExpr = do
  e <- basicExpr
  choice [ match AsTok >> cast_expr e
         , return e
         ]
  where
    cast_expr e = do
      ty <- parseType
      return $ CastE e ty

-- Match expressions that start with an identifier or literal type.
basicExpr :: P (Expr Parsed)
basicExpr =
  sizeof_expr <|> alignof_expr <|> base_expr <|>
  (identifier >>= basicExprWithIdentifier) <|>
  (parseType >>= basicExprWithType) <|>
  try (parenList parseType >>= basicExprWithTypes) <|>
  derefExpr
  where
    sizeof_expr = do
      match SizeofTok 
      fmap SizeofE parseType
    alignof_expr = do
      match AlignofTok 
      fmap AlignofE parseType
    base_expr = do
      match BaseTok
      fmap BaseE atomicExpr

-- Parse an expression that began with an identifier 
basicExprWithIdentifier :: Identifier -> P (Expr Parsed)
basicExprWithIdentifier id =
  try basicExprWithRecordType <|> varE
  where
    -- Parse an expression that begins with a record type
    -- Either a record construction, or some expression that has that
    -- return type 
    basicExprWithRecordType = do
      args <- optionMaybe parseTypeArgs
      id_name <- fromIdentifier id
      let base_record_type = mkNamedT id_name
      let record_type =
            case args
            of Nothing -> base_record_type
               Just ts -> AppT base_record_type ts
      recordE record_type <|> basicExprWithType record_type
      
    -- A record construction
    recordE record_type =
      RecordE record_type `liftM` braces (expr `sepBy` match CommaTok)
    
    varE = return $ VarE id

-- | Parse an expression that began with a type.
basicExprWithType ty =
  intLitE <|> floatLitE <|> loadE <|> basicExprWithTypes [ty]
  where
    intLitE = fmap (IntLitE ty) integer
    
    floatLitE = fmap (FloatLitE ty) floating

    loadE = do
      match LoadTok
      addr <- derefExpr
      return $ LoadE ty addr

-- | Parse an expression that begain with a type list.
basicExprWithTypes tys = callE
  where
    callToken = (match CallTok >> return (CallE tys)) <|>
                (match PrimCallTok >> return (PrimCallE tys))

    callE = callToken `ap` derefExpr `ap` derefExprList

derefExprList = parenList expr <|> fmap (:[]) derefExpr

derefExpr = deref <|> atomicExpr
  where
    deref = do
      match DerefTok
      e <- atomicExpr
      return $ DerefE e

-- | An atomic expression.  Expressions are atomic if they are not made of 
-- parts separated by spaces.
atomicExpr = fmap VarE identifier <|> true_lit <|> false_lit <|>
             nil_lit <|> null_lit <|> wild <|> parens expr
  where
    true_lit = match TrueTok >> return (BoolLitE True)
    false_lit = match FalseTok >> return (BoolLitE False)
    nil_lit = match NilTok >> return NilLitE
    null_lit = match NullTok >> return NullLitE
    wild = match WildTok >> return WildE

-- | An lvalue is parsed as an expression, then converted to an lvalue if
-- it appears in lvalue context.
-- This consumes no input, but may cause a parse error.
exprToLValue :: Expr Parsed -> P (LValue Parsed)
exprToLValue (VarE v) = return $ VarL v
exprToLValue (DerefE e) = return $ StoreL e
exprToLValue (LoadFieldE base off) = return $ StoreFieldL base off
exprToLValue (RecordE rec fields) =
  fmap (UnpackL rec) $ mapM exprToLValue fields
exprToLValue WildE = return $ WildL
exprToLValue _ = fail "LHS of assignment is not an lvalue"

-- | An expression list found in a statement.
-- To resolve ambiguity, the expression list must be followed by an equal
-- sign or semicolon.
stmtExprList = try (fmap (:[]) expr) <|> parenList expr

atom :: P (Atom Parsed)
atom = fmap ValA stmtExprList

-- | Parse a block of statements
block :: P (Stmt Parsed)
block = braces statements

-- | Parse a sequence of statements
statements :: P (Stmt Parsed)
statements = if_stmt <|> letrec_stmt <|> typedef_stmt <|> membar_stmt <|> let_or_atom
  where
    -- An 'if' statement
    if_stmt = do
      match IfTok
      cond <- parens expr
      if_true <- block
      match ElseTok
      if_false <- if_stmt <|> (block <* match SemiTok)
      return $ IfS cond if_true if_false Nothing
    
    -- A 'while' statement
    while_stmt = do
      match WhileTok
      inits <- parenList $ do param <- parameter
                              match AssignTok
                              val <- expr
                              return (param, val)
      cond <- parens expr
      body <- block
      match SemiTok
      return $ WhileS inits cond body Nothing

    -- A 'letrec' statement
    letrec_stmt = do
      match LetrecTok
      fdefs <- braces $ functionDef `sepBy` match SemiTok
      match SemiTok
      body <- statements
      return $ LetrecS fdefs body

    -- A memory barrier statement
    membar_stmt = do
      match MemoryBarrierTok
      match SemiTok
      body <- statements
      return $ MemoryBarrierS body

    -- A 'typedef' statement
    typedef_stmt = do
      match TypedefTok
      typename <- name
      match AssignTok
      ty <- parseType
      match SemiTok
      body <- statements
      return $ TypedefS typename ty body

    -- A statement starting with an expression list: either assignment or
    -- the end of the block
    let_or_atom = do
      es <- stmtExprList
      assignment es <|> end_block es

    -- An assignment statement (LHS = RHS; ...)
    assignment lhs_expressions = do
      match AssignTok
      lvalues <- mapM exprToLValue lhs_expressions
      assign_if lvalues <|> assign_while lvalues <|> assign_atom lvalues
    
    -- An if assignment (LHS = if () {...} else {...}; ...)
    assign_if lvalues = do
      (IfS cond if_true if_false Nothing) <- if_stmt
      tail <- statements
      return $ IfS cond if_true if_false (Just (lvalues, tail))

    -- A while assignment (LHS = while (inits) (cond) {...}; ...)
    assign_while lvalues = do
      (WhileS inits cond body Nothing) <- while_stmt
      tail <- statements
      return $ WhileS inits cond body (Just (lvalues, tail))

    -- Create an assignment statement (LHS = RHS; ...)
    assign_atom lvalues = do
      rhs <- atom
      match SemiTok
      tail <- statements
      return $ LetS lvalues rhs tail
    
    end_block es = do
      match SemiTok
      return $ ReturnS (ValA es)

-------------------------------------------------------------------------------
-- Definitions

maybeIdentifier = fmap Just identifier <|> (match WildTok >> return Nothing)

parameter :: P (Parameter Parsed)
parameter = liftM2 Parameter parseType maybeIdentifier

parameters :: P (Parameters Parsed)
parameters = parenList parameter

-- | Parse a list of type parameters
recordParameters :: P [String]
recordParameters = parenList name

recordDef :: P (RecordDef Parsed)
recordDef = do
  match RecordTok
  nm <- name
  params <- option [] recordParameters
  fields <- braces $ fieldDef `sepEndBy` match SemiTok
  return $ mkRecordDef nm params fields

mutability :: P Mutability
mutability = (match ConstTok >> return Constant) <|> return Mutable

fieldDef :: P (FieldDef Parsed)
fieldDef = liftM3 FieldDef mutability parseType name

dataDef :: P (DataDef Parsed)
dataDef = do
  match DataTok
  
  -- Read a type, which must be 'owned' or 'pointer'
  data_type <- parseGlobalType

  name <- identifier
  match AssignTok
  value <- expr
  return $ DataDef name data_type value

-- | Parse a function body
parseFunctionBody :: P ([Parameter Parsed], Stmt Parsed)
parseFunctionBody = braces $ do
  locals <- local_data `sepEndBy` match SemiTok
  body <- statements
  return (locals, body)
  where
    local_data = do
      match DataTok
      ty <- parseType
      name <- identifier
      return $ Parameter ty (Just name)

-- | Parse a function or procedure definition
functionDef :: P (FunctionDef Parsed)
functionDef = do
  is_procedure <- choice [ match FunctionTok >> return False 
                         , match ProcedureTok >> return True]
  should_inline <- (match InlineTok >> return True) <|> return False
  name <- identifier
  params <- parameters
  match ArrowTok
  returns <- fmap (:[]) parseType <|> parenList parseType
  (locals, body) <- parseFunctionBody
  return $ FunctionDef { functionName = name 
                       , functionIsProcedure = is_procedure 
                       , functionInlineRequest = should_inline
                       , functionLocals = locals
                       , functionParams = params 
                       , functionReturns = returns 
                       , functionBody = body}

topLevelDefs :: P [Def Parsed]
topLevelDefs = do defs <- def `sepEndBy` match SemiTok
                  endOfFile
                  return defs
  where
    def = choice [ fmap FunctionDefEnt functionDef
                 , fmap DataDefEnt dataDef
                 , fmap RecordDefEnt recordDef]

-------------------------------------------------------------------------------
-- Module parsing

-- | Parse an external declaration
--    
-- @(extern | import)
--    (data type | function | procedure)
--    (fqn [string] | identifier [string])
--    (parameter_type_list -> return_type_list)?@
externDecl :: P (ExternDecl Parsed)
externDecl = extern_decl <|> import_decl
  where
    extern_decl = match ExternTok >> parse_decl make_extern_decl
      where    
        make_extern_decl = do
          (mod, name@(Identifier nm tags)) <- fullyQualifiedName
          c_name <- optionMaybe string
          let label_ext = externLabel mod nm tags c_name
          return $ \t -> ExternDecl t label_ext
    
    import_decl = match ImportTok >> parse_decl make_import_decl
      where
        make_import_decl = do
          local_name@(Identifier nm tags) <- identifier
          c_name <- option nm string
          let label = externLabel builtinModuleName nm tags (Just c_name)
          return $ \t -> ImportDecl t label local_name

    parse_decl :: P (ExternType Parsed -> ExternDecl Parsed)
               -> P (ExternDecl Parsed)
    parse_decl parse_name = parse_data <|> parse_function
      where
        parse_data = do
          match DataTok
          extern_type <- parseGlobalType
          mk <- parse_name
          return $ mk (ExternData extern_type)
        
        parse_function = do
          is_procedure <- choice [ match FunctionTok >> return False 
                                 , match ProcedureTok >> return True]
          mk <- parse_name
          params <- type_list
          match ArrowTok
          returns <- type_list
          return $ mk $ if is_procedure
                        then ExternProcedure params returns
                        else ExternFunction params returns

        type_list =
          fmap (:[]) parseType <|> parenList parseType

parseModule :: P (ModuleName, [ExternDecl Parsed], [Def Parsed])
parseModule = do
  -- Parse the module name declaration
  match ModuleTok
  mn <- parseModuleName
  match SemiTok
  
  -- Parse 'extern' declarations
  exts <- externDecl `sepEndBy` match SemiTok
  
  -- Parse definitions
  defs <- topLevelDefs
  
  return (mn, exts, defs)

-------------------------------------------------------------------------------

-- | Test the parser on a string.  For debugging.
testParse :: String -> P a -> a
testParse text parser =
  let tokens = lexFile "<test>" text
  in case runParser parser () "<test>" tokens
     of Left err -> error (show err)
        Right x -> x

parseFile :: FilePath -> String
          -> IO (ModuleName, [ExternDecl Parsed], [Def Parsed])
parseFile path text =
  let tokens = lexFile path text
  in case runParser parseModule () path tokens
     of Left err -> fail (show err)
        Right x -> return x