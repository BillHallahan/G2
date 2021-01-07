module G2.Solver.ParseSMT
    ( parseSMT
    , parseGetValues) where

import G2.Solver.Language

import Data.Char
import Data.Ratio
import Numeric
import qualified Text.Builder as B

import Text.Parsec (Parsec)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

-- This is not complete!  It currently only covers the small amount of the SMT
-- language needed to parse models

smtDef :: LanguageDef st
smtDef =
    emptyDef { Token.commentStart = ""
             , Token.commentEnd = ""
             , Token.commentLine = ";"
             , Token.nestedComments = False
             , Token.identStart = letter <|> oneOf ident
             , Token.identLetter = alphaNum <|> oneOf ident
             , Token.reservedNames = ["as", "let", "-", "/", "\""]}

ident :: [Char]
ident = ['~', '!', '$', '@', '%', '^', '&', '*' , '_', '-', '+', '=', '<', '>', '.', '?', '/']

smtLexer :: Token.TokenParser st
smtLexer = Token.makeTokenParser smtDef

identifier :: Parsec String st String
identifier = Token.identifier smtLexer

reserved :: String -> Parsec String st ()
reserved = Token.reserved smtLexer

integer :: Parsec String st Integer
integer = Token.integer smtLexer

floatT :: Parsec String st Double
floatT = try (Token.float smtLexer)

flexFloatT :: Parsec String st Double
flexFloatT = try (Token.float smtLexer) <|> return . fromInteger =<< integer

whiteSpace :: Parsec String st ()
whiteSpace = Token.whiteSpace smtLexer

parens :: Parsec String st a -> Parsec String st a
parens = Token.parens smtLexer

smtParser :: Parser SMTAST
smtParser = whiteSpace >> sExpr

getValuesParser :: Parser SMTAST
getValuesParser = parens (parens (identifier >> sExpr))

sExpr :: Parser SMTAST
sExpr = try boolExpr <|> parens sExpr <|> letExpr <|> try doubleFloatExpr
                     <|> try doubleFloatExprDec <|> stringExpr <|> intExpr

letExpr :: Parser SMTAST
letExpr = do
    reserved "let"
    bEx <- parens (parens identExprTuple)
    ex <- sExpr
    return $ SLet bEx ex

identExprTuple :: Parser (SMTName, SMTAST)
identExprTuple = do
    bind <- identifier
    ex <- sExpr
    return (bind, ex)

boolExpr :: Parser SMTAST
boolExpr = do
    n <- parensConsName <|> identifier
    case n of
        "true" -> return (VBool True)
        "false" -> return (VBool False)
        _ -> error $ "Bad bool expr"

parensConsName :: Parsec String st String
parensConsName = parens parensConsName <|> consName

consName :: Parsec String st String
consName = do
    reserved "as"
    ex <- identifier
    _ <- parens (many1 identifier)
    return ex

intExpr :: Parser SMTAST
intExpr = do
    s <- optionMaybe (reserved "-")
    i <- return . fromIntegral =<< integer
    case s of
        Just _ -> return (VInt (-i))
        Nothing -> return (VInt i)

doubleFloatExpr :: Parser SMTAST
doubleFloatExpr = doubleFloatExprNeg <|> doubleFloatExprRat

doubleFloatExprNeg :: Parser SMTAST
doubleFloatExprNeg = do
    _ <- reserved "-"
    (VDouble r) <- parens doubleFloatExprRat
    return (VDouble (-r))

doubleFloatExprRat :: Parser SMTAST
doubleFloatExprRat = do
    s <- optionMaybe (reserved "/")
    f <- flexDoubleFloat
    f' <- flexDoubleFloat
    let r = approxRational (f / f') (0.000001)
    case s of 
        Just _ -> return (VDouble r)
        Nothing -> return (VDouble r)

doubleFloatExprDec :: Parser SMTAST
doubleFloatExprDec = do
    r <- doubleFloat
    _ <- optionMaybe (reserved "?")
    return (VDouble r)

doubleFloat :: Parser Rational
doubleFloat = do
    s <- optionMaybe (reserved "-")
    f <- floatT
    let r = approxRational f (0.00001)
    case s of 
        Just _ -> return (-r)
        Nothing -> return r

flexDoubleFloat :: Parser Rational
flexDoubleFloat = do
    s <- optionMaybe (reserved "-")
    f <- flexFloatT
    let r = approxRational f (0.00001)
    case s of 
        Just _ -> return (-r)
        Nothing -> return r

stringExpr :: Parser SMTAST
stringExpr = do
    _ <- char '"'
    str <- stringExpr'
    _ <- char '"'
    return (VChar str)

stringExpr' :: Parser Char
stringExpr' = do
    try parseHex <|> choice (alphaNum:char '\\':char ' ':map char ident)

parseHex :: Parser Char
parseHex = do
    _ <- char '\\'
    _ <- char 'x'
    str <- many (choice . map char $ ['0'..'9'] ++ ['a'..'f'])
    case readHex str of
        [(c, _)] -> return $ chr c
        _ -> error $ "stringExpr': Bad string"

parseSMT :: String -> SMTAST
parseSMT s = case parse smtParser s s of
    Left e -> error $ "get model parser error on " ++ show e
    Right r -> r

-- | parseGetValues
-- Parse the result of a get-values call
parseGetValues :: String -> SMTAST
parseGetValues s =
    case parse getValuesParser s s of
        Left e -> error $ "get values parser error on " ++ show e
        Right r -> r
