module G2.Internals.Solver.ParseSMT
    (parseSMT) where

import G2.Internals.Solver.Language

import Data.Ratio
-- | SMT Parser
-- This is not complete!  It currently only covers the small amount of the SMT
-- language needed to parse models

import Text.Parsec (Parsec)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

smtDef :: LanguageDef st
smtDef =
    emptyDef { Token.commentStart = ""
             , Token.commentEnd = ""
             , Token.commentLine = ";"
             , Token.nestedComments = False
             , Token.identStart = letter <|> oneOf ident
             , Token.identLetter = alphaNum <|> oneOf ident
             , Token.reservedNames = ["let", "-", "/"]}

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
floatT = Token.float smtLexer

whiteSpace :: Parsec String st ()
whiteSpace = Token.whiteSpace smtLexer

parens :: Parsec String st a -> Parsec String st a
parens = Token.parens smtLexer

smtParser :: Parser SMTAST
smtParser = whiteSpace >> sExpr

sExpr :: Parser SMTAST
sExpr = parens sExpr <|> letExpr <|> consExpr <|> try doubleFloatExprRat <|> try doubleFloatExprDec <|> intExpr

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

consExpr :: Parser SMTAST
consExpr = do
    n <- identifier
    l <- optionMaybe (many1 sExpr)
    let l' = case l of 
                Just l'' -> l''
                Nothing -> []
    return $ Cons n l' (Sort "" [])

intExpr :: Parser SMTAST
intExpr = do
    s <- optionMaybe (reserved "-")
    i <- return . fromIntegral =<< integer
    case s of
        Just _ -> return (VInt (-i))
        Nothing -> return (VInt i)

doubleFloatExprRat :: Parser SMTAST
doubleFloatExprRat = do
    s <- optionMaybe (reserved "/")
    f <- doubleFloat
    f' <- doubleFloat
    let r = approxRational (f / f') (0.00001)
    case s of 
        Just _ -> return (VDouble r)
        Nothing -> return (VDouble r)

doubleFloatExprDec :: Parser SMTAST
doubleFloatExprDec = do
    r <- doubleFloat
    return (VDouble r)

doubleFloat :: Parser Rational
doubleFloat = do
    s <- optionMaybe (reserved "-")
    f <- floatT
    let r = approxRational f (0.00001)
    case s of 
        Just _ -> return (-r)
        Nothing -> return r

parseSMT :: String -> SMTAST
parseSMT s = case parse smtParser s s of
    Left e -> error $ show e
    Right r -> r