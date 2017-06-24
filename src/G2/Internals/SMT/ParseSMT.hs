module G2.Internals.SMT.ParseSMT (parseSMT) where

import G2.Internals.SMT.Language

import Data.Ratio
-- | SMT Parser
-- This is not complete!  It currently only covers the small amount of the SMT
-- language needed to parse models

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

smtDef =
    emptyDef { Token.commentStart = ""
             , Token.commentEnd = ""
             , Token.commentLine = ";"
             , Token.nestedComments = False
             , Token.identStart = letter <|> oneOf ident
             , Token.identLetter = alphaNum <|> oneOf ident
             , Token.reservedNames = ["let", "-"]}

ident = ['~', '!', '@', '%', '^', '&', '*' , '_', '-', '+', '=', '<', '>', '.', '?', '/']

smtLexer = Token.makeTokenParser smtDef

identifier = Token.identifier smtLexer
reserved = Token.reserved smtLexer
integer = Token.integer smtLexer
floatT = Token.float smtLexer
whiteSpace = Token.whiteSpace smtLexer
parens = Token.parens smtLexer

smtParser :: Parser SMTAST
smtParser = whiteSpace >> sExpr

sExpr :: Parser SMTAST
sExpr = parens sExpr <|> letExpr <|> consExpr <|> try doubleFloatExpr <|> intExpr

letExpr :: Parser SMTAST
letExpr = do
    reserved "let"
    bEx <- parens (parens identExprTuple)
    ex <- sExpr
    return $ SLet bEx ex

identExprTuple :: Parser (Name, SMTAST)
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

doubleFloatExpr :: Parser SMTAST
doubleFloatExpr = do
    s <- optionMaybe (reserved "-")
    f <- floatT
    let r = approxRational f (0.00001)
    case s of 
        Just _ -> return (VDouble (-r))
        Nothing -> return (VDouble r)

parseSMT :: String -> SMTAST
parseSMT s = case parse smtParser "" s of
    Left e -> error $ show e
    Right r -> r