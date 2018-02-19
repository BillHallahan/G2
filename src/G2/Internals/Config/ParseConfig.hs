module G2.Internals.Config.ParseConfig (parseConfig) where

import Text.ParserCombinators.Parsec.Language

import Text.Parsec (Parsec)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import qualified Data.Map as M
import Data.Maybe

configDef :: LanguageDef st
configDef =
    emptyDef { Token.commentStart = "{-"
             , Token.commentEnd = "-}"
             , Token.commentLine = "--"
             , Token.nestedComments = False
             , Token.identStart = noneOf [' ', '\t', '=', ',', '\n', '\r']
             , Token.identLetter = noneOf [' ', '\t', '=', ',', '\n', '\r']
             , Token.reservedNames = ["="]}

ident :: [Char]
ident = ['/', '.', '-', '_']

configLexer :: Token.TokenParser st
configLexer = Token.makeTokenParser configDef

identifier :: Parsec String st String
identifier = Token.identifier configLexer

reserved :: String -> Parsec String st ()
reserved = Token.reserved configLexer

eol :: Parser ()
eol = do
    oneOf "\n\r"
    return ()

spacedComma :: Parser ()
spacedComma = do
    spaces
    char ','
    spaces
    return ()

parseSetting :: Parser (String, [String])
parseSetting = do
    key <- identifier
    spaces
    char '='
    spaces
    val <- sepBy identifier spacedComma
    return (key, val)

parseLine :: Parser (String, [String])
parseLine = do
    kv <- parseSetting
    spaces <|> eof
    return kv

parseFile :: Parser [(String, [String])]
parseFile = many parseLine

parseConfig :: String -> IO (Either ParseError (M.Map String [String]))
parseConfig nm =
    parseFromFile parseFile nm >>= return . fmap (M.fromList)