module G2.Config.ParseConfig (parseConfig) where

import Text.ParserCombinators.Parsec.Language

import Text.Parsec (Parsec)
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as Token

import qualified Data.Map as M

configDef :: LanguageDef st
configDef =
    emptyDef { Token.commentStart = "{-"
             , Token.commentEnd = "-}"
             , Token.commentLine = "--"
             , Token.nestedComments = False
             , Token.identStart = noneOf [' ', '\t', '=', ',', '\n', '\r']
             , Token.identLetter = noneOf [' ', '\t', '=', ',', '\n', '\r']
             , Token.reservedNames = ["="]}

configLexer :: Token.TokenParser st
configLexer = Token.makeTokenParser configDef

identifier :: Parsec String st String
identifier = Token.identifier configLexer

spacedComma :: Parser ()
spacedComma = do
    spaces
    _ <- char ','
    spaces
    return ()

parseSetting :: Parser (String, [String])
parseSetting = do
    key <- identifier
    spaces
    _ <- char '='
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
