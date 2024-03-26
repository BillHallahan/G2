module G2.Solver.ParseSMT
    ( parseSMT
    , parseGetValues) where

import G2.Solver.Language

import Data.Bits
import Data.Char
import Data.Ratio
import GHC.Float
import Numeric

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
             , Token.reservedNames = ["as", "let", "-", "/", "\"", "fp", "+zero", "-zero", "+oo", "-oo", "NaN"]}

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

smtParser :: Maybe Sort -> Parser SMTAST
smtParser srt = whiteSpace >> (sExpr srt)

getValuesParser :: Maybe Sort -> Parser SMTAST
getValuesParser srt = parens (parens (identifier >> (sExpr srt)))

sExpr :: Maybe Sort -> Parser SMTAST
sExpr srt = try boolExpr <|> parens (sExpr srt) <|> letExpr <|> try realExpr <|> try (doubleFloatExpr srt)
                         <|> try doubleFloatExprDec <|> stringExpr <|> intExpr

letExpr :: Parser SMTAST
letExpr = do
    reserved "let"
    bEx <- parens (parens identExprTuple)
    ex <- sExpr Nothing
    return $ SLet bEx ex

identExprTuple :: Parser (SMTName, SMTAST)
identExprTuple = do
    bind <- identifier
    ex <- sExpr Nothing
    return (bind, ex)

boolExpr :: Parser SMTAST
boolExpr = do
    n <- parensConsName <|> identifier
    case n of
        "true" -> return (VBool True)
        "false" -> return (VBool False)
        _ -> fail "not bool"

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

realExpr :: Parser SMTAST
realExpr = try realExprNeg <|> realExprRat

realExprNeg :: Parser SMTAST
realExprNeg = do
    _ <- reserved "-"
    VReal r <- parens realExprRat
    return (VReal (-r))

realExprRat :: Parser SMTAST
realExprRat = do
    s <- reserved "/"
    f <- integer
    _ <- char '.'
    _ <- char '0'
    _ <- whiteSpace
    f' <- integer
    _ <- char '.'
    _ <- char '0'
    let r = toRational f / toRational f'
    return $ VReal r

doubleFloatExpr :: Maybe Sort -> Parser SMTAST
doubleFloatExpr = doubleFloatExprFP

doubleFloatExprFP :: Maybe Sort -> Parser SMTAST
doubleFloatExprFP (Just SortFloat) =
    floatNum <|> try floatPlusZero <|> try floatMinusZero <|> try floatPlusInfinity <|> try floatMinusInfinity <|> floatNaN
doubleFloatExprFP _ =
    doubleNum <|> try doublePlusZero <|> try doubleMinusZero <|> try doublePlusInfinity <|> try doubleMinusInfinity <|> doubleNaN

fpReserved :: (a -> SMTAST) -> String -> a -> Parser SMTAST
fpReserved cons r f = do
    _ <- char '_'
    _ <- whiteSpace
    _ <- reserved r
    _ <- integer
    _ <- integer
    return $ cons f

floatReserved :: String -> Float -> Parser SMTAST
floatReserved = fpReserved VFloat

floatPlusZero :: Parser SMTAST
floatPlusZero = floatReserved "+zero" 0

floatMinusZero :: Parser SMTAST
floatMinusZero = floatReserved "-zero" (- 0)

floatPlusInfinity :: Parser SMTAST
floatPlusInfinity = floatReserved "+oo" (1 / 0)

floatMinusInfinity :: Parser SMTAST
floatMinusInfinity = floatReserved "-oo" (- 1 / 0)

floatNaN :: Parser SMTAST
floatNaN = floatReserved "NaN" (0 / 0)

floatNum :: Parser SMTAST
floatNum = do
    _ <- reserved "fp"
    i <- parseBitVec
    _ <- whiteSpace
    eb <- parseBitVec
    _ <- whiteSpace
    sp <- parseBitVec
    return (VFloat $ mkFloat (i ++ eb ++ sp)) 

mkFloat :: [Int] -> Float
mkFloat = castWord32ToFloat . foldr (\(i, v) w -> if v == 0 then w else setBit w i) 0 . zip [0..] . reverse

doubleReserved :: String -> Double -> Parser SMTAST
doubleReserved = fpReserved VDouble

doublePlusZero :: Parser SMTAST
doublePlusZero = doubleReserved "+zero" 0

doubleMinusZero :: Parser SMTAST
doubleMinusZero = doubleReserved "-zero" (- 0)

doublePlusInfinity :: Parser SMTAST
doublePlusInfinity = doubleReserved "+oo" (1 / 0)

doubleMinusInfinity :: Parser SMTAST
doubleMinusInfinity = doubleReserved "-oo" (- 1 / 0)

doubleNaN :: Parser SMTAST
doubleNaN = doubleReserved "NaN" (0 / 0)

doubleNum :: Parser SMTAST
doubleNum = do
    _ <- reserved "fp"
    i <- parseBitVec
    _ <- whiteSpace
    eb <- parseBitVec
    _ <- whiteSpace
    sp <- parseBitVec
    return (VDouble $ mkDouble (i ++ eb ++ sp)) 

mkDouble :: [Int] -> Double
mkDouble = castWord64ToDouble . foldr (\(i, v) w -> if v == 0 then w else setBit w i) 0 . zip [0..] . reverse

parseBitVec :: Parser [Int]
parseBitVec = try parseBin <|> parseHex
    -- _ <- char '_'
    -- _ <- whiteSpace
    -- _ <- char 'b'
    -- _ <- char 'v'
    -- i <- fromIntegral <$> integer
    -- _ <- whiteSpace
    -- _ <- integer
    -- return i

parseBin :: Parser [Int]
parseBin = do
    _ <- char '#'
    _ <- char 'b'
    bv <- many (char '0' <|> char '1')
    return $ map (\c -> if c == '0' then 0 else 1) bv

parseHex :: Parser [Int]
parseHex = do
    _ <- char '#'
    _ <- char 'x'
    bv <- many (choice . map char $ ['0'..'9'] ++ ['a'..'f'])
    return . map (\c -> if c == '0' then 0 else 1) $ concatMap bin bv

doubleFloatExprDec :: Parser SMTAST
doubleFloatExprDec = do
    r <- doubleFloat
    _ <- optionMaybe (reserved "?")
    return (VFloat r)

doubleFloat :: Parser Float
doubleFloat = do
    s <- optionMaybe (reserved "-")
    f <- floatT
    let r = double2Float f
    case s of 
        Just _ -> return (-r)
        Nothing -> return r

flexDoubleFloat :: Parser Double
flexDoubleFloat = do
    s <- optionMaybe (reserved "-")
    f <- flexFloatT
    case s of 
        Just _ -> return (-f)
        Nothing -> return f

stringExpr :: Parser SMTAST
stringExpr = do
    _ <- char '"'
    str <- many stringExpr'
    _ <- char '"'
    return (VString str)

stringExpr' :: Parser Char
stringExpr' = do
    try parseHexChar <|> try parseUni <|> choice (alphaNum:char '\\':char ' ':map char ident)

parseHexChar :: Parser Char
parseHexChar = do
    _ <- char '\\'
    _ <- char 'x'
    str <- many (choice . map char $ ['0'..'9'] ++ ['a'..'f'])
    case readHex str of
        [(c, _)] -> return $ chr c
        _ -> error $ "stringExpr': Bad string"

parseUni :: Parser Char
parseUni = do
    _ <- char '\\'
    _ <- char 'u'
    _ <- char '{'
    str <- many (choice . map char $ ['0'..'9'] ++ ['a'..'f'])
    _ <- char '}'
    case readHex str of
        [(c, _)] -> return $ chr c
        _ -> error $ "stringExpr': Bad string"

parseSMT :: Sort -> String -> SMTAST
parseSMT srt s = case parse (smtParser (Just srt)) s s of
    Left e -> error $ "get model parser error on " ++ show e
    Right r -> r

-- | parseGetValues
-- Parse the result of a get-values call
parseGetValues :: Sort -> String -> SMTAST
parseGetValues srt s =
    case parse (getValuesParser (Just srt)) s s of
        Left e -> error $ "get values parser error on " ++ show e
        Right r -> r

bin:: Char -> String
bin '0' = "0000"
bin '1' = "0001"
bin '2' = "0010"
bin '3' = "0011"
bin '4' = "0100"
bin '5' = "0101"
bin '6' = "0110"
bin '7' = "0111"
bin '8' = "1000"
bin '9' = "1001"
bin 'a' = "1010"
bin 'b' = "1011"
bin 'c' = "1100"
bin 'd' = "1101"
bin 'e' = "1110"
bin 'f' = "1111"
bin _ = error "bin: Unsupported Char"