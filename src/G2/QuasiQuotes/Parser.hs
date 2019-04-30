module G2.QuasiQuotes.Parser
  ( QuotedExtract (..)
  , extractQuotedData
  , transformQuoted
  , quotedEx2Hsk
  , getConcVars
  ) where


import Data.Array
import Data.Char
import Data.List
import Text.Regex
import Text.Regex.Base

testStr1 :: String
testStr1 = "!(y :: Int) !(z :: Int) -> ?(a :: Int) ?(b :: Int) | a + b + 2 == y + z "

testStr2 :: String
testStr2 = "!(y :: Int) -> ?(b :: Int) | (y == 2) || (b == 4)"

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace

--------------------
-- Regular expressions

-- RS stands for Regex String
idRs :: String
idRs = "[A-Za-z][0-9A-Za-z_]*"

whiteSpaceRs :: String
whiteSpaceRs = "[ \t\r\n\v\f]"

paddedIdRs :: String
paddedIdRs = whiteSpaceRs ++ "*" ++ idRs ++ whiteSpaceRs ++ "*"

bar :: String
bar = "|"

concVarRegex :: Regex
concVarRegex = mkRegex $ "[(]" ++ paddedIdRs ++ "::[^!?|]*"

symbVarRegex :: Regex
symbVarRegex = mkRegex $ "[?][(]" ++ paddedIdRs ++ "::[^!?|]*"

lamDividerRegex :: Regex
lamDividerRegex = mkRegex $ "->" ++ whiteSpaceRs ++ "[?]"

dividerRegex :: Regex
dividerRegex = mkRegex $ "[" ++ bar ++ "]"

-- Output from matchAlltext
matchAllText2 :: RegexLike regex source => regex -> source -> [source]
matchAllText2 regex = map (fst . snd) . concatMap assocs . matchAllText regex

idPairFrom2Colon :: String -> (String, String)
idPairFrom2Colon twoColonSepd =
  case splitRegex (mkRegex "::") twoColonSepd of
    (s1 : s2 : []) ->
      case (splitRegex (mkRegex "[(]") s1, reverse $ trim s2) of
        (_ : varName : [], ')' : revVarType)
          -> (trim varName, "(" ++ reverse revVarType ++ ")")
        _ -> error $ "idPairFromColon: incorrect decomp: " ++ show (s1, s2)
    _ -> error $ "idPairFrom2Colon: incorrect string " ++ show twoColonSepd

  {-
  case matchAllText2 (mkRegex idRs) twoColonSepd of
    (s1 : s2 : []) -> (trim s1, trim s2)
    _ -> error $ "idPairFrom2Colon: incorrect string " ++ show twoColonSepd
  -}

-- These three functions need to be fed processed strings
-- getConcVars :: String -> [(String, String)]
-- getConcVars chewed = map idPairFrom2Colon $ matchAllText2 concVarRegex chewed

getConcVars :: String -> [(String, String)]
getConcVars = getConcVars' 0 ""

getConcVars' :: Int -> String -> String -> [(String, String)]
getConcVars' n pr ('(':xs)
    | n == 0 = getConcVars' (n + 1) pr xs
    | otherwise = getConcVars' (n + 1) ('(':pr) xs
getConcVars' n pr (')':xs)
    | n == 1
    , [v, t] <- splitRegex (mkRegex "::") (reverse pr) = (filter (not . isSpace) v, "(" ++ t ++ ")"):getConcVars' (n - 1) "" xs
    | otherwise = getConcVars' (n - 1) (')':pr) xs
getConcVars' n pr (x:xs)
  | n > 0 = getConcVars' n (x:pr) xs
  | otherwise = getConcVars' n (x:pr) xs
getConcVars' _ pr []
    | [v, t] <- splitRegex (mkRegex "::") (reverse pr) = [(filter (not . isSpace) v, "(" ++ t ++ ")")]
    | otherwise = []

getSymbVars :: String -> [(String, String)]
getSymbVars chewed = map idPairFrom2Colon $ matchAllText2 symbVarRegex chewed

getFuncBody :: String -> String
getFuncBody chewed = concat $ tail $ splitRegex dividerRegex chewed


-----------------------
-- Parsing extracted stuff

data QuotedExtract = QuotedExtract
  { concVars :: [(String, String)] -- (varName, VarType)
  , symbVars :: [(String, String)] -- (varName, varType)
  , bodyExpr :: String
  } deriving (Show, Eq)

-- Extract the conc var-ty pairs, symb var-ty pairs, and fun body
extractQuotedData :: String -> QuotedExtract
extractQuotedData raw
  | (h:raw') <- dropWhile isSpace raw
  , h == '\\' = 
  -- First split based on the divider bar "|"
  -- into variable declarations and body
  case splitRegex dividerRegex raw' of
    (hd : tl) ->
      -- Further partiton with "-> ?" into concrete and symbolics
      -- Remember that splitting will consume the initial ?
      case splitRegex lamDividerRegex hd of
        (concs : symbs) ->
          QuotedExtract
            { concVars = getConcVars concs
            , symbVars = getSymbVars $ '?' : concat symbs
            , bodyExpr = trim $ intercalate bar tl
            }
    _ -> error $ "extractQuotedData: bad text " ++ show raw
  | otherwise = error $ "extractQuotedData: bad text " ++ show raw

quotedEx2Hsk :: QuotedExtract -> String
quotedEx2Hsk quoted =
  let (concVs, concTs) = unzip $ concVars quoted
      (symbVs, symbTs) = unzip $ symbVars quoted
      bodyStr = bodyExpr quoted
      typeStr = intercalate " -> " (concTs ++ symbTs ++ ["Bool"])
      concParamStr = intercalate " " concVs
      symbParamStr = intercalate " " symbVs
  in
    "(\\ " ++ concParamStr ++ " -> " 
      ++ "\\ " ++ symbParamStr ++ " -> "
        ++ bodyStr ++ ") :: " ++ typeStr

-------------------
-- The one-pass function
transformQuoted :: String -> String
transformQuoted = quotedEx2Hsk . extractQuotedData


