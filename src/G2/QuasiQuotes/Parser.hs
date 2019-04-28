module G2.QuasiQuotes.Parser
  ( QuotedExtract (..)
  , extractQuotedData
  , transformQuoted
  , quotedEx2Hsk
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

paddedIdRs :: String
paddedIdRs = "[ \t]*" ++ idRs ++ "[ \t]*"

barRs :: String
barRs = "|"

concVarRegex :: Regex
concVarRegex = mkRegex $ "![(]" ++ paddedIdRs ++ "::[^!?|-]*"

symbVarRegex :: Regex
symbVarRegex = mkRegex $ "[?][(]" ++ paddedIdRs ++ "::[^!?|-]*"

dividerRegex :: Regex
dividerRegex = mkRegex $ "[" ++ barRs ++ "]"

-- Output from matchAlltext
matchAllText2 :: RegexLike regex source => regex -> source -> [source]
matchAllText2 regex = map (fst . snd) . concatMap assocs . matchAllText regex

idPairFrom2Colon :: String -> (String, String)
idPairFrom2Colon twoColonSepd =
  case splitRegex (mkRegex "::") twoColonSepd of
    (s1 : s2 : []) ->
      case (splitRegex (mkRegex "[(]") s1, reverse $ trim s2) of
        (_ : varName : [], ')' : revVarType)
          -> (trim varName, reverse revVarType)
        _ -> error $ "idPairFromColon: incorrect decomp: " ++ show (s1, s2)
    _ -> error $ "idPairFrom2Colon: incorrect string " ++ show twoColonSepd

  {-
  case matchAllText2 (mkRegex idRs) twoColonSepd of
    (s1 : s2 : []) -> (trim s1, trim s2)
    _ -> error $ "idPairFrom2Colon: incorrect string " ++ show twoColonSepd
  -}

getConcVars :: String -> [(String, String)]
getConcVars raw = map idPairFrom2Colon $ matchAllText2 concVarRegex raw

getSymbVars :: String -> [(String, String)]
getSymbVars raw = map idPairFrom2Colon $ matchAllText2 symbVarRegex raw

getFuncBody :: String -> String
getFuncBody raw = concat $ tail $ splitRegex dividerRegex raw


-----------------------
-- Parsing extracted stuff

data QuotedExtract = QuotedExtract
  { concVars :: [(String, String)] -- (varName, VarType)
  , symbVars :: [(String, String)] -- (varName, varType)
  , bodyExpr :: String
  } deriving (Show, Eq)

-- Extract the conc var-ty pairs, symb var-ty pairs, and fun body
extractQuotedData :: String -> QuotedExtract
extractQuotedData raw =
  -- Split the dividers up
  let splitted = splitRegex dividerRegex raw in
  case splitted of
    (hd : tl) ->
      QuotedExtract
        { concVars = getConcVars hd
        , symbVars = getSymbVars hd
        , bodyExpr = trim $ intercalate barRs tl
        }
    _ -> error $ "extractQuotedData: bad text " ++ show raw

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


