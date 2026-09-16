module KMP where

import Data.Array
  ( Array
  , listArray
  , bounds
  , (!)
  )

import G2.Plugin

-- |The solid data type of KMP table
data Table a = Table
  { alphabetTable :: Array Int a
  , jumpTable :: Array Int Int
  , len :: Int
  }

type MatchState = Int

-- |The 'build' function eats a pattern (list of some Eq) and generates a KMP table.
--
-- The time and space complexities are both O(length of the pattern)
build :: Eq a => [a] -> Table a
build pattern =
  let
    len = length pattern

    resTable = Table
      { alphabetTable = listArray (0,len-1) pattern
      , jumpTable = listArray (-1,len-1) $ (-2) : genJump (-1) 0
      , len = len
      }

    genJump _ 0 =
      let
        o = if 1 == len || alphabetTable resTable ! 0 /= alphabetTable resTable ! 1
          then -1
          else -2

        later = genJump (-1) 1
      in
        o : later

    genJump lastMPJump i =
      let
        ch = alphabetTable resTable ! i

        findJ j
          | j == -2 = -2
          | alphabetTable resTable ! (j+1) == ch = j
          | j == -1 = -2
          | otherwise = findJ (jumpTable resTable ! j)

        j = findJ lastMPJump

        o = if i+1 == len || alphabetTable resTable ! (i+1) /= alphabetTable resTable ! (j+2)
          then j+1
          else jumpTable resTable ! (j+1)

        later = genJump (j+1) (i+1)
      in o : later

  in
    resTable

-- |The 'matchSingle' function takes the KMP table, the current state of the matching and the next
-- element in the sequence and returns whether it finished a matching sequence along with the new
-- state. This is useful if your input doesn't come in a list or you need other flexibilities.
--
-- The matching state is just an integer representing how long of a pattern prefix has been
-- matched already. Therefore the initial state should be 0 if you start with an empty sequence.
matchSingle :: Eq a => Table a -> MatchState -> a -> (Bool, MatchState)
matchSingle table j s
  | j < 0 || j < len table && s == alphabetTable table ! j = (j + 1 == len table, j + 1)
  | otherwise = matchSingle table (1 + (jumpTable table ! (j - 1))) s


-- |The 'match' function takes the KMP table and a list to be searched (might be infinite)
-- and then generates the search results as a list of every matched begining (might be infinite).
--
-- The time complexity is O(length of the pattern + length of the searched list)
match :: Eq a => Table a -> [a] -> [Int]
match table str = [ 0 | len table == 0 ] ++ go (1 - len table) 0 str
  where
    go i j [] = []
    go i j (s:ss) = case matchSingle table j s of
      (False, j') -> go (i + 1) j' ss
      (True, j')  -> i : go (i + 1) j' ss

{-# ANN containsKmp (SMTEquivIs "containsSmt") #-}
containsKmp :: String -> String -> Bool
containsKmp needle haystack =
    let table = build needle
        indices = match table haystack
    in not $ null indices

containsSmt :: String -> String -> Bool
containsSmt = smtContains
