{-# LANGUAGE QuasiQuotes #-}

module Lookup.Test where

import G2.QuasiQuotes.QuasiQuotes
import Lookup.Lookup

lookupTest1 :: IO (Maybe [(Int, String)])
lookupTest1 =
  findAssocList
    [(23, "hello"), (59, "goodbye")]
    4

lookupTest2 :: IO (Maybe [(Int, String)])
lookupTest2 =
  [g2| \(pairs :: [(Int, Maybe String)]) -> ?(kvs :: [(Int, String)]) |
        all id $ map (\(k, v) -> kvLookup k kvs == v) pairs |]
          [(23, Just "hello"), (23, Nothing), (59, Just "goodbye")]


findAssocList :: [(Int, String)] -> Int -> IO (Maybe [(Int, String)])
findAssocList =
  [g2| \(mustExist :: [(Int, String)])
        (minLen :: Int)
          -> ?(kvs :: [(Int, String)]) |
      (all id $ map (\(k, v) ->
                      kvLookup k kvs == Just v)
                    mustExist)
        && length kvs >= minLen |]

