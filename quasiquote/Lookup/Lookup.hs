module Lookup.Lookup where

import Prelude hiding (lookup)

kvLookup :: Int -> [(Int , a)] -> Maybe a
kvLookup key kvs =
  case kvs of
    [] -> Nothing
    (k , v ) : rest ->
      case key == k of
        True -> Just v
        False -> kvLookup key rest

