{-# LANGUAGE QuasiQuotes #-}

module Regex.Test where

import Regex.Regex
import G2.QuasiQuotes.QuasiQuotes

regexTest1 :: IO (Maybe String)
regexTest1 = stringSearch (Concat (Atom 'a') (Atom 'b'))

regexTest2 :: IO (Maybe String)
regexTest2 = stringSearch r
  where
    r = Concat
          (Star (Plus (Atom 'a') (Atom 'b')))
          (Concat (Atom 'c')
            (Plus (Atom 'd')
                (Concat (Atom 'e')
                              (Atom 'f'))))
                

stringSearch :: Regex -> IO (Maybe String)
stringSearch = [g2| \(r :: Regex) -> ?(str :: String) |
              match r str |]

