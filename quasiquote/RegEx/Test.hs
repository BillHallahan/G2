{-# LANGUAGE QuasiQuotes #-}

module RegEx.Test where

import RegEx.RegEx
import G2.QuasiQuotes.QuasiQuotes

regexTest1 :: IO (Maybe String)
regexTest1 = stringSearch (Concat (Atom 'a') (Atom 'b'))

regexTest2 :: IO (Maybe String)
regexTest2 = stringSearch r
  where
    r = Concat
          (Star (Or (Atom 'a') (Atom 'b')))
          (Concat (Atom 'c')
            (Or (Atom 'd')
                (Concat (Atom 'e')
                        (Atom 'f'))))
                

stringSearch :: RegEx -> IO (Maybe String)
stringSearch = [g2| \(r :: RegEx) -> ?(str :: String) |
              match r str |]

