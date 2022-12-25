{-# LANGUAGE QuasiQuotes #-}

module RegEx.Test where

import RegEx.RegEx
import G2.QuasiQuotes.QuasiQuotes

stringSearch :: RegEx -> IO (Maybe String)
stringSearch = [g2| \(r :: RegEx) -> ?(str :: String) |
              match r str |]


-- (a + b)* c (d + (e f)*)
regex1 :: RegEx
regex1 =
  Concat (Star (Or (Atom 'a') (Atom 'b')))
         (Concat (Atom 'c')
                 (Or (Atom 'd')
                     (Concat (Atom 'e')
                             (Atom 'f'))))

regex2 :: RegEx
regex2 = Concat (Atom 'a')
         (Concat (Atom 'b')
         (Concat (Atom 'c')
         (Concat (Atom 'd')
         (Concat (Atom 'e')
         ((Atom 'f'))))))

regex3 :: RegEx
regex3 = Or (Atom 'a')
         (Or (Atom 'b')
         (Or (Atom 'c')
         (Or (Atom 'd')
         (Or (Atom 'e')
         ((Atom 'f'))))))

regex4 :: RegEx
regex4 = Concat (Star (Atom 'a'))
          (Concat (Star (Atom 'b'))
          (Concat (Star (Atom 'c'))
          (Concat (Star (Atom 'd'))
          (Concat (Star (Atom 'e'))
          ((Star (Atom 'f')))))))
