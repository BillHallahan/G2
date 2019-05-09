{-# LANGUAGE QuasiQuotes #-}

module NQueens.Call where

import NQueens.Encoding
import G2.QuasiQuotes.QuasiQuotes

queensTestN :: Int -> IO (Maybe [Queen])
queensTestN n = [g2| \(n :: Int) -> ?(queens :: [Queen]) |
                  legalQueens n queens
                    && allSafe queens |] n
