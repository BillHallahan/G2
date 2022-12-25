{-# LANGUAGE QuasiQuotes #-}

module NQueens.Test (queensTestN, allQueensSafe) where

import NQueens.Encoding
import G2.QuasiQuotes.QuasiQuotes

{-
queensTestN :: Int -> IO (Maybe [Queen])
queensTestN n = [g2| \(n :: Int) -> ?(queens :: [Queen]) |
                  legalQueens n queens
                    && allSafe queens |] n
-}

queensTestN :: Int -> IO (Maybe [Queen])
queensTestN num = [g2| \(n :: Int) -> ?(qs :: [Queen]) |
                allQueensSafe n qs |] num


