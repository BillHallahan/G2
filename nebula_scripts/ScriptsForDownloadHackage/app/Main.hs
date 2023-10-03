module Main where

import Data.List.Extra ( groupOn, word1 ) 
import System.Process.Extra ( systemOutput_, system_ )

main :: IO ()
main = do
  let toUrl (name, ver) = "http://hackage.haskell.org/package/" ++ name ++ "/" ++ name ++ "-" ++ ver ++ ".tar.gz"
  urls <- map (toUrl . last) . groupOn fst . map word1 . lines <$> systemOutput_ "cabal list --simple"
  writeFile "_urls.txt" $ unlines urls
  system_ "wget --input-file=_urls.txt"