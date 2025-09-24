module Main where

import Data.List.Extra ( groupOn, word1 ) 
import System.Process.Extra ( systemOutput_, system_ )
import System.Directory (createDirectoryIfMissing)


main :: IO ()
main = do
  let toUrl (name, ver) = "http://hackage.haskell.org/package/" ++ name ++ "/" ++ name ++ "-" ++ ver ++ ".tar.gz"
  urls <- map (toUrl . last) . groupOn fst . map word1 . lines <$> systemOutput_ "cabal list --simple"
  writeFile "_urls.txt" $ unlines urls
  -- Create the folder if it doesn't exist
  createDirectoryIfMissing True "all_hackage"

  -- Tell wget to dump files into "all_hackage/"
  system_ "wget -P all_hackage --input-file=_urls.txt"