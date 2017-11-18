module G2.Internals.Translation.Cabal.Downloader
  ( downloadFile
  , downloadPackage
  , downloadBase
  , mkUrl
  ) where

import qualified Network.HTTP as H
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.List as L

hackage_url :: FilePath
hackage_url = "http://hackage.haskell.org/package"

base_4_10_url :: FilePath
base_4_10_url = "http://hackage.haskell.org/package/base/base-4.10.0.0.tar.gz"

mkUrl :: String -> [Int] -> FilePath
mkUrl name versions = L.intercalate "/" parts
  where
    canonical = name ++ L.intercalate "-" (map show versions)
    parts = [hackage_url, canonical, canonical ++ ".tar.gz"]

downloadFile :: FilePath -> FilePath -> IO ()
downloadFile url destination = do
  let request = H.getRequest url
  response_body <- H.getResponseBody =<< H.simpleHTTP request
  B.writeFile destination $ B.pack response_body

downloadPackage :: String -> [Int] -> FilePath -> IO ()
downloadPackage name versions = downloadFile (mkUrl name versions)

downloadBase :: FilePath -> IO ()
downloadBase = downloadFile base_4_10_url

