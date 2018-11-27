module G2.Translation.Cabal.Interface
  ( unpackTarSameDir
  , unpackTar
  , module G2.Translation.Cabal.Downloader
  , module G2.Translation.Cabal.Parser
  ) where

import qualified System.Process as P
import qualified Distribution.Package as D
import qualified Distribution.PackageDescription as D
import qualified Data.Map as M
import qualified System.FilePath as F

import G2.Translation.Cabal.Downloader
import G2.Translation.Cabal.Parser

unpackTar :: FilePath -> FilePath -> IO ()
unpackTar tar_file destination = P.callProcess "tar" flags >> return ()
  where
    flags = [ "-zxf"
            , tar_file
            , "-C"
            , F.dropFileName destination ]

unpackTarSameDir :: FilePath -> IO ()
unpackTarSameDir tar_file = unpackTar tar_file $ F.dropFileName tar_file

newtype DependencyGraph = DependencyGraph
  { un_graph :: M.Map D.PackageIdentifier [D.Dependency]
  } deriving (Show, Eq, Read)

insertNode :: D.PackageIdentifier -> [D.Dependency] -> DependencyGraph
           -> DependencyGraph
insertNode key values graph = graph { un_graph = un_graph' }
  where
    un_graph' = M.insert key values $ un_graph graph

isVersionOk :: D.PackageIdentifier -> D.Dependency -> Bool
isVersionOk package_id dependency = undefined
  where
    ranges = undefined


run :: FilePath -> IO ()
run target = undefined
