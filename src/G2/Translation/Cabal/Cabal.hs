{-# LANGUAGE CPP #-}

module G2.Translation.Cabal.Cabal (cabalSrcDirs) where

import Distribution.PackageDescription

#if MIN_VERSION_Cabal(2,2,0)
import Distribution.PackageDescription.Parsec
#else
import Distribution.PackageDescription.Parse
#endif

import Distribution.Verbosity
import Distribution.Utils.Path

-- | Takes the filepath to a Cabal file, and returns a list of FilePaths to red
-- from.
cabalSrcDirs :: FilePath -> IO [FilePath]
cabalSrcDirs fp = do
    gpd <- readGenericPackageDescription silent fp
    return $ genericPackageDescriptionSrcDirs gpd

genericPackageDescriptionSrcDirs :: GenericPackageDescription -> [FilePath]
genericPackageDescriptionSrcDirs (GenericPackageDescription
                                            { condLibrary = cl
                                            , condExecutables = ce }) = do
    maybe [] (condTreeSrcDirs libSrcDirs) cl ++ concatMap (condTreeSrcDirs execSrcDirs . snd) ce

condTreeSrcDirs :: (a -> [FilePath]) -> CondTree v c a -> [FilePath]
condTreeSrcDirs f (CondNode { condTreeData = t }) = f t

libSrcDirs :: Library -> [FilePath]
libSrcDirs = buildInfoSrcDirs . libBuildInfo

execSrcDirs :: Executable -> [FilePath]
execSrcDirs = buildInfoSrcDirs . buildInfo

buildInfoSrcDirs :: BuildInfo -> [FilePath]
#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
buildInfoSrcDirs (BuildInfo { hsSourceDirs = sd }) = map getSymbolicPath sd
#else
buildInfoSrcDirs (BuildInfo { hsSourceDirs = sd }) = sd
#endif