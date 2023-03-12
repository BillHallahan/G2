{-# LANGUAGE CPP #-}

module G2.Translation.Cabal.Cabal (cabalSrcDirs) where

import Distribution.PackageDescription

#if MIN_VERSION_Cabal(2,2,0)
import Distribution.PackageDescription.Parsec
#else
import Distribution.PackageDescription.Parse
#endif

import Distribution.Verbosity
#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
import Distribution.Utils.Path
#endif

-- | Takes the filepath to a Cabal file, and returns a list of FilePaths to red
-- from.
cabalSrcDirs :: FilePath -> IO [FilePath]
cabalSrcDirs fp = do
    gpd <- readGenericPackageDescription silent fp
    return $ genericPackageDescriptionSrcDirs gpd

genericPackageDescriptionSrcDirs :: GenericPackageDescription -> [FilePath]
genericPackageDescriptionSrcDirs (GenericPackageDescription
                                            { condLibrary = cl
                                            , condExecutables = ce
                                            , condTestSuites = ts }) = do
       maybe [] (condTreeSrcDirs libSrcDirs) cl
    ++ concatMap (condTreeSrcDirs execSrcDirs . snd) ce
    ++ concatMap (condTreeSrcDirs testSrcDirs . snd) ts

condTreeSrcDirs :: (a -> [FilePath]) -> CondTree v c a -> [FilePath]
condTreeSrcDirs f (CondNode { condTreeData = t }) = f t

libSrcDirs :: Library -> [FilePath]
libSrcDirs = buildInfoSrcDirs . libBuildInfo

execSrcDirs :: Executable -> [FilePath]
execSrcDirs = buildInfoSrcDirs . buildInfo

testSrcDirs :: TestSuite -> [FilePath]
testSrcDirs = buildInfoSrcDirs . testBuildInfo

buildInfoSrcDirs :: BuildInfo -> [FilePath]
#if MIN_VERSION_GLASGOW_HASKELL(9,2,2,0)
buildInfoSrcDirs (BuildInfo { hsSourceDirs = sd }) = map getSymbolicPath sd
#else
buildInfoSrcDirs (BuildInfo { hsSourceDirs = sd }) = sd
#endif