{-# LANGUAGE CPP #-}

module G2.Translation.Cabal.Cabal (cabalSrcDirs, fullDirs) where

import Distribution.PackageDescription

import qualified Distribution.ModuleName as MN
import G2.Translation.Haskell
import System.FilePath

#if MIN_VERSION_Cabal(2,2,0)
import Distribution.PackageDescription.Parsec
#else
import Distribution.PackageDescription.Parse
#endif

import Distribution.Verbosity

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
buildInfoSrcDirs (BuildInfo { hsSourceDirs = sd }) = sd

fullDirs :: FilePath -> IO [FilePath]
fullDirs proj = do
    cabal <- findCabal proj
    let cab = case cabal of
                Just c -> proj </> c
                Nothing -> error "No Cabal"
    gpd <- readGenericPackageDescription silent cab
    let cn = case condLibrary gpd of
                Just c -> c
                Nothing -> error "No Library"
        libs = foldr (\l acc -> l:acc) [] cn
        modules = concat $ map exposedModules libs
        sources = concat $ map (hsSourceDirs . libBuildInfo) libs
        others = concat $ map (otherModules . libBuildInfo) libs
        paths = sources ++ (map MN.toFilePath $
                (exposedModules $ condTreeData cn) ++ modules ++ others ++
                (otherModules $ libBuildInfo $ condTreeData cn))
    return $ map (proj </>) paths
