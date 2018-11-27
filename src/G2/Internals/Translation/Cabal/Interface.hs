module G2.Internals.Translation.Cabal.Interface where

import Distribution.Compiler
import Distribution.PackageDescription
import Distribution.PackageDescription.Configuration
import Distribution.PackageDescription.Parse
import Distribution.Simple.Configure
import Distribution.Simple.InstallDirs
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Program.Db
import Distribution.Simple.Setup
import Distribution.Simple.SrcDist
import Distribution.Verbosity

getLocalBuildInfo :: FilePath -> IO LocalBuildInfo
getLocalBuildInfo target = do
    gpd <- readPackageDescription silent target

    print gpd

    let hbi = emptyHookedBuildInfo
        pkgdb = defaultProgramDb
        cf = defaultConfigFlags pkgdb

    print cf

    configure (gpd, hbi) cf

getPackageDescription :: FilePath -> IO PackageDescription
getPackageDescription target = do
    gpd <- readPackageDescription silent target

    return $ flattenPackageDescription gpd

runCabal :: FilePath -> IO ()
runCabal target = do
    insdir <- defaultInstallDirs GHC False False
    let insdir' = substituteInstallDirTemplates [] insdir
    print $ fromPathTemplate (libsubdir insdir')
    print $ fromPathTemplate (includedir insdir')
    --lbi <- getLocalBuildInfo target
    pd <- getPackageDescription target
    mapM_ (print . targetBuildDepends) $ allBuildInfo pd
    -- print $ allBuildInfo pd
    return ()
