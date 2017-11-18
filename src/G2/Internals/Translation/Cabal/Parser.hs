module G2.Internals.Translation.Cabal.Parser 
  ( LibraryCondTree
  , packageLibraryDeps
  , pkgIdent
  , parseCabal
  ) where

import qualified Distribution.Package as D
import qualified Distribution.PackageDescription as D
import qualified Distribution.PackageDescription.Parse as D
import qualified Distribution.Verbosity as D

-- | Extract `Dependency` from `BuildInfo`.
buildInfoDeps :: D.BuildInfo -> [D.Dependency]
buildInfoDeps build_info = tool_deps ++ config_deps ++ target_deps
  where
    tool_deps = D.buildTools build_info
    config_deps = D.pkgconfigDepends build_info
    target_deps = D.targetBuildDepends build_info

-- | Extract `Dependency` from `Library`.
libraryDeps :: D.Library -> [D.Dependency]
libraryDeps = buildInfoDeps . D.libBuildInfo

-- | A `CondTree` parametrized with `Library`.
type LibraryCondTree = D.CondTree D.ConfVar [D.Dependency] D.Library

-- | Extract `Dependency` from a `CondTree` parametrized with `Library`.
condTreeLibDeps :: LibraryCondTree -> [D.Dependency]
condTreeLibDeps cond_tree = node_deps ++ constraint_deps ++ child_deps
  where
    node_deps = libraryDeps $ D.condTreeData cond_tree
    constraint_deps = D.condTreeConstraints cond_tree
    child_deps = concatMap (\(_, child, m_child) ->
                                condTreeLibDeps child ++
                                maybe [] condTreeLibDeps m_child) $
                           D.condTreeComponents cond_tree

-- | Extract `Dependency` from `GenericPackageDescription`.
packageLibraryDeps :: D.GenericPackageDescription -> [D.Dependency]
packageLibraryDeps generic_package = description_deps ++ library_deps
  where
    library_deps = maybe [] condTreeLibDeps $ D.condLibrary generic_package
    description_deps = maybe [] libraryDeps
                        $ D.library
                        $ D.packageDescription generic_package

-- | Extract `PackageIdentifier` from `GenericPackageDescription`.
pkgIdent :: D.GenericPackageDescription -> D.PackageIdentifier
pkgIdent = D.package . D.packageDescription

-- | Parse a .cabal file to get the `PackageIdentifier` and `Dependency`.
parseCabal :: FilePath -> IO (D.PackageIdentifier, [D.Dependency])
parseCabal cabal_file = do
  gen_description <- D.readPackageDescription D.normal cabal_file
  return (pkgIdent gen_description, packageLibraryDeps gen_description)

