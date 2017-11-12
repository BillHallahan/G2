module G2.Internals.Translation.Cabal.Parser 
  ( pkgLibDeps
  , pkgIdent
  , parseCabal
  ) where

import Distribution.Package
import Distribution.PackageDescription
import Distribution.PackageDescription.Parse
import Distribution.Verbosity

buildInfoDeps :: BuildInfo -> [Dependency]
buildInfoDeps build_info = tool_deps ++ conf_deps ++ tgt_deps
  where
    tool_deps = buildTools build_info
    conf_deps = pkgconfigDepends build_info
    tgt_deps = targetBuildDepends build_info

libDeps :: Library -> [Dependency]
libDeps = buildInfoDeps . libBuildInfo

condTreeLibDeps :: CondTree ConfVar [Dependency] Library -> [Dependency]
condTreeLibDeps cond_tree = node_deps ++ const_deps ++ child_deps
  where
    node_deps = libDeps $ condTreeData cond_tree
    const_deps = condTreeConstraints cond_tree
    child_deps = concatMap (\(_, child, m_child) ->
                                condTreeLibDeps child ++
                                maybe [] condTreeLibDeps m_child) $
                           condTreeComponents cond_tree

pkgLibDeps :: GenericPackageDescription -> [Dependency]
pkgLibDeps gen_pkg = desc_deps ++ lib_deps
  where
    lib_deps = maybe [] condTreeLibDeps $ condLibrary gen_pkg
    desc_deps = maybe [] libDeps $ library $ packageDescription gen_pkg

pkgIdent :: GenericPackageDescription -> PackageIdentifier
pkgIdent = package . packageDescription

parseCabal :: FilePath -> IO (PackageIdentifier, [Dependency])
parseCabal cabal_file = do
  gen_desc <- readPackageDescription normal cabal_file
  return (pkgIdent gen_desc, pkgLibDeps gen_desc)


