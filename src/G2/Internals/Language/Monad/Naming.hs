module G2.Internals.Language.Monad.Naming ( doRenameN
                                          , doRenamesN
                                          , renameAllN
                                          , freshSeededStringN
                                          , freshSeededStringsN
                                          , freshSeededNameN
                                          , freshSeededNamesN
                                          , freshNameN
                                          , freshNamesN ) where

import G2.Internals.Language

import G2.Internals.Language.Monad.Support

import qualified Data.Text as T

doRenameN :: Named a => Name -> a -> StateM t a
doRenameN n a = withNG $ \ng -> doRename n ng a

doRenamesN :: Named a => [Name] -> a -> StateM t a
doRenamesN ns a = withNG $ \ng -> doRenames ns ng a

renameAllN :: Named a => a -> StateM t a
renameAllN a = withNG (renameAll a)

freshSeededStringN :: T.Text -> StateM t Name
freshSeededStringN t = withNG (freshSeededString t)

freshSeededStringsN :: [T.Text] -> StateM t [Name]
freshSeededStringsN t = withNG (freshSeededStrings t)

freshSeededNameN :: Name -> StateM t Name
freshSeededNameN n = withNG (freshSeededName n)

freshSeededNamesN :: [Name] -> StateM t [Name]
freshSeededNamesN ns = withNG (freshSeededNames ns)

freshNameN :: StateM t Name
freshNameN = withNG (freshName)

freshNamesN :: Int -> StateM t [Name]
freshNamesN i = withNG (freshNames i)

freshIdN :: Type -> StateM t Id
freshIdN t = withNG (freshId t)

freshIdsN :: [Type] -> StateM t [Id]
freshIdsN ts = withNG (freshIds ts)