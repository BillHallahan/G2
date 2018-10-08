module G2.Internals.Language.Monad.Naming ( doRenameN
                                          , doRenamesN
                                          , renameAllN
                                          , freshSeededStringN
                                          , freshSeededStringsN
                                          , freshSeededNameN
                                          , freshSeededNamesN
                                          , freshNameN
                                          , freshNamesN
                                          , freshIdN
                                          , freshSeededIdN
                                          , freshIdsN ) where

import G2.Internals.Language

import G2.Internals.Language.Monad.Support

import qualified Data.Text as T

doRenameN :: (ExState s m, Named a) => Name -> a -> m a
doRenameN n a = withNG $ \ng -> doRename n ng a

doRenamesN :: (ExState s m, Named a) => [Name] -> a -> m a
doRenamesN ns a = withNG $ \ng -> doRenames ns ng a

renameAllN :: (ExState s m, Named a) => a -> m a
renameAllN a = withNG (renameAll a)

freshSeededStringN :: ExState s m => T.Text -> m Name
freshSeededStringN t = withNG (freshSeededString t)

freshSeededStringsN :: ExState s m => [T.Text] -> m [Name]
freshSeededStringsN t = withNG (freshSeededStrings t)

freshSeededNameN :: ExState s m => Name -> m Name
freshSeededNameN n = withNG (freshSeededName n)

freshSeededNamesN :: ExState s m => [Name] -> m [Name]
freshSeededNamesN ns = withNG (freshSeededNames ns)

freshNameN :: ExState s m => m Name
freshNameN = withNG (freshName)

freshNamesN :: ExState s m => Int -> m [Name]
freshNamesN i = withNG (freshNames i)

freshIdN :: ExState s m => Type -> m Id
freshIdN t = withNG (freshId t)

freshSeededIdN :: (Named n, ExState s m) => n -> Type -> m Id
freshSeededIdN n t = withNG (freshSeededId n t)

freshIdsN :: ExState s m => [Type] -> m [Id]
freshIdsN ts = withNG (freshIds ts)
