module G2.Language.Monad.Naming ( doRenameN
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

import G2.Language

import G2.Language.Monad.Support

import qualified Data.Text as T

doRenameN :: (NamingM s m, Named a) => Name -> a -> m a
doRenameN n a = withNG $ \ng -> doRename n ng a

doRenamesN :: (NamingM s m, Named a) => [Name] -> a -> m a
doRenamesN ns a = withNG $ \ng -> doRenames ns ng a

renameAllN :: (NamingM s m, Named a) => a -> m a
renameAllN a = withNG (renameAll a)

freshSeededStringN :: NamingM s m => T.Text -> m Name
freshSeededStringN t = withNG (freshSeededString t)

freshSeededStringsN :: NamingM s m => [T.Text] -> m [Name]
freshSeededStringsN t = withNG (freshSeededStrings t)

freshSeededNameN :: NamingM s m => Name -> m Name
freshSeededNameN n = withNG (freshSeededName n)

freshSeededNamesN :: NamingM s m => [Name] -> m [Name]
freshSeededNamesN ns = withNG (freshSeededNames ns)

freshNameN :: NamingM s m => m Name
freshNameN = withNG (freshName)

freshNamesN :: NamingM s m => Int -> m [Name]
freshNamesN i = withNG (freshNames i)

freshIdN :: NamingM s m => Type -> m Id
freshIdN t = withNG (freshId t)

freshSeededIdN :: (Named n, NamingM s m) => n -> Type -> m Id
freshSeededIdN n t = withNG (freshSeededId n t)

freshIdsN :: NamingM s m => [Type] -> m [Id]
freshIdsN ts = withNG (freshIds ts)
