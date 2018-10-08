module G2.Internals.Language.Monad.ExprEnv ( memberE
                                           , lookupE
                                           , insertE
                                           , mapE
                                           , mapME ) where

import G2.Internals.Language

import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.Monad.Support

import Prelude hiding ( filter
                      , lookup
                      , map
                      , null)

liftEE :: ExState s m => (ExprEnv -> a) -> m a
liftEE f = return . f =<< exprEnv

memberE :: ExState s m => Name -> m Bool
memberE n = liftEE (E.member n)

lookupE :: ExState s m => Name -> m (Maybe Expr)
lookupE n = liftEE (E.lookup n)

insertE :: ExState s m => Name -> Expr -> m ()
insertE n e = do
    eenv <- exprEnv
    let eenv' = E.insert n e eenv
    putExprEnv eenv'

mapE :: ExState s m => (Expr -> Expr) -> m ()
mapE f = do
    eenv <- exprEnv
    let eenv' = E.map f eenv
    putExprEnv eenv'

mapME :: ExState s m => (Expr -> m Expr) -> m ()
mapME f = do
    eenv <- exprEnv
    eenv' <- E.mapM f eenv
    putExprEnv eenv'
