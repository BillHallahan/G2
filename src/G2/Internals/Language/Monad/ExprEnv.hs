module G2.Internals.Language.Monad.ExprEnv ( memberE
                                           , lookupE
                                           , insertE ) where

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