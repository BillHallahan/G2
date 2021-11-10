module G2.Language.Monad.ExprEnv ( memberE
                                 , lookupE
                                 , insertE
                                 , insertSymbolicE
                                 , mapE
                                 , mapME
                                 , mapWithKeyME ) where

import G2.Language

import qualified G2.Language.ExprEnv as E
import G2.Language.Monad.Support

import Prelude hiding ( filter
                      , lookup
                      , map
                      , null)

liftEE :: ExprEnvM s m => (ExprEnv -> a) -> m a
liftEE f = return . f =<< exprEnv

memberE :: ExprEnvM s m => Name -> m Bool
memberE n = liftEE (E.member n)

lookupE :: ExprEnvM s m => Name -> m (Maybe Expr)
lookupE n = liftEE (E.lookup n)

insertE :: ExprEnvM s m => Name -> Expr -> m ()
insertE n e = do
    eenv <- exprEnv
    let eenv' = E.insert n e eenv
    putExprEnv eenv'

insertSymbolicE :: ExprEnvM s m => Name -> Id -> m ()
insertSymbolicE n i = do
    eenv <- exprEnv
    let eenv' = E.insertSymbolic n i eenv
    putExprEnv eenv'

mapE :: ExprEnvM s m => (Expr -> Expr) -> m ()
mapE f = do
    eenv <- exprEnv
    let eenv' = E.map f eenv
    putExprEnv eenv'

mapME :: ExprEnvM s m => (Expr -> m Expr) -> m ()
mapME f = do
    eenv <- exprEnv
    eenv' <- E.mapM f eenv
    putExprEnv eenv'

mapWithKeyME :: ExprEnvM s m => (Name -> Expr -> m Expr) -> m ()
mapWithKeyME f = do
    eenv <- exprEnv
    eenv' <- E.mapWithKeyM f eenv
    putExprEnv eenv'
