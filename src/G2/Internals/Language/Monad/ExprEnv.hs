module G2.Internals.Language.Monad.ExprEnv ( memberE
                                           , lookupE
                                           , insertE ) where

import G2.Internals.Language

import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.Monad.Support

import Prelude hiding( filter
                     , lookup
                     , map
                     , null)

liftEE :: (ExprEnv -> a) -> StateM t a
liftEE f = readRecord (f . expr_env)

memberE :: Name -> StateM t Bool
memberE n = liftEE (E.member n)

lookupE :: Name -> StateM t (Maybe Expr)
lookupE n = liftEE (E.lookup n)

insertE :: Name -> Expr -> StateM t ()
insertE n e = do
    eenv <- expr_envM
    let eenv' = E.insert n e eenv
    rep_expr_envM eenv'