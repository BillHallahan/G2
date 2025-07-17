module G2.Initialization.TrivializeDCs where

import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import G2.Language.Monad

import Data.Traversable

-- note [Cons DC]
-- When using SMT strings, we must ensure that all strings can be represented in the
-- SMT solver.  To do this, we make use of an adjStr function (in GHC.Prim2) which forces evaluation
-- of a string.
-- So we have, for instance:
--
--   @ xs == ys = let
--      ...
--      in case typeIndex# xs `adjStr` xs `adjStr` ys of
--          1# -> strEq# xs ys
--          ... @
-- to force xs and ys to an SMT representable form, which can then be passed to strEq#. Note that
-- this relies on being able to share the result of computing `xs` and `ys` between when they are forced
-- by adjStr and when thet are used in strEq#.
--
-- However, suppose we have something like:
--   @ a:as ++ bs == "hello" @
-- What happens here is we bind:
--      xs -> (a:as ++ bs)
--      ys -> "hello"
-- and adjStr does walk over xs.  However, because there is no intermediate variable in the tail
-- of the list `a:as ++ bs`. we do not actuall getting any sharing- and so, adjStr does not have
-- the desired effect.
-- The solution is to rewrite cons constructors using lets to ensure that we always getting sharing.
-- The above is rewritten to:
--      @ let zs = as ++ bs in a:zs == "hello" @
-- Allowing sharing to happen via `zs`.

-- | Ensure that all non-trivial arguments to list cons data constructors
-- are wrapped in arguments.
-- See note [Cons DC]
trivializeDCs :: NameGen -> KnownValues -> ExprEnv -> (ExprEnv, NameGen)
trivializeDCs ng kv eenv =
    runNamingM (trivializeDCs' kv eenv) ng

trivializeDCs' :: KnownValues -> ExprEnv -> NameGenM ExprEnv
trivializeDCs' kv = E.mapM (modifyM go)
    where
        go a@(App _ _)
            | (d@(Data (DataCon { dc_name = dcn}))):es <- unApp a
            , dcn == dcCons kv = do
                (new_binds, es') <-
                    mapAccumM (\nbs e ->
                        if isSimple e
                            then return (nbs, e)
                            else do
                                fr <- freshIdN (typeOf e)
                                return ((fr, e):nbs, Var fr)) [] es
                case new_binds of
                    [] -> return a
                    _ -> return $ Let new_binds (mkApp $ d:es')
            | otherwise = return a
            where
                isSimple (Var _) = True
                isSimple (Lit _) = True
                isSimple (Prim _ _) = True
                isSimple (Type _) = True
                isSimple _ = False
        go e = return e