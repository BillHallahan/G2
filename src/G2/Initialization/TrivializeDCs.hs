module G2.Initialization.TrivializeDCs where

import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import G2.Language.Monad

import Data.Traversable

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