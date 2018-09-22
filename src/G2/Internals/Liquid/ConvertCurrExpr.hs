module G2.Internals.Liquid.ConvertCurrExpr where

import G2.Internals.Language
import G2.Internals.Language.Monad
import G2.Internals.Liquid.Types

addCurrExprAssumption :: Id -> LHStateM ()
addCurrExprAssumption ifi = do
    (CurrExpr er ce) <- currExpr

    assumpt <- lookupAssumptionM (idName ifi)
    is <- inputIds

    case assumpt of
        Just assumpt' -> do
            let appAssumpt = mkApp $ assumpt':map Var is
            let ce' = Assume appAssumpt ce
            putCurrExpr (CurrExpr er ce')
        Nothing -> return ()