module G2.Internals.Liquid.ConvertCurrExpr (addCurrExprAssumption) where

import G2.Internals.Language
import G2.Internals.Language.Monad

import G2.Internals.Liquid.Conversion
import G2.Internals.Liquid.Types
import qualified Data.Map as M
import Data.Maybe

addCurrExprAssumption :: Id -> LHStateM ()
addCurrExprAssumption ifi = do
    (CurrExpr er ce) <- currExpr

    assumpt <- lookupAssumptionM (idName ifi)
    fi <- fixedInputs
    is <- inputIds

    lh <- mapM (lhTCDict'' M.empty) $ mapMaybe typeType fi

    let (typs, ars) = span isType $ fi ++ map Var is

    case assumpt of
        Just assumpt' -> do
            let appAssumpt = mkApp $ assumpt':typs ++ lh ++ ars
            let ce' = Assume appAssumpt ce
            putCurrExpr (CurrExpr er ce')
        Nothing -> return ()

isType :: Expr -> Bool
isType (Type _) = True
isType _ = False

typeType :: Expr -> Maybe Type
typeType (Type t) = Just t
typeType _ = Nothing