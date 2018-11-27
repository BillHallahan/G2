module G2.Language.Monad.CreateFuncs where

import G2.Language.Monad.ExprEnv
import G2.Language.Monad.Naming
import G2.Language.Monad.Support
import G2.Language.Syntax

import Control.Monad

-- createFuncsM
-- Given a list of b's, a function to map the b's to Names
-- and a function to map those b's to Expr
-- Generates pairs of names and Expr's and put's them in the ExprEnv
-- Also returns a s, of Name/Expr pairs
createFuncsM :: ExState st m => 
                [b]
             -> s
             -> (b -> m Name)
             -> (b -> Name -> s -> m s)
             -> (s -> b -> m Expr)
             -> m s
createFuncsM genFrom store namef storef exprf = do
    ns <- freshSeededNamesN =<< mapM namef genFrom

    let genFromNames = zip genFrom ns
    -- let fullStore = foldr (uncurry storef) store genFromNames
    fullStore <- foldM (\s (b, n) -> storef b n s) store genFromNames

    exprfs <- mapM (exprf fullStore) genFrom

    sequence_ $ map (uncurry insertE) (zip ns exprfs)

    return fullStore
