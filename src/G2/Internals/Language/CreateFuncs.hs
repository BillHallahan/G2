module G2.Internals.Language.CreateFuncs where

import G2.Internals.Language.Expr
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support

import qualified Data.Map as M
import Data.Maybe

-- | createFuncs
-- Give a list of b's, and functions to generate names and expressions from those
-- b's, generates functions and puts them in the ExprEnv
-- The function to generate the expression gets the full list of b/Name pairs
-- All b/Name pairs are also stored in some s, using the provided function
createFuncs :: ExprEnv
            -> NameGen
            -> [b]
            -> s
            -> (b -> Name)
            -> (b -> Name -> s -> s)
            -> (s -> b -> NameGen -> (Expr, NameGen))
            -> (ExprEnv, NameGen, s)
createFuncs eenv ng genFrom store namef storef exprf =
    let
        --Generate names, put them in the store
        (names, ng2) = freshSeededNames (map namef genFrom) ng
        genFromNames = zip genFrom names

        fullStore = foldr (uncurry storef) store genFromNames

        --Generate functions, put them in the expression environment
        (exprfs, ng3) = mapNG (exprf fullStore) genFrom ng2
        eenv2 = foldr (uncurry E.insert) eenv (zip names exprfs)

    in
    (eenv2, ng3, fullStore)

