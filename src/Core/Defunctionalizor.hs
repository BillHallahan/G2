module G2.Core.Defunctionalizor where

import G2.Core.CoreManipulator
import G2.Core.Language

import qualified Data.List as L
import qualified Data.Map  as M

{-Defunctionalizor

We need to eliminate higher order functions to
enable a translation to SMT formulas.
-}

--defunctionalize :: State -> State

defunctionalize :: Expr -> Expr
defunctionalize e = e

--evalType :: (Type -> a) -> (a -> a -> a) -> Type -> a -> a
isHigherOrderFunc :: Type -> Bool
isHigherOrderFunc t = evalType isHigherOrderFunc' (||) t False
    where
        isHigherOrderFunc' :: Type -> Bool
        isHigherOrderFunc' _ = False