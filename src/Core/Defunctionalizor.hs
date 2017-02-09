module G2.Core.Defunctionalizor where

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

isHigherOrderFunc :: Type -> Bool
isHigherOrderFunc (TyFun (TyFun _ _) _) = True
isHigherOrderFunc (TyFun t1 t2) = (isHigherOrderFunc t1) || (isHigherOrderFunc t2)
isHigherOrderFunc (TyApp t1 t2) = (isHigherOrderFunc t1) || (isHigherOrderFunc t2)
isHigherOrderFunc (TyConApp n ts) = or . map (\t' -> isHigherOrderFunc t') $ ts
--isHigherOrderFunc (TyAlg n ts) = or . map (\t' -> isHigherOrderFunc' t' ) $ ts
isHigherOrderFunc (TyForAll n t) = isHigherOrderFunc t
isHigherOrderFunc _ = False