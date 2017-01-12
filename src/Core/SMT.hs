module G2.Core.SMT where

import G2.Core.Language
import G2.Core.FOL
import G2.Core.Evaluator

import qualified Data.List as L
import qualified Data.Map  as M


-- Translation of values?
{-
translateExpr :: Expr -> Term
translateExpr exp = case d of
    Var a -> let name' = a ++ "_" ++ (show $ length args)
             in TFun name' (map translateExpr args)
    DCon (name, tag, pars) -> let name' = name ++ "_" ++  (show $ length args)
                              in TFun name' (map translateExpr args)
  where (d:args) = unrollApp exp

translateAlt :: Alt -> Term
translateAlt (dcon, args) = TDataCon dcon (map TVar args)
-}
