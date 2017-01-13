module G2.Core.SMT where

import G2.Core.Language
import G2.Core.FOL
import G2.Core.Evaluator

import qualified Data.List as L
import qualified Data.Map  as M

-- Prepare the environment before hand with data constructors.
-- mkSolverDataCons :: TEnv -> ???
-- mkSolverDataCons tv = undefined

-- Only values should appear here.
transExpr :: Expr -> Term
transExpr (Var n t)   = TVar n t
transExpr (Const c t)  = TConst c t
transExpr (Lam n e t) = undefined
transExpr (App f a)   = TApp (transExpr f) (transExpr a)

-- Translation of values?

{-
topTransExpr exp = case d of
    Var name -> let name' = name ++ "_" ++ (show $ length args)
                in TFun name' (map transExpr args)
    DCon (n,i,t,a) -> undefined
  where (d:args) = unrollApp exp
-}

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
