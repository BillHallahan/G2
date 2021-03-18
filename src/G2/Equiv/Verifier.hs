module G2.Equiv.Verifier () where

import G2.Language

import G2.Config

import G2.Interface

import qualified Control.Monad.State.Lazy as CM

import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Typing as T

import qualified Data.HashSet as HS
import qualified G2.Solver as S

exprReadyForSolver :: ExprEnv -> Expr -> Bool
exprReadyForSolver h (Var i) = E.isSymbolic (idName i) h && T.isPrimType (typeOf i)
exprReadyForSolver h (App f a) = exprReadyForSolver h f && exprReadyForSolver h a
exprReadyForSolver h (Prim _ _) = True
exprReadyForSolver h (Lit _) = True
exprReadyForSolver h _ = False

readyForSolver :: (ExprEnv, ExprEnv) -> (Expr, Expr) -> Bool
readyForSolver (h1, h2) (e1, e2) =
  exprReadyForSolver h1 e1 && exprReadyForSolver h2 e2

runSymExec :: Config ->
              State () ->
              State () ->
              CM.StateT (Bindings, Bindings) IO ([State ()], [State ()])
runSymExec config s1 s2 = do
  (bindings1, bindings2) <- CM.get
  (exec_res1, bindings1') <- CM.lift $ runG2WithConfig s1 config bindings1
  (exec_res2, bindings2') <- CM.lift $ runG2WithConfig s2 config bindings2
  CM.put (bindings1', bindings2')
  return (map final_state exec_res1, map final_state exec_res2)

-- build initial hash set in Main before calling
{-
Things to do:
Iterate over every pair of states produced
Put it into the solver, see if it's equivalent
If any pair isn't, reject
-}
verifyLoop :: S.Solver solver =>
              solver ->
              HS.HashSet (State (), State ()) ->
              Bindings ->
              Bindings ->
              Config ->
              IO (S.Result () ())
verifyLoop solver states b1 b2 config = do
  v <- CM.runStateT (mapM (uncurry (runSymExec config)) (HS.toList states)) (b1, b2)
  error "TODO"
