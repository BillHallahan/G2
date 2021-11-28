module G2.Execution.Merging.MergingHelpers
  ( createEqExpr
  , replaceCaseWSym
  , exprToPCs
  ) where

import G2.Language
import G2.Execution.Merging.StateMerging
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC

import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS

-- | Given a Case Expr created by merging exprs, replaces it with a symbolic variable. Encodes the choices in the Case Expr as Path Constraints
-- Called from evalApp when App center is Prim
replaceCaseWSym :: State t -> NameGen -> Expr -> (State t, NameGen, Expr)
replaceCaseWSym s@(State {path_conds = pc}) ng e =
    let ((s', ng'), (e', newPCs)) = replaceCaseWSym' (s, ng) e
        pc' = foldr PC.insert pc newPCs
    in (s' {path_conds = pc'}, ng', e')

-- e.g. given App A (Case x of 1 -> App B (Case x' of 1 -> a, 2-> b), 2 -> App B c)
-- return App A n, with new PathConds:
-- [x = 1 => n = App B n', x = 2 => n = App B c, x = 1 => x' = 1 => n' = a, x = 1 => x' = 2 => n' = b]
replaceCaseWSym' :: (State t, NameGen) -> Expr -> ((State t, NameGen), (Expr, [PathCond]))
replaceCaseWSym' (s@(State {known_values = kv}), ng) (Case (Var i) _ alts@(a:_)) =
    let (Alt _ altE) = a
        newSymT = returnType altE
        (newSym, ng') = freshId newSymT ng -- create new symbolic variable

        -- No need to bind Id in Case Expr to `altEs` since it must have been generated only when merging states
        altEs = map (\(Alt (LitAlt _) e) -> e) alts
        ((s', ng''), res) = L.mapAccumL replaceCaseWSym' (s, ng') altEs
        (es, pcsL) = L.unzip res

        -- for each modified Alt Expr, add Path Cond
        es' = map (mkEqPrimExpr newSymT kv (Var newSym)) es
        (_, newPCs) = bindExprToNum (\num e -> PC.mkSingletonAssumePC i (fromInteger num) (ExtCond e True)) es'

        -- for the PathConds returned from replaceCaseWSym', wrap them in AssumePCs
        pcsL' = concat . snd $ bindExprToNum (\num pcs -> map (\pc -> PC.mkSingletonAssumePC i (fromInteger num) pc) pcs) pcsL
        -- we assume PathCond restricting values of `i` has already been added before hand when creating the Case Expr

        eenv' = expr_env s'
        eenv'' = E.insertSymbolic newSym eenv'
    in ((s' {expr_env = eenv''}, ng''), (Var newSym, newPCs ++ pcsL'))
replaceCaseWSym' (s, ng) (App e1 e2) =
    let ((s', ng'), (e1', newPCs1)) = replaceCaseWSym' (s, ng) e1
        ((s'', ng''), (e2', newPCs2)) = replaceCaseWSym' (s', ng') e2
    in ((s'', ng''), ((App e1' e2'), newPCs1 ++ newPCs2))
replaceCaseWSym' (s, ng) e = ((s, ng), (e, []))

exprToPCs :: Expr -> Bool -> [PathCond]
exprToPCs (Case (Var i) _ alts) boolVal =
    let altEs = map (\(Alt (LitAlt (LitInt n)) e) -> (n, e)) alts
        -- wrap Exprs in AssumePCs
        -- we assume PathCond restricting values of `i` has already been added before hand when creating the Case Expr
    in map (\(num, e) -> PC.mkSingletonAssumePC i num (ExtCond e boolVal)) altEs
exprToPCs e boolVal = [ExtCond e boolVal]

createEqExpr :: KnownValues -> Id -> Expr -> Expr
createEqExpr kv newId e = App (App eq (Var newId)) e 
    where eq = mkEqPrimInt kv
