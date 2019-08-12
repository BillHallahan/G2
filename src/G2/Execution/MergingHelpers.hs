module G2.Execution.MergingHelpers
  ( createEqExpr
  , createEqExprInt
  , getAssumption
  , isSMAssumption
  , liftCaseBinds
  , matchLitAlts
  , replaceCaseWSym
  , replaceCase
  ) where

import G2.Language
import G2.Execution.StateMerging
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC

import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.HashSet as HS

-- | Removes any Case-s in the expr_env and curr_expr by selecting one choice each time
-- e.g. Given an Expr `Case x of 1 -> e1, 2 -> e2`, lookups the value of `x`
-- in the `Model` of the state and picks the corresponding Expr e1 or e2.
replaceCase :: State t -> State t
replaceCase s@(State {curr_expr = cexpr, expr_env = eenv}) =
    let eenv' = E.map (replaceCaseExpr s) eenv
        (CurrExpr eOrR e) = cexpr 
        cexpr' = CurrExpr eOrR (replaceCaseExpr s e)
    in (s {curr_expr = cexpr', expr_env = eenv'})

replaceCaseExpr :: State t -> Expr -> Expr
replaceCaseExpr s (App e1 e2) = App (replaceCaseExpr s e1) (replaceCaseExpr s e2)
replaceCaseExpr s@(State {model = m, type_classes = tc}) cse@(Case e i alts@(Alt (LitAlt _) _:_)) =
    let val = subExpr m tc e
    in case val of
        (Lit lit) ->
            let
                binds = [(i, Lit lit)]
            in
            case matchLitAlts lit alts of
                (Alt (LitAlt _) expr):_ -> replaceCaseExpr s $ liftCaseBinds binds expr
                    -- The above may not match if an expression constraining a variable
                    -- introduced from merging had an implication added by another merge,
                    -- and that implication was not satisfied by the model.
                    -- In this situation, we do not need to replace the case expression
                _ -> error "replaceCaseExpr: No bound value"
        _ -> error $ "Unable to find Lit value for e. Got: " ++ show val
replaceCaseExpr _ e = e

-- | Looks up values in the `Model` of the state and substitutes into @`e`
subExpr :: Model -> TypeClasses -> Expr -> Expr
subExpr m tc = modifyContainedASTs (subExpr' m tc [])

subExpr' :: Model -> TypeClasses -> [Id] -> Expr -> Expr
subExpr' m tc is v@(Var i@(Id n _))
    | i `notElem` is
    , Just e <- M.lookup n m =
        subExpr' m tc (i:is) e
    | otherwise = v
subExpr' m tc is e = modifyChildren (subExpr' m tc is) e

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
        (_, newPCs) = bindExprToNum (\num e -> PC.mkAssumePC i (fromInteger num) (ExtCond e True)) es'

        -- for the PathConds returned from replaceCaseWSym', wrap them in AssumePCs
        pcsL' = concat . snd $ bindExprToNum (\num pcs -> map (\pc -> PC.mkAssumePC i (fromInteger num) pc) pcs) pcsL
        -- we assume PathCond restricting values of `i` has already been added before hand when creating the Case Expr

        eenv' = expr_env s'
        eenv'' = E.insertSymbolic (idName newSym) newSym eenv'
        syms' = symbolic_ids s'
        syms'' = HS.insert newSym syms'

    in ((s' {expr_env = eenv'', symbolic_ids = syms''}, ng''), (Var newSym, newPCs ++ pcsL'))
replaceCaseWSym' (s, ng) (App e1 e2) =
    let ((s', ng'), (e1', newPCs1)) = replaceCaseWSym' (s, ng) e1
        ((s'', ng''), (e2', newPCs2)) = replaceCaseWSym' (s', ng') e2
    in ((s'', ng''), ((App e1' e2'), newPCs1 ++ newPCs2))
replaceCaseWSym' (s, ng) e = ((s, ng), (e, []))

getAssumption :: Expr -> (Id, Integer)
getAssumption (App (App (Prim Eq _) (Var i)) (Lit (LitInt val))) = (i, val)
getAssumption e = error $ "Unable to extract Id, Int from Assumed Expr: " ++ (show e)

-- | Returns True is Expr can be pattern matched against Assume-d Expr created during state merging
isSMAssumption :: Expr -> Bool
isSMAssumption (App (App (Prim Eq _) (Var _)) (Lit (LitInt _))) = True
isSMAssumption _ = False

-- | Returns an Expr equivalent to "x == val", where x is a Var created from the given Id
createEqExprInt :: KnownValues -> Id -> Integer -> Expr
createEqExprInt kv newId val = createEqExpr kv newId (Lit (LitInt val))

createEqExpr :: KnownValues -> Id -> Expr -> Expr
createEqExpr kv newId e = App (App eq (Var newId)) e 
    where eq = mkEqPrimInt kv

-- | Match literal constructor based `Alt`s.
matchLitAlts :: Lit -> [Alt] -> [Alt]
matchLitAlts lit alts = [a | a @ (Alt (LitAlt alit) _) <- alts, lit == alit]

liftCaseBinds :: [(Id, Expr)] -> Expr -> Expr
liftCaseBinds [] expr = expr
liftCaseBinds ((b, e):xs) expr = liftCaseBinds xs $ replaceASTs (Var b) e expr
