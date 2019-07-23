module G2.Execution.MergingHelpers
  ( createEqExpr
  , createEqExprInt
  , getAssumption
  , isSMAssumption
  , liftCaseBinds
  , matchLitAlts
  , replaceCaseWSym
  , replaceCase
  , addClause
  ) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC

import qualified Data.Map as M
import qualified Data.HashSet as HS
import Debug.Trace

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
replaceCaseExpr s@(State {model = m, type_classes = tc}) (Case e i alts) =
    let val = subExpr m tc e
    in case val of
        (Lit lit) ->
            let (Alt (LitAlt _) expr):_ = matchLitAlts lit alts
                binds = [(i, Lit lit)]
            in replaceCaseExpr s $ liftCaseBinds binds expr
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

-- | Given a Case Expr created by merging exprs, replaces it with a symbolic variable. Encodes the choices in the NonDet Expr as Path Constraints
-- Called from evalApp when App center is Prim
replaceCaseWSym :: State t -> NameGen -> Expr -> (State t, NameGen, Expr)
replaceCaseWSym s@(State {expr_env = eenv, path_conds = pc, known_values = kv, symbolic_ids = syms}) ng (Case (Var i) bindI alts@(a:_)) =
    let (Alt _ altE) = a
        newSymT = returnType altE
        (newSym, ng') = freshId newSymT ng -- create new symbolic variable
        eenv' = E.insertSymbolic (idName newSym) newSym eenv
        syms' = HS.insert newSym syms

        pcs = concatMap (createPCs kv i bindI newSym) alts
        pc' = foldr PC.insert pc pcs

    in (s {expr_env = eenv', path_conds = pc', symbolic_ids = syms'}, ng', Var newSym)
replaceCaseWSym s ng (App e1 e2) =
    let (s', ng', e1') = replaceCaseWSym s ng e1
        (s'', ng'', e2') = replaceCaseWSym s' ng' e2
    in (s'', ng'', (App e1' e2'))
replaceCaseWSym s ng e = (s, ng, e)

-- For each Alt, add Path Constraints equating `newSymId` to the Alt Expr, enclosed in an AssumePC based on the matched Lit
createPCs :: KnownValues -> Id -> Id -> Id -> Alt -> [PathCond]
createPCs kv i bindId newSymId (Alt match e)
    | (LitAlt l@(LitInt val)) <- match =
        let bind = [(bindId, Lit l)]
            e' = liftCaseBinds bind e
            val' = fromInteger val
        in case e' of
            (Case (Var i') bindI' as) ->
                let newPCs = concatMap (createPCs kv i' bindI' newSymId) as
                in map (\pc -> AssumePC i val' pc) newPCs
            _ ->
                let pc = AssumePC i val' $ ExtCond (createEqExpr kv newSymId e') True
                in [pc]
    | otherwise = error $ "Unable to pattern match Alt: " ++ show (Alt match e)

getAssumption :: Expr -> (Id, Int)
getAssumption (App (App (Prim Eq _) (Var i)) (Lit (LitInt val))) = (i, fromInteger val)
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

-- Given an `ExtCond e b`, and an `Id`, `Int` pair, modifies `e` to (NOT (Id == Int)) OR e
addClause :: KnownValues -> Id -> Integer -> PathCond -> PathCond
addClause kv newId num pc = addClause' kv (mkEqIntExpr kv (Var newId) num) pc

addClause' :: KnownValues -> Expr -> PathCond -> PathCond
addClause' kv clause (ExtCond e b) =
    let e' = mkOrExpr kv (mkNotExpr kv clause) e
    in ExtCond e' b
addClause' _ _ pc = error $ "Can only add clause to ExtCond. Got: " ++ (show pc)


