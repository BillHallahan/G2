module G2.Internals.Liquid.Rules where

import G2.Internals.Execution.NormalForms
import G2.Internals.Execution.Rules
import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.Stack as S

import qualified Data.Map as M
import Data.Maybe

-- lhReduce
-- When reducing for LH, we change the rule for evaluating Var f.
-- Var f can potentially split into two states.
-- (a) One state is exactly the same as the current reduce function: we lookup
--     up the var, and set the curr expr to its definition.
-- (b) [StateB] The other var is created if the definition of f is of the form:
--     lam x_1 ... lam x_n . let x = f x_1 ... x_n in Assert (a x_1 ... x_n x) x
--
--     We introduce a new symbolic variable x_s, with the same type of s, and
--     set the curr expr to
--     let x = x_s in Assert (a x'_1 ... x'_n x_s) x_s
--     appropriately binding x'_i to x_i in the expression environment
--
--     This allows us to choose any value for the return type of the function.
--     In this rule, we also return a b, oldb `mappend` [(f, [x_1, ..., x_n], x)]
--     This is essentially abstracting away the function definition, leaving
--     only the information that LH also knows (that is, the information in the
--     refinment type.)
lhReduce :: State [(Name, [Expr], Expr)] -> (Rule, [ReduceResult [(Name, [Expr], Expr)]])
lhReduce = stdReduceBase lhReduce'


lhReduce' :: State [(Name, [Expr], Expr)] -> Maybe (Rule, [ReduceResult [(Name, [Expr], Expr)]])
lhReduce' State { expr_env = eenv
               , curr_expr = CurrExpr Evaluate vv@(Let [(b, e)] a@(Assert _ _ _))
               , name_gen = ng
               , exec_stack = stck
               , track = tr } =
        let
            (r, er) = stdReduceEvaluate eenv vv ng
            states = map (\(eenv', cexpr', paths', ngen', f) ->
                        ( eenv'
                        , cexpr'
                        , paths'
                        , []
                        , Nothing
                        , ngen'
                        , maybe stck (\f' -> S.push f' stck) f
                        , []
                        , tr))
                       er
            sb = symbState eenv vv ng stck tr
        in
        Just $ (r, states ++ [sb])
lhReduce' _ = Nothing

symbState :: ExprEnv -> Expr -> NameGen -> S.Stack Frame -> [(Name, [Expr], Expr)] -> (ReduceResult [(Name, [Expr], Expr)])
symbState eenv cexpr@(Let [(b, _)] (Assert (Just (fn, ars, re)) e e')) ng stck tr =
    let
        (i, ng') = freshId (returnType cexpr) ng

        cexpr' = Let [(b, Var i)] $ Assume e (Var b)

        eenv' = E.insertSymbolic (idName i) i eenv
    in
    (eenv', CurrExpr Evaluate cexpr', [], [], Nothing, ng', stck, [i], (fn, map Var ars, Var i):tr)
symbState _ _ _ _ _ = error "Bad expr in symbState"