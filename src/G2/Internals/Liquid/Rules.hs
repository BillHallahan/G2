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
--     lam x_1 ... lam x_n . let x = x_s in Assert (a x_1 ... x_n x_s) x_s
--
--     This allows us to choose any value for the return type of the function.
--     In this rule, we also return a b, oldb ++ [(f, [x_1, ..., x_n], x)]
--     This is essentially abstracting away the function definition, leaving
--     only the information that LH also knows (that is, the information in the
--     refinment type.)
lhReduce :: State [(Name, [Id], Id)] -> (Rule, [ReduceResult [(Name, [Id], Id)]])
lhReduce = stdReduceBase lhReduceEvaluate

lhReduceEvaluate :: E.ExprEnv -> Expr -> NameGen -> (Rule, [EvaluateResult [(Name, [Id], Id)]])
lhReduceEvaluate eenv vv@(Var v) ng
    | Just expr <- E.lookup (idName v) eenv =
        let
            (r, frame) = if isExprValueForm expr eenv 
                            then ( RuleEvalVarVal (idName v), Nothing)
                            else ( RuleEvalVarNonVal (idName v)
                                 , Just $ UpdateFrame (idName v))

            sa = ( eenv
                 , CurrExpr Evaluate expr
                 , []
                 , ng
                 , frame
                 , [])

            sb = symbState expr eenv vv ng
        in
        ( r
        , sa:maybeToList sb)
lhReduceEvaluate eenv cexpr ng = stdReduceEvaluate eenv cexpr ng

-- | symbState
-- See [StateB]
symbState :: Expr -> ExprEnv -> Expr -> NameGen -> Maybe (EvaluateResult [(Name, [Id], Id)])
symbState vv eenv cexpr@(Var (Id n _)) ng =
    let
        (i, ng') = freshId (returnType cexpr) ng
        eenv' = E.insertSymbolic (idName i) i eenv

        cexpr' = maybeInsertInLams (symbCexpr i) vv
    in
    case cexpr' of
        Just cexpr'' -> 
            Just (eenv', CurrExpr Evaluate cexpr'', [], ng', Nothing, [])
        Nothing -> Nothing
symbState _ _ _ _ = Nothing

symbCexpr :: Id -> [Id] -> Expr -> Maybe Expr
symbCexpr i _ (Let [(b, e)] a@(Assert _ _ (Var b'))) =
    if b == b' 
        then Just $ Let [(b, Var i)] a 
        else Nothing
symbCexpr _ _ e = Nothing

argsAndRet :: Expr -> ([Id], Id)
argsAndRet (Lam i e) =
    let
        (is, a) = argsAndRet e
    in
    (i:is, a)
argsAndRet (Let [(b, _)] _) = ([], b)