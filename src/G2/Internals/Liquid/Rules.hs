{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Internals.Liquid.Rules ( LHRed (..)
                                 , LHHalter (..)
                                 , lhReduce
                                 , initialTrack) where

import G2.Internals.Execution.Reducer
import G2.Internals.Execution.Rules
import G2.Internals.Language
import qualified G2.Internals.Language.ApplyTypes as AT
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.Stack as S

import Data.Maybe
import Data.Monoid
import Data.Semigroup
import qualified Data.Text as T

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
lhReduce :: State [FuncCall] -> (Rule, [ReduceResult [FuncCall]])
lhReduce = stdReduceBase lhReduce'

lhReduce' :: State [FuncCall] -> Maybe (Rule, [ReduceResult [FuncCall]])
lhReduce' State { expr_env = eenv
               , curr_expr = CurrExpr Evaluate vv@(Let _ (Assert _ _ _))
               , name_gen = ng
               , apply_types = at
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
            sb = symbState eenv vv ng at stck tr
        in
        Just $ (r, states ++ maybeToList sb)
lhReduce' _ = Nothing

symbState :: ExprEnv -> Expr -> NameGen -> ApplyTypes -> S.Stack Frame -> [FuncCall] -> Maybe (ReduceResult [FuncCall])
symbState eenv cexpr@(Let [(b, _)] (Assert (Just (FuncCall {funcName = fn, arguments = ars})) e _)) ng at stck tr =
    let
        cexprT = returnType cexpr

        (t, atf) = case AT.lookup cexprT at of
                        Just (t', f) -> (TyConApp t' [], App (Var f))
                        Nothing -> (cexprT, id)

        (i, ng') = freshId t ng

        cexpr' = Let [(b, atf (Var i))] $ Assume e (Var b)

        eenv' = E.insertSymbolic (idName i) i eenv

        -- the top of the stack may be an update frame for the variable currently being evaluated
        -- we don't want the definition to be updated with a symbolic variable, so we remove it
        stck' = case S.pop stck of
                    Just (UpdateFrame u, stck'') -> if u == fn then stck'' else stck
                    _ -> stck
    in
    -- There may be TyVars or TyBottom in the return type, in the case we have hit an error
    -- In this case, we cannot branch into a symbolic state
    case not (hasTyBottom cexprT) && null (tyVars cexprT) of
        True -> Just (eenv', CurrExpr Evaluate cexpr', [], [], Nothing, ng', stck', [i], (FuncCall {funcName = fn, arguments = ars, returns = Var i}):tr)
        False -> Nothing
symbState _ _ _ _ _ _ = error "Bad expr in symbState"

-- Counts the maximal number of Vars with names in the ExprEnv
-- that could be evaluated along any one path in the function
initialTrack :: ExprEnv -> Expr -> Int
initialTrack eenv (Var (Id n _)) =
    case E.lookup n eenv of
        Just _ -> 1
        Nothing -> 0
initialTrack eenv (App e e') = initialTrack eenv e + initialTrack eenv e'
initialTrack eenv (Lam _ e) = initialTrack eenv e
initialTrack eenv (Let b e) = initialTrack eenv e + (getSum $ evalContainedASTs (Sum . initialTrack eenv) b)
initialTrack eenv (Case e _ a) = initialTrack eenv e + (getMax $ evalContainedASTs (Max . initialTrack eenv) a)
initialTrack eenv (Cast e _) = initialTrack eenv e
initialTrack eenv (Assume _ e) = initialTrack eenv e
initialTrack eenv (Assert _ _ e) = initialTrack eenv e
initialTrack _ _ = 0

data LHRed = LHRed
-- data LHOrderer = LHOrderer T.Text (Maybe T.Text) ExprEnv
data LHHalter = LHHalter T.Text (Maybe T.Text) ExprEnv


instance Reducer LHRed [FuncCall] where
    redRules _ = lhReduce

instance Halter LHHalter Int [FuncCall] where
    initHalt (LHHalter entry modn eenv) _ _ =
        let 
            fe = case E.occLookup entry modn eenv of
                Just e -> e
                Nothing -> error "initOrder: Bad function passed"
        in
        initialTrack eenv fe

    reInitHalt _ ii (Processed {accepted = acc}) _ = minimum $ ii:map (length . track) acc

    stopRed _ hv _ s = if length (track s) > hv then Discard else Continue

    stepHalter _ hv _ _ = hv
