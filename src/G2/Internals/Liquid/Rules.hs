{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module G2.Internals.Liquid.Rules ( LHRed (..)
                                 , LHHalter (..)
                                 , LHTracker (..)
                                 , lhReduce
                                 , initialTrack) where

import G2.Internals.Config
import G2.Internals.Execution.Reducer
import G2.Internals.Execution.Rules
import G2.Internals.Language
import qualified G2.Internals.Language.ApplyTypes as AT
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.Stack as S
import G2.Internals.Liquid.Annotations
import G2.Internals.Solver hiding (Assert)

import Data.Maybe
import Data.Monoid
import Data.Semigroup
import qualified Data.Text as T

import Debug.Trace

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
lhReduce :: [Name] -> Config -> State LHTracker -> (Rule, [ReduceResult LHTracker])
lhReduce ns = stdReduceBase (lhReduce' ns)

lhReduce' :: [Name] -> State LHTracker -> Maybe (Rule, [ReduceResult LHTracker])
lhReduce' ns
          State { expr_env = eenv
                , type_env = tenv
                , curr_expr = CurrExpr Evaluate vv@(Let _ (Assert _ _ _))
                , name_gen = ng
                , known_values = kv
                , apply_types = at
                , exec_stack = stck
                , track = tr } =
        let
            (r, er) = stdReduceEvaluate eenv vv tenv kv ng
            states = map (\(eenv', cexpr', paths', ngen', f) ->
                        ( eenv'
                        , cexpr'
                        , paths'
                        , []
                        , Nothing
                        , ngen'
                        , maybe stck (\f' -> S.push f' stck) f
                        , []
                        , []
                        , tr))
                       er
            sb = symbState ns eenv vv ng at stck tr
        in
        Just $ (r, states ++ maybeToList sb)
lhReduce' _ State { expr_env = eenv
                  , type_env = tenv
                  , curr_expr = CurrExpr Evaluate vv@(Var (Id n _))
                  , name_gen = ng
                  , known_values = kv
                  , exec_stack = stck
                  , track = tr} =
    let
        (r, er) = stdReduceEvaluate eenv vv tenv kv ng
        states = map (\(eenv', cexpr', paths', ngen', f) ->
                        ( eenv'
                        , cexpr'
                        , paths'
                        , []
                        , Nothing
                        , ngen'
                        , maybe stck (\f' -> S.push f' stck) f
                        , []
                        , []
                        , tr {last_var = Just n}))
                       er
    in
    Just $ (r, states)

lhReduce' _ _ = Nothing

symbState :: [Name] -> ExprEnv -> Expr -> NameGen -> ApplyTypes -> S.Stack Frame -> LHTracker -> Maybe (ReduceResult LHTracker)
symbState ns eenv 
          cexpr@(Let [(b, _)] (Assert (Just (FuncCall {funcName = fn, arguments = ars, returns = ret})) e _)) 
          ng at stck 
          tr@(LHTracker {abstract_calls = abs_c, last_var = Just last_v, annotations = annm }) =
    let
        cexprT = returnType cexpr

        (t, atf) = case AT.lookup cexprT at of
                        Just (t', f) -> (TyConApp t' TYPE, App (Var f))
                        Nothing -> (cexprT, id)

        (i, ng') = freshId t ng

        inferred = maybe [] (map snd) $ lookupAnnotAtLoc last_v annm -- lookupAnnot last_v annm
        inferredExprs = mkInferredAssumptions (ars ++ [ret]) inferred
        inferred' = foldr Assume (Var b) $ e:inferredExprs

        cexpr' = Let [(b, atf (Var i))] $ inferred'

        eenv' = E.insertSymbolic (idName i) i eenv

        -- the top of the stack may be an update frame for the variable currently being evaluated
        -- we don't want the definition to be updated with a symbolic variable, so we remove it
        -- stck' = case S.pop stck of
        --             Just (UpdateFrame u, stck'') -> if u == fn then stck'' else stck
        --             _ -> stck
        stck' = stck
    in
    -- There may be TyVars or TyBottom in the return type, in the case we have hit an error
    -- In this case, we cannot branch into a symbolic state
    case not (hasTyBottom cexprT) && null (tyVars cexprT) && fn `elem` ns of
        True -> Just (eenv', CurrExpr Evaluate cexpr', [], [], Nothing, ng', stck', [i], [], tr {abstract_calls = (FuncCall {funcName = fn, arguments = ars, returns = Var i}):abs_c})
        False -> Nothing
symbState _ _ _ _ _ _ _ = Nothing

-- Counts the maximal number of Vars with names in the ExprEnv
-- that could be evaluated along any one path in the function
initialTrack :: ExprEnv -> Expr -> Int
initialTrack eenv (Var (Id n _)) =
    case E.lookup n eenv of
        Just _ -> 1
        Nothing -> 0
initialTrack eenv (App e e') = initialTrack eenv e + initialTrack eenv e'
initialTrack eenv (Lam _ _ e) = initialTrack eenv e
initialTrack eenv (Let b e) = initialTrack eenv e + (getSum $ evalContainedASTs (Sum . initialTrack eenv) b)
initialTrack eenv (Case e _ a) = initialTrack eenv e + (getMax $ evalContainedASTs (Max . initialTrack eenv) a)
initialTrack eenv (Cast e _) = initialTrack eenv e
initialTrack eenv (Assume _ e) = initialTrack eenv e
initialTrack eenv (Assert _ _ e) = initialTrack eenv e
initialTrack _ _ = 0

mkInferredAssumptions :: [Expr] -> [Expr] -> [Expr]
mkInferredAssumptions ars_ret es = mkInferredAssumptions' (reverse ars_ret) es


mkInferredAssumptions' :: [Expr] -> [Expr] -> [Expr]
mkInferredAssumptions' _ [] = []
mkInferredAssumptions' ret_ars (e:es) =
    let
        cl = countLams e
        app = e:reverse (take cl ret_ars)
    in
    (mkApp app):mkInferredAssumptions' ret_ars es

countLams :: Expr -> Int
countLams (Lam _ _ e) = 1 + countLams e
countLams _ = 0

data LHTracker = LHTracker { abstract_calls :: [FuncCall]
                           , last_var :: Maybe Name
                           , annotations :: AnnotMap } deriving (Eq, Show)

instance Named LHTracker where
    names (LHTracker {abstract_calls = abs_c, last_var = n, annotations = annots}) = names abs_c ++ names n ++ names annots
    
    rename old new (LHTracker {abstract_calls = abs_c, last_var = n, annotations = annots}) =
        LHTracker {abstract_calls = rename old new abs_c, last_var = rename old new n, annotations = rename old new annots}
    
    renames hm (LHTracker {abstract_calls = abs_c, last_var = n, annotations = annots}) =
        LHTracker {abstract_calls = renames hm abs_c, last_var = renames hm n, annotations = renames hm annots}

instance ASTContainer LHTracker Expr where
    containedASTs (LHTracker {abstract_calls = abs_c, annotations = annots}) = containedASTs abs_c ++ containedASTs annots
    modifyContainedASTs f lht@(LHTracker {abstract_calls = abs_c, annotations = annots}) =
        lht {abstract_calls = modifyContainedASTs f abs_c, annotations = modifyContainedASTs f annots}

instance ASTContainer LHTracker Type where
    containedASTs (LHTracker {abstract_calls = abs_c, annotations = annots}) = containedASTs abs_c ++ containedASTs annots
    modifyContainedASTs f lht@(LHTracker {abstract_calls = abs_c, annotations = annots}) =
        lht {abstract_calls = modifyContainedASTs f abs_c, annotations = modifyContainedASTs f annots}

data LHRed con = LHRed [Name] con Config
-- data LHOrderer = LHOrderer T.Text (Maybe T.Text) ExprEnv
data LHHalter = LHHalter T.Text (Maybe T.Text) ExprEnv


instance Solver con => Reducer (LHRed con) LHTracker where
    redRules lhr@(LHRed ns solver config) s = do
        (r, s') <- reduce (lhReduce ns config) solver config s

        return $ (if r == RuleIdentity then Finished else InProgress, s', lhr)

instance Halter LHHalter Int LHTracker where
    initHalt (LHHalter entry modn eenv) _ _ =
        let 
            fe = case E.occLookup entry modn eenv of
                Just e -> e
                Nothing -> error "initOrder: Bad function passed"
        in
        initialTrack eenv fe

    reInitHalt _ ii (Processed {accepted = acc}) _ = minimum $ ii:map (length . abstract_calls . track) acc

    stopRed _ hv _ s = if length (abstract_calls $ track s) > hv then Discard else Continue

    stepHalter _ hv _ _ = hv
