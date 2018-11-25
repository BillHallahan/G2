{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module G2.Internals.Liquid.Rules ( LHRed (..)
                                 , LHLimitByAcceptedHalter
                                 , LHLimitByAcceptedOrderer
                                 , LHAbsHalter (..)
                                 , LHTracker (..)
                                 , lhReduce
                                 , initialTrack

                                 , limitByAccepted) where

import G2.Internals.Config
import G2.Internals.Execution.Reducer
import G2.Internals.Execution.Rules
import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.Stack as S
import G2.Internals.Liquid.Annotations
import G2.Internals.Solver hiding (Assert)

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
lhReduce :: Config -> State LHTracker -> (Rule, [ReduceResult LHTracker])
lhReduce = stdReduceBase lhReduce'

lhReduce' :: State LHTracker -> Maybe (Rule, [ReduceResult LHTracker])
lhReduce' State { expr_env = eenv
                , type_env = tenv
                , curr_expr = CurrExpr Evaluate vv@(Let _ (Assert _ _ _))
                , name_gen = ng
                , known_values = kv
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
            sb = symbState eenv vv ng stck tr
        in
        Just $ (r, states ++ maybeToList sb)
-- We override the default Let case, so we can add function bindings
-- to our list of abstractable functions
lhReduce' State { expr_env = eenv
                , curr_expr = CurrExpr Evaluate (Let b e)
                , name_gen = ng
                , exec_stack = stck
                , track = tr } =
    let 
        (eenv', e', ng', news) = liftLetBinds b eenv e ng

        absM = map snd . filter (hasFuncType . fst) $ zip (map fst b) news
    in
    Just 
       ( RuleEvalLet news
       , [( eenv'
          , CurrExpr Evaluate e'
          , []
          , []
          , Nothing
          , ng'
          , stck
          , []
          , []
          , tr { abstractable = abstractable tr ++ absM })])
lhReduce' State { expr_env = eenv
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

lhReduce' _ = Nothing

symbState :: ExprEnv -> Expr -> NameGen -> S.Stack Frame -> LHTracker -> Maybe (ReduceResult LHTracker)
symbState eenv 
          cexpr@(Let [(b, _)] (Assert (Just (FuncCall {funcName = fn, arguments = ars })) e _)) 
          ng stck 
          tr@(LHTracker { abstractable = ns
                        , abstract_calls = abs_c }) =
    let
        cexprT = returnType cexpr

        -- We have to retype this Id, so it has the correct type in the Symbolic Id list
        idToT = tysBoundByStack eenv stck cexpr
        cexprT' = foldr (uncurry retype) cexprT idToT
        -- (i, ng') = freshId cexprT' ng
        sg = SymGen cexprT'

        -- Create lambdas, to gobble up any ApplyFrames left on the stack
        (lams, ng'') = tyBindings ng cexpr

        -- If the type of b is not the same as cexprT's type, we have no assumption,
        -- so we get a new b.  Otherwise, we just keep our current b,
        -- in case it is used in the assertion
        (b', ng''') = if typeOf b == cexprT then (b, ng'') else freshId cexprT ng''

        cexpr' = lams $ Assume e (Var b')

        -- We add the Id's from the newly created Lambdas to the arguments list
        lamI = map Var $ leadingLamIds cexpr'

        eenv' = E.insert (idName b') sg eenv
    in
    -- There may be TyBottom in the return type, in the case we have hit an error
    -- In this case, we cannot branch into a symbolic state
    case not (hasTyBottom cexprT) && fn `elem` ns of
        True -> Just ( eenv'
                     , CurrExpr Evaluate cexpr'
                     , []
                     , []
                     , Nothing
                     , ng'''
                     , stck
                     , []
                     , []
                     , tr { abstract_calls = (FuncCall {funcName = fn, arguments = ars ++ lamI
                          , returns = Var b'}):abs_c}
                     )
        False -> Nothing
symbState _ _ _ _ _ = Nothing

-- Creates Lambda bindings to saturate the type of the given Typed thing,
-- and a list of the bindings so they can be used elsewhere
tyBindings :: Typed t => NameGen -> t -> (Expr -> Expr, NameGen)
tyBindings ng t =
    let
        at = spArgumentTypes t
        (fn, ng') = freshNames (length at) ng
    in
    (tyBindings' fn at, ng')

tyBindings' :: [Name] -> [ArgType] -> Expr -> Expr
tyBindings' _ [] = id
tyBindings' ns (NamedType i:ts) = Lam TypeL i . tyBindings' ns ts
tyBindings' (n:ns) (AnonType t:ts) = Lam TermL (Id n t) . tyBindings' ns ts
tyBindings' [] _ = error "Name list exhausted in tyBindings'"

tysBoundByStack :: Typed t => ExprEnv -> S.Stack Frame -> t -> [(Id, Type)]
tysBoundByStack eenv s t = tysBoundByStack' eenv s (typeOf t)

tysBoundByStack' :: ExprEnv -> S.Stack Frame -> Type -> [(Id, Type)]
tysBoundByStack' eenv s (TyFun _ t)
    | Just (_, s') <- S.pop s = tysBoundByStack' eenv s' t
tysBoundByStack' eenv s (TyForAll b t)
    | NamedTyBndr i <- b
    , Just (ApplyFrame e, s') <- S.pop s
    , Just t' <- getTypeExpr eenv e =
        (i, t'):tysBoundByStack' eenv s' t'
    | Just (_, s') <- S.pop s =  tysBoundByStack' eenv s' t
tysBoundByStack' _ _ _ = []

getTypeExpr :: ExprEnv -> Expr -> Maybe Type
getTypeExpr eenv (Var (Id n _)) =
    case E.lookup n eenv of
        Just e -> getTypeExpr eenv e
        Nothing -> Nothing
getTypeExpr _ (Type t) = Just t
getTypeExpr _ _ = Nothing

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

data LHTracker = LHTracker { abstractable :: [Name]
                           , abstract_calls :: [FuncCall]
                           , last_var :: Maybe Name
                           , annotations :: AnnotMap } deriving (Eq, Show)

instance Named LHTracker where
    names (LHTracker {abstractable = abst, abstract_calls = abs_c, last_var = n, annotations = anns}) = 
        names abst ++ names abs_c ++ names n ++ names anns
    
    rename old new (LHTracker {abstractable = abst, abstract_calls = abs_c, last_var = n, annotations = anns}) =
        LHTracker { abstractable = rename old new abst
                  , abstract_calls = rename old new abs_c
                  , last_var = rename old new n
                  , annotations = rename old new anns }
    
    renames hm (LHTracker {abstractable = abst, abstract_calls = abs_c, last_var = n, annotations = anns}) =
        LHTracker { abstractable = renames hm abst
                  , abstract_calls = renames hm abs_c
                  , last_var = renames hm n
                  , annotations = renames hm anns }

instance ASTContainer LHTracker Expr where
    containedASTs (LHTracker {abstract_calls = abs_c, annotations = anns}) =
        containedASTs abs_c ++ containedASTs anns
    modifyContainedASTs f lht@(LHTracker {abstract_calls = abs_c, annotations = anns}) =
        lht {abstract_calls = modifyContainedASTs f abs_c, annotations = modifyContainedASTs f anns}

instance ASTContainer LHTracker Type where
    containedASTs (LHTracker {abstract_calls = abs_c, annotations = anns}) = containedASTs abs_c ++ containedASTs anns
    modifyContainedASTs f lht@(LHTracker {abstract_calls = abs_c, annotations = anns}) =
        lht {abstract_calls = modifyContainedASTs f abs_c, annotations = modifyContainedASTs f anns}

data LHRed con = LHRed con Config

instance Solver con => Reducer (LHRed con) LHTracker where
    redRules lhr@(LHRed solver config) s = do
        (r, s') <- reduce (lhReduce config) solver config s

        return $ (if r == RuleIdentity then Finished else InProgress, s', lhr)

limitByAccepted :: Int -> (LHLimitByAcceptedHalter, LHLimitByAcceptedOrderer)
limitByAccepted i = (LHLimitByAcceptedHalter i, LHLimitByAcceptedOrderer i)

-- LHLimitByAcceptedHalter and LHLimitByAcceptedOrderer should always be used
-- together.
-- LHLimitByAcceptedHalter is parameterized by a cutoff, `c`.
-- It allows execution of a state only if
--    (1) No counterexamples have been found
--    (2) The earliest the best (fewest abstracted functions) counterexample
--        was found was at reduction step n, and the state has taken fewer
--        than c + n steps
-- If either of these is violated, we switch to a new state.
-- However, if we find a better (fewer abstracted functions) counterexamples
-- with a higher, n, we want to be able to go back to that state.
--
-- For this reason, we rely on discardOnStart to discard states that have taken
-- too many steps.  Because the Orderer always chooses the State that has taken the
-- least steps, we only restart a State with too many steps once EVERY state has too
-- many steps.

-- | Halt if we go `n` steps past another, already accepted state 
data LHLimitByAcceptedHalter = LHLimitByAcceptedHalter Int

instance Halter LHLimitByAcceptedHalter (Maybe Int) LHTracker where
    initHalt _ _ _ = Nothing

    -- If we start trying to execute a state with more than the maximal number
    -- of rules applied, we throw it away.
    discardOnStart (LHLimitByAcceptedHalter co) (Just v) _ s = num_steps s > v + co
    discardOnStart _ Nothing _ _ = False

    -- Find all accepted states with the (current) minimal number of abstracted functions
    -- Then, get the minimal number of steps taken by one of those states
    updatePerStateHalt _ _ (Processed { accepted = []}) _ = Nothing
    updatePerStateHalt _ _ (Processed { accepted = acc@(_:_)}) _ =
        Just . minimum . map num_steps
            $ allMin (length . abstract_calls . track) acc
    
    stopRed _ Nothing _ _ = Continue
    stopRed (LHLimitByAcceptedHalter co) (Just nAcc) _ s =
        if num_steps s > nAcc + co then Switch else Continue
    
    stepHalter _ hv _ _ = hv

-- | Runs the state that had the fewest number of rules applied.
data LHLimitByAcceptedOrderer = LHLimitByAcceptedOrderer Int
 
instance Orderer LHLimitByAcceptedOrderer () Int LHTracker where
    initPerStateOrder _ _ _ = ()

    orderStates _ _ = num_steps

    updateSelected _ _ _ _ = ()


allMin :: Ord b => (a -> b) -> [a] -> [a]
allMin f xs =
    let
        minT = minimum $ map f xs
    in
    filter (\s -> minT == (f s)) xs

-- | Halt if we abstract more calls than some other already accepted state
data LHAbsHalter = LHAbsHalter T.Text (Maybe T.Text) ExprEnv

instance Halter LHAbsHalter Int LHTracker where
    -- We initialize the maximal number of abstracted variables,
    -- to the number of variables in the entry function
    initHalt (LHAbsHalter entry modn eenv) _ _ =
        let 
            fe = case E.occLookup entry modn eenv of
                Just e -> e
                Nothing -> error "initOrder: Bad function passed"
        in
        initialTrack eenv fe

    updatePerStateHalt _ ii (Processed {accepted = acc}) _ = minimum $ ii:map (length . abstract_calls . track) acc

    stopRed _ hv _ s = if length (abstract_calls $ track s) > hv then Discard else Continue

    stepHalter _ hv _ _ = hv
