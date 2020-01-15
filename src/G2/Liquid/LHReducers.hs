{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module G2.Liquid.LHReducers ( LHRed (..)
                            , LHLimitByAcceptedOrderer (..)
                            , LHLimitByAcceptedHalter
                            , LHLimitByAcceptedOrderer
                            , LHAbsHalter (..)
                            , LHMaxOutputsHalter (..)
                            , SearchedBelowHalter (..)
                            , LHTracker (..)

                            , abstractCallsNum
                            , minAbstractCalls

                            , lhReduce
                            , initialTrack

                            , limitByAccepted) where

import G2.Execution.Reducer
import G2.Execution.Rules
import G2.Language
import qualified G2.Language.Stack as Stck
import qualified G2.Language.ExprEnv as E
import G2.Liquid.Annotations

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
lhReduce :: Name -> State LHTracker -> Maybe (Rule, [State LHTracker])
lhReduce cfn s@(State { curr_expr = CurrExpr Evaluate (Tick (NamedLoc tn) e@(Assume (Just fc) _ _))
                      , track = tr@(LHTracker { abstract_calls = abs_c })
                      , exec_stack = stck})
                    | cfn == tn =
                        let
                            stck' = if arguments fc == [] then Stck.filter (\f -> f /= UpdateFrame (funcName fc)) stck else stck
                        in
                        Just ( RuleOther
                             , [s { curr_expr = CurrExpr Evaluate e
                                  , track = tr { abstract_calls = fc:abs_c }
                                  , exec_stack = stck' }])
                    | otherwise = Nothing

lhReduce _ _ = Nothing

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
initialTrack eenv (Assume _ _ e) = initialTrack eenv e
initialTrack eenv (Assert _ _ e) = initialTrack eenv e
initialTrack _ _ = 0

data LHTracker = LHTracker { abstract_calls :: [FuncCall]
                           , last_var :: Maybe Name
                           , annotations :: AnnotMap } deriving (Eq, Show)

minAbstractCalls :: [State LHTracker] -> Int
minAbstractCalls xs = minimum $ 10000000000:fmap abstractCallsNum xs

abstractCallsNum :: State LHTracker -> Int
abstractCallsNum = length . abstract_calls . track

instance Named LHTracker where
    names (LHTracker {abstract_calls = abs_c, last_var = n, annotations = anns}) = 
        names abs_c ++ names n ++ names anns
    
    rename old new (LHTracker {abstract_calls = abs_c, last_var = n, annotations = anns}) =
        LHTracker { abstract_calls = rename old new abs_c
                  , last_var = rename old new n
                  , annotations = rename old new anns }
    
    renames hm (LHTracker {abstract_calls = abs_c, last_var = n, annotations = anns}) =
        LHTracker { abstract_calls = renames hm abs_c
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

data LHRed = LHRed Name

instance Reducer LHRed () LHTracker where
    initReducer _ _ = ()

    redRules lhr@(LHRed cfn) _ s b = do
        case lhReduce cfn s of
            Just (_, s') -> 
                return $ ( InProgress
                         , zip s' (repeat ()), b, lhr)
            Nothing -> return (Finished, [(s, ())], b, lhr)

limitByAccepted :: Int -> (LHLimitByAcceptedHalter, LHLimitByAcceptedOrderer)
limitByAccepted i = (LHLimitByAcceptedHalter i, LHLimitByAcceptedOrderer)

-- LHLimitByAcceptedHalter should always be used
-- with LHLimitByAcceptedOrderer.
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
    initHalt _ _ = Nothing

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
    
    stopRed _ Nothing _ _ = return Continue
    stopRed (LHLimitByAcceptedHalter co) (Just nAcc) _ s =
        return $ if num_steps s > nAcc + co then Switch else Continue
    
    stepHalter _ hv _ _ _ = hv

-- | Runs the state that had the fewest number of rules applied.
data LHLimitByAcceptedOrderer = LHLimitByAcceptedOrderer
 
instance Orderer LHLimitByAcceptedOrderer () Int LHTracker where
    initPerStateOrder _ _ = ()

    orderStates or _ _ s = (num_steps s, or)

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
    initHalt (LHAbsHalter entry modn eenv) _ =
        let 
            fe = case E.occLookup entry modn eenv of
                Just e -> e
                Nothing -> error $ "initOrder: Bad function passed\n" ++ show entry ++ " " ++ show modn
        in
        initialTrack eenv fe

    updatePerStateHalt _ ii (Processed {accepted = acc}) _ = minimum $ ii:map (length . abstract_calls . track) acc

    stopRed _ hv pr s =
        return $ if length (abstract_calls $ track s) > hv
            then trace ("accepted " ++ show (length (accepted pr)) ++ " discarded "
                            ++ show (length (discarded pr)) ++ " discarded no abs " ++ show (length (filter (\s -> abstractCallsNum s == 0) $ discarded pr))) Discard
            else Continue

    stepHalter _ hv _ _ _ = hv

data LHMaxOutputsHalter = LHMaxOutputsHalter Int

instance Halter LHMaxOutputsHalter Int LHTracker where
    initHalt (LHMaxOutputsHalter m) _ = m

    updatePerStateHalt _ hv _ _ = hv

    stopRed _ m (Processed { accepted = acc }) _
        | length acc' >= m = return Discard
        | otherwise = return Continue
        where
            min_abs = minAbstractCalls acc
            acc' = filter (\s -> abstractCallsNum s == min_abs) acc

    stepHalter _ hv _ _ _ = hv

-- | Suppose that the minimal number of abstracted calls in an accepted state is m.
-- This Halter discards all unprocessed states after finding at least found_at_least states with
-- exactly m abstracted calls, if either:
-- (1) at least discarded_at_least states with fewer than m accepted calls have been discarded.
-- (2) at most discarded_at_most states with fewer than m accepted calls have been discarded.
data SearchedBelowHalter = SearchedBelowHalter { found_at_least :: Int
                                               , discarded_at_least :: Int
                                               , discarded_at_most :: Int }

data SBInfo = SBInfo { accepted_lt_num :: Int
                     , discarded_lt_num :: Int }

instance Halter SearchedBelowHalter SBInfo LHTracker where
    initHalt _ _ = SBInfo { accepted_lt_num = 0, discarded_lt_num = 0}

    updatePerStateHalt _ hv (Processed { accepted = acc, discarded = dis }) _ =
        SBInfo { accepted_lt_num = length acc'
               , discarded_lt_num = length dis_less_than_min }
        where
            min_abs = minAbstractCalls acc
            
            acc' = filter (\acc_s -> abstractCallsNum acc_s == min_abs) acc

            dis_less_than_min = filter (\s -> abstractCallsNum s < min_abs || abstractCallsNum s == 0) dis

    stopRed sbh (SBInfo { accepted_lt_num = length_acc, discarded_lt_num = length_dis_ltm } ) (Processed { accepted = acc }) s
        | length_acc >= found_at_least sbh
        , length_dis_ltm >= discarded_at_least sbh = return Discard

        | length_acc >= 1
        , length_dis_ltm >= discarded_at_most sbh = return Discard

        | otherwise = return Continue
        where
            min_abs = minAbstractCalls acc
            
    stepHalter _ hv _ _ _ = hv
