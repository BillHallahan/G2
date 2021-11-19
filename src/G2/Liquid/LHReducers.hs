{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

module G2.Liquid.LHReducers ( LHRed (..)
                            , AllCallsRed (..)
                            , RedArbErrors (..)
                            , NonRedAbstractReturns (..)

                            , LHAcceptIfViolatedHalter (..)
                            , LHSWHNFHalter (..)
                            , LHLimitByAcceptedOrderer (..)
                            , LHLimitByAcceptedHalter
                            , LHLimitByAcceptedOrderer
                            , LHAbsHalter (..)
                            , LHMaxOutputsHalter (..)
                            , LHMaxOutputsButTryHalter (..)
                            , LHLimitSameAbstractedHalter (..)
                            , SearchedBelowHalter (..)
                            , LHLeastAbstracted (..)
                            , LHTracker (..)

                            , lhTimerHalter

                            , abstractCallsNum
                            , minAbstractCalls

                            , lhReduce
                            , initialTrack

                            , limitByAccepted) where

import G2.Execution.NormalForms
import G2.Execution.Reducer
import G2.Execution.Rules
import G2.Language
import qualified G2.Language.Stack as Stck
import qualified G2.Language.ExprEnv as E
import G2.Liquid.Annotations
import G2.Liquid.Helpers
import G2.Liquid.SpecialAsserts

import Data.Foldable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S
import Data.List
import Data.List.Extra
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid hiding ((<>))
import Data.Ord
import Data.Semigroup
import qualified Data.Text as T
import Data.Time.Clock

import Debug.Trace
import G2.Lib.Printers

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
                           , annotations :: AnnotMap

                           , all_calls :: [FuncCall]} deriving (Eq, Show)

minAbstractCalls :: [State LHTracker] -> Int
minAbstractCalls xs =
    minimum $ 10000000000:mapMaybe (\s -> case true_assert s of
                                            True -> Just $ abstractCallsNum s
                                            False -> Nothing ) xs

abstractCallsNum :: State LHTracker -> Int
abstractCallsNum = length . abstract_calls . track

instance Named LHTracker where
    names (LHTracker {abstract_calls = abs_c, last_var = n, annotations = anns, all_calls = ac}) = 
        names abs_c <> names n <> names anns <> names ac
    
    rename old new (LHTracker {abstract_calls = abs_c, last_var = n, annotations = anns, all_calls = ac}) =
        LHTracker { abstract_calls = rename old new abs_c
                  , last_var = rename old new n
                  , annotations = rename old new anns
                  , all_calls = rename old new ac }
    
    renames hm (LHTracker {abstract_calls = abs_c, last_var = n, annotations = anns, all_calls = ac}) =
        LHTracker { abstract_calls = renames hm abs_c
                  , last_var = renames hm n
                  , annotations = renames hm anns
                  , all_calls = renames hm ac }

instance ASTContainer LHTracker Expr where
    containedASTs (LHTracker {abstract_calls = abs_c, annotations = anns, all_calls = ac}) =
        containedASTs abs_c ++ containedASTs anns ++ containedASTs ac
    modifyContainedASTs f lht@(LHTracker {abstract_calls = abs_c, annotations = anns, all_calls = ac}) =
        lht { abstract_calls = modifyContainedASTs f abs_c
            , annotations = modifyContainedASTs f anns
            , all_calls = modifyContainedASTs f ac}

instance ASTContainer LHTracker Type where
    containedASTs (LHTracker {abstract_calls = abs_c, annotations = anns, all_calls = ac}) =
        containedASTs abs_c ++ containedASTs anns ++ containedASTs ac
    modifyContainedASTs f lht@(LHTracker {abstract_calls = abs_c, annotations = anns, all_calls = ac}) =
        lht {abstract_calls = modifyContainedASTs f abs_c
            , annotations = modifyContainedASTs f anns
            , all_calls = modifyContainedASTs f ac }

data LHRed = LHRed Name

instance Reducer LHRed () LHTracker where
    initReducer _ _ = ()

    redRules lhr@(LHRed cfn) _ s b = do
        case lhReduce cfn s of
            Just (_, s') -> 
                return $ ( InProgress
                         , zip s' (repeat ()), b, lhr)
            Nothing -> return (Finished, [(s, ())], b, lhr)

data AllCallsRed  = AllCallsRed

instance Reducer AllCallsRed () LHTracker where
    initReducer _ _ = ()

    redRules lhr _ s@(State { curr_expr = CurrExpr Evaluate (Assert (Just fc) _ _) }) b =
        let
            lht = (track s) { all_calls = fc:all_calls (track s) }
        in
        return $ (Finished, [(s { track = lht } , ())], b, lhr)
    redRules lhr _ s b = return $ (Finished, [(s, ())], b, lhr)

data RedArbErrors = RedArbErrors

instance Reducer RedArbErrors () t where
    initReducer _ _ = ()

    redRules r _ s@(State { curr_expr = CurrExpr er (Tick tick (Let [(_, Type t)] _)) }) b 
        | tick == arbErrorTickish =
            let
                (arb, _) = arbValue t (type_env s) (arb_value_gen b)
            in
            return (InProgress, [(s { curr_expr = CurrExpr er arb }, ())], b, r)
    redRules r _ s b = return (Finished, [(s, ())], b, r)

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

    updatePerStateHalt _ ii (Processed {accepted = acc}) _ =
        minimum $ ii:mapMaybe (\s -> case true_assert s of
                                        True -> Just . length . abstract_calls . track $ s
                                        False -> Nothing) acc

    stopRed _ hv pr s =
        return $ if length (abstract_calls $ track s) > hv
            then Discard
            else Continue

    stepHalter _ hv _ _ _ = hv

data LHMaxOutputsHalter = LHMaxOutputsHalter Int

instance Halter LHMaxOutputsHalter Int LHTracker where
    initHalt (LHMaxOutputsHalter m) _ = m

    updatePerStateHalt _ hv _ _ = hv

    stopRed _ _ _ _ = return Continue

    discardOnStart _ m (Processed { accepted = acc }) _ = length acc' >= m
        where
            min_abs = minAbstractCalls acc
            acc' = filter (\s -> abstractCallsNum s == min_abs) acc

    stepHalter _ hv _ _ _ = hv

data LHMaxOutputsButTryHalter =
    LHMaxOutputsButTryHalter { max_out :: Int -- ^ The maximal number of states to output
                             , try_at_least :: Int -- ^ The number of states with less abstracted
                                                   -- functions to consider, before giving up
                             }

instance Halter LHMaxOutputsButTryHalter () LHTracker where
    initHalt _ _ = ()

    updatePerStateHalt _ hv _ _ = hv

    stopRed _ _ _ _ = return Continue

    discardOnStart (LHMaxOutputsButTryHalter m tal) _
                   (Processed { accepted = acc, discarded = dis }) s =
        length acc' >= m 
            && ( abstractCallsNum s >= m || length dis' >= tal || min_abs == 0 )
        where
            min_abs = minAbstractCalls acc
            acc' = filter (\s -> abstractCallsNum s == min_abs) acc

            dis' = filter (\s -> abstractCallsNum s < min_abs) dis

    stepHalter _ hv _ _ _ = hv

data LHLimitSameAbstractedHalter =
    LHLimitSameAbstractedHalter Int

instance Halter LHLimitSameAbstractedHalter () LHTracker where
    initHalt _ _ = ()

    updatePerStateHalt _ hv _ _ = hv

    stopRed _ _ _ _ = return Continue

    discardOnStart (LHLimitSameAbstractedHalter m) _ (Processed { accepted = acc }) s =
        M.findWithDefault 0 s_abst abst_count >= m
        where
            s_abst = S.fromList . map funcName . abstract_calls . track $ s

            absts = map (S.fromList . map funcName . abstract_calls . track) acc
            abst_count = foldr (M.alter (Just . maybe 0 (+ 1))) M.empty absts 

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

data LHTimerHalter = LHTimerHalter { lh_init_time :: UTCTime
                                   , lh_max_seconds :: NominalDiffTime
                                   , lh_check_every :: Int }

lhTimerHalter :: NominalDiffTime -> IO LHTimerHalter
lhTimerHalter ms = do
    curr <- getCurrentTime
    return LHTimerHalter { lh_init_time = curr, lh_max_seconds = ms, lh_check_every = 10 }

instance Halter LHTimerHalter Int t where
    initHalt _ _ = 0
    updatePerStateHalt _ _ _ _ = 0

    stopRed tr@(LHTimerHalter { lh_init_time = it
                              , lh_max_seconds = ms })
            v (Processed { accepted = acc }) s
        | v == 0
        , any true_assert acc = do
            curr <- getCurrentTime
            let diff = diffUTCTime curr it

            if diff > ms
                then return Discard
                else return Continue
        | otherwise = return Continue

    stepHalter (LHTimerHalter { lh_check_every = ce }) v _ _ _
        | v >= ce = 0
        | otherwise = v + 1

-- | Tries to consider the same number of states with each abstracted functions
data LHLeastAbstracted ord = LHLeastAbstracted (S.HashSet Name) ord

instance (Orderer ord sov b LHTracker, Show b) => Orderer (LHLeastAbstracted ord) sov (Maybe Name, b) LHTracker where
    initPerStateOrder (LHLeastAbstracted _ ord) = initPerStateOrder ord

    orderStates (LHLeastAbstracted ns ord) sov pr s =
        let
            (b, ord') = orderStates ord sov pr s
            fns = fmap funcName . listToMaybe . abstract_calls . track $ s
        in
        ((fns, b), LHLeastAbstracted ns ord')

    updateSelected (LHLeastAbstracted _ ord) = updateSelected ord

    stepOrderer (LHLeastAbstracted _ ord) = stepOrderer ord

    getState (LHLeastAbstracted cf_func ord) pr m =
        let
            abs_f = map (fmap funcName)
                  . map (\s -> case abstract_calls . track $ s of
                            (n:_) -> Just n
                            _ -> Nothing)
                  $ accepted pr ++ discarded pr

            num_abs = S.map (\n -> (n, length $ filter ((==) n) abs_f))
                    . S.insert Nothing
                    $ S.map Just cf_func

            min_func = map fst . sortBy (comparing snd) $ S.toList num_abs

            ms = filter (not . M.null . snd)
               $ map (\n -> (n, M.filterWithKey (\(n', _) _ -> n == n') m)) min_func
        in
        case ms of
            (n, m'):_ 
                | Just (b, s) <- getState ord pr $ M.mapKeys snd m' ->
                   Just ((n, b), s)
            _ -> Nothing

-- | Reduces any non-SWHNF values being returned by an abstracted function
data NonRedAbstractReturns = NonRedAbstractReturns

instance Reducer NonRedAbstractReturns () LHTracker where
    initReducer _ _ = ()

    redRules nrpr _  s@(State { expr_env = eenv
                              , curr_expr = cexpr
                              , exec_stack = stck
                              , track = LHTracker { abstract_calls = afs }
                              , model = m
                              , true_assert = True })
                      b@(Bindings { deepseq_walkers = ds})
        | Just af <- firstJust (absRetToRed eenv ds) afs = do
            let stck' = Stck.push (CurrExprFrame NoAction cexpr) stck
                cexpr' = CurrExpr Evaluate af

            let s' = s { curr_expr = cexpr'
                       , exec_stack = stck'
                       }

            return (InProgress, [(s', ())], b, nrpr)
        | otherwise = do
            return (Finished, [(s, ())], b, nrpr)
    redRules nrpr _ s b = return (Finished, [(s, ())], b, nrpr)

absRetToRed :: ExprEnv -> Walkers -> FuncCall -> Maybe Expr
absRetToRed eenv ds (FuncCall { returns = r })
    | not . normalForm eenv $ r
    , Just strict_e <- mkStrict_maybe ds r =
        Just $ fillLHDictArgs ds strict_e 
    | otherwise = Nothing

-- | Accepts a state when it is in SWHNF, true_assert is true,
-- and all abstracted functions have reduced returns.
-- Discards it if in SWHNF and true_assert is false
data LHAcceptIfViolatedHalter = LHAcceptIfViolatedHalter

instance Halter LHAcceptIfViolatedHalter () LHTracker where
    initHalt _ _ = ()
    updatePerStateHalt _ _ _ _ = ()
    stopRed _ _ _ s =
        let
            eenv = expr_env s
            abs_calls = abstract_calls (track s)
        in
        case isExecValueForm s of
            True 
                | true_assert s
                , all (normalForm eenv . returns) abs_calls -> return Accept
                | true_assert s -> return Continue
                | otherwise -> return Discard
            False -> return Continue
    stepHalter _ _ _ _ _ = ()

data LHSWHNFHalter = LHSWHNFHalter

instance Halter LHSWHNFHalter () LHTracker where
    initHalt _ _ = ()
    updatePerStateHalt _ _ _ _ = ()
    stopRed _ _ _ s =
        let
            eenv = expr_env s
            abs_calls = abstract_calls (track s)
        in
        case isExecValueForm s  && all (normalForm eenv . returns) abs_calls of
            True -> return Accept
            False -> return Continue
    stepHalter _ _ _ _ _ = ()


