{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

module G2.Liquid.LHReducers ( lhRed
                            , allCallsRed
                            , higherOrderCallsRed
                            , redArbErrors
                            , nonRedAbstractReturnsRed

                            , lhAcceptIfViolatedHalter
                            , lhSWHNFHalter
                            , lhLimitByAcceptedOrderer
                            , lhLimitByAcceptedHalter
                            , lhAbsHalter
                            , lhMaxOutputsHalter
                            , LHTracker (..)

                            , lhStdTimerHalter
                            , lhTimerHalter

                            , abstractCallsNum
                            , minAbstractCalls

                            , lhReduce
                            , initialTrack) where

import G2.Execution.NormalForms
import G2.Execution.Reducer
import G2.Execution.Rules
import G2.Language
import qualified G2.Language.Stack as Stck
import qualified G2.Language.ExprEnv as E
import G2.Liquid.Annotations
import G2.Liquid.Conversion
import G2.Liquid.Helpers
import G2.Liquid.SpecialAsserts

import Control.Monad.IO.Class 
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
initialTrack eenv (Case e _ _ a) = initialTrack eenv e + (getMax $ evalContainedASTs (Max . initialTrack eenv) a)
initialTrack eenv (Cast e _) = initialTrack eenv e
initialTrack eenv (Assume _ _ e) = initialTrack eenv e
initialTrack eenv (Assert _ _ e) = initialTrack eenv e
initialTrack _ _ = 0

data LHTracker = LHTracker { abstract_calls :: [FuncCall]
                           , last_var :: Maybe Name
                           , annotations :: AnnotMap

                           , all_calls :: [FuncCall]
                           , higher_order_calls :: [FuncCall] } deriving (Eq, Show)

minAbstractCalls :: [State LHTracker] -> Int
minAbstractCalls xs =
    minimum $ 10000000000:mapMaybe (\s -> case true_assert s of
                                            True -> Just $ abstractCallsNum s
                                            False -> Nothing ) xs

abstractCallsNum :: State LHTracker -> Int
abstractCallsNum = length . abstract_calls . track

instance Named LHTracker where
    names (LHTracker {abstract_calls = abs_c, last_var = n, annotations = anns, all_calls = ac, higher_order_calls = hc}) = 
        names abs_c <> names n <> names anns <> names ac <> names hc
    
    rename old new (LHTracker {abstract_calls = abs_c, last_var = n, annotations = anns, all_calls = ac, higher_order_calls = hc}) =
        LHTracker { abstract_calls = rename old new abs_c
                  , last_var = rename old new n
                  , annotations = rename old new anns
                  , all_calls = rename old new ac
                  , higher_order_calls = rename old new hc }
    
    renames hm (LHTracker {abstract_calls = abs_c, last_var = n, annotations = anns, all_calls = ac, higher_order_calls = hc}) =
        LHTracker { abstract_calls = renames hm abs_c
                  , last_var = renames hm n
                  , annotations = renames hm anns
                  , all_calls = renames hm ac
                  , higher_order_calls = renames hm hc }

instance ASTContainer LHTracker Expr where
    containedASTs (LHTracker {abstract_calls = abs_c, annotations = anns, all_calls = ac, higher_order_calls = hc}) =
        containedASTs abs_c ++ containedASTs anns ++ containedASTs ac ++ containedASTs hc
    modifyContainedASTs f lht@(LHTracker {abstract_calls = abs_c, annotations = anns, all_calls = ac, higher_order_calls = hc}) =
        lht { abstract_calls = modifyContainedASTs f abs_c
            , annotations = modifyContainedASTs f anns
            , all_calls = modifyContainedASTs f ac
            , higher_order_calls = modifyContainedASTs f hc}

instance ASTContainer LHTracker Type where
    containedASTs (LHTracker {abstract_calls = abs_c, annotations = anns, all_calls = ac, higher_order_calls = hc}) =
        containedASTs abs_c ++ containedASTs anns ++ containedASTs ac ++ containedASTs hc
    modifyContainedASTs f lht@(LHTracker {abstract_calls = abs_c, annotations = anns, all_calls = ac, higher_order_calls = hc}) =
        lht {abstract_calls = modifyContainedASTs f abs_c
            , annotations = modifyContainedASTs f anns
            , all_calls = modifyContainedASTs f ac
            , higher_order_calls = modifyContainedASTs f hc }

{-# INLINE lhRed #-}
lhRed :: Monad m => Name -> Reducer m () LHTracker
lhRed cfn = mkSimpleReducer (const ()) rr
    where
        rr _ s b = do
            case lhReduce cfn s of
                Just (_, s') -> 
                    return $ ( InProgress
                             , zip s' (repeat ()), b)
                Nothing -> return (Finished, [(s, ())], b)

{-# INLINE allCallsRed #-}
allCallsRed :: Monad m => Reducer m () LHTracker
allCallsRed = mkSimpleReducer (const ()) rr
    where
        rr _ s@(State { curr_expr = CurrExpr Evaluate (Assert (Just fc) _ _) }) b =
            let
                lht = (track s) { all_calls = fc:all_calls (track s) }
            in
            return $ (Finished, [(s { track = lht } , ())], b)
        rr _ s b = return $ (Finished, [(s, ())], b)

{-# INLINE higherOrderCallsRed #-}
higherOrderCallsRed :: Monad m => Reducer m () LHTracker
higherOrderCallsRed = mkSimpleReducer (const ()) rr
    where
        rr _ s@(State { curr_expr = CurrExpr Evaluate (Tick (NamedLoc nl) (Assume (Just fc) _ _)) }) b | nl == higherOrderTickName=
            let
                lht = (track s) { higher_order_calls = fc:higher_order_calls (track s) }
            in
            return $ (Finished, [(s { track = lht } , ())], b)
        rr _ s@(State { curr_expr = CurrExpr Evaluate (Tick (NamedLoc nl) (Assume (Just fc) _ real_assert@(Assert _ _ _))) }) b | nl == higherOrderTickName=
            let
                lht = (track s) { higher_order_calls = fc:higher_order_calls (track s) }
            in
            return $ (Finished, [(s { curr_expr = CurrExpr Evaluate real_assert
                                    , track = lht } , ())], b)
        rr _ s b = return $ (Finished, [(s, ())], b)

{-# INLINE redArbErrors #-}
redArbErrors :: Monad m => Reducer m () t
redArbErrors = mkSimpleReducer (const ()) rr
    where
        rr _ s@(State { curr_expr = CurrExpr er (Tick tick (Let [(_, Type t)] _)) }) b 
            | tick == arbErrorTickish =
                let
                    (arb, _) = arbValue t (type_env s) (arb_value_gen b)
                in
                return (InProgress, [(s { curr_expr = CurrExpr er arb }, ())], b)
        rr _ s b = return (Finished, [(s, ())], b)

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
lhLimitByAcceptedHalter :: Monad m => Int -> Halter m (Maybe Int) LHTracker
lhLimitByAcceptedHalter co =
    (mkSimpleHalter (const Nothing) update stop (\hv _ _ _ -> hv)) { discardOnStart = discard }
    where
        -- If we start trying to execute a state with more than the maximal number
        -- of rules applied, we throw it away.
        discard (Just v) _ s = num_steps s > v + co
        discard Nothing _ _ = False

        -- Find all accepted states with the (current) minimal number of abstracted functions
        -- Then, get the minimal number of steps taken by one of those states
        update _ (Processed { accepted = []}) _ = Nothing
        update _ (Processed { accepted = acc@(_:_)}) _ =
            Just . minimum . map num_steps
                $ allMin (length . abstract_calls . track) acc
        
        stop Nothing _ _ = return Continue
        stop (Just nAcc) _ s =
            return $ if num_steps s > nAcc + co then Switch else Continue

-- | Runs the state that had the fewest number of rules applied.
lhLimitByAcceptedOrderer :: Orderer () Int t
lhLimitByAcceptedOrderer = mkSimpleOrderer (const ()) (\_ _ -> num_steps) (\_ _ _ -> ())

allMin :: Ord b => (a -> b) -> [a] -> [a]
allMin f xs =
    let
        minT = minimum $ map f xs
    in
    filter (\s -> minT == (f s)) xs

-- | Halt if we abstract more calls than some other already accepted state
lhAbsHalter :: Monad m => T.Text -> Maybe T.Text -> ExprEnv -> Halter m Int LHTracker
lhAbsHalter entry modn eenv = mkSimpleHalter initial update stop step
    where
        -- We initialize the maximal number of abstracted variables,
        -- to the number of variables in the entry function
        initial _ =
            let 
                fe = case E.occLookup entry modn eenv of
                    Just e -> e
                    Nothing -> error $ "initOrder: Bad function passed\n" ++ show entry ++ " " ++ show modn
            in
            initialTrack eenv fe

        update ii (Processed {accepted = acc}) _ =
            minimum $ ii:mapMaybe (\s -> case true_assert s of
                                            True -> Just . length . abstract_calls . track $ s
                                            False -> Nothing) acc

        stop hv _ s =
            return $ if length (abstract_calls $ track s) > hv
                then Discard
                else Continue

        step hv _ _ _ = hv

lhMaxOutputsHalter :: Monad m => Int -> Halter m Int LHTracker
lhMaxOutputsHalter mx = (mkSimpleHalter
                            (const mx)
                            (\hv _ _ -> hv)
                            (\_ _ _ -> return Continue)
                            (\hv _ _ _ -> hv)) { discardOnStart = discard}
    where
        discard m (Processed { accepted = acc }) _ = length acc' >= m
            where
                min_abs = minAbstractCalls acc
                acc' = filter (\s -> abstractCallsNum s == min_abs) acc

lhStdTimerHalter :: (MonadIO m, MonadIO m_run) => NominalDiffTime -> m (Halter m_run Int t)
lhStdTimerHalter ms = lhTimerHalter ms 10

lhTimerHalter :: (MonadIO m, MonadIO m_run) => NominalDiffTime -> Int -> m (Halter m_run Int t)
lhTimerHalter ms ce = do
    curr <- liftIO $ getCurrentTime
    return $ mkSimpleHalter (const 0)
                            (\_ _ _ -> 0)
                            (stop curr)
                            step
    where
        stop it v (Processed { accepted = acc }) _
            | v == 0
            , any true_assert acc = do
                curr <- liftIO $ getCurrentTime
                let t_diff = diffUTCTime curr it

                if t_diff > ms
                    then return Discard
                    else return Continue
            | otherwise = return Continue

        step v _ _ _
            | v >= ce = 0
            | otherwise = v + 1

-- | Reduces any non-SWHNF values being returned by an abstracted function
{-# INLINE nonRedAbstractReturnsRed #-}
nonRedAbstractReturnsRed :: Monad m => Reducer m () LHTracker
nonRedAbstractReturnsRed =
    mkSimpleReducer (const ())
                    nonRedAbstractReturnsRedStep

nonRedAbstractReturnsRedStep :: Monad m => RedRules m () LHTracker
nonRedAbstractReturnsRedStep _ 
                  s@(State { expr_env = eenv
                           , curr_expr = cexpr
                           , exec_stack = stck
                           , track = LHTracker { abstract_calls = afs }
                           , true_assert = True })
                  b@(Bindings { deepseq_walkers = ds})
    | Just af <- firstJust (absRetToRed eenv ds) afs = do
        let stck' = Stck.push (CurrExprFrame NoAction cexpr) stck
            cexpr' = CurrExpr Evaluate af

        let s' = s { curr_expr = cexpr'
                   , exec_stack = stck'
                   }

        return (InProgress, [(s', ())], b)
    | otherwise = do
        return (Finished, [(s, ())], b)
nonRedAbstractReturnsRedStep _ s b = return (Finished, [(s, ())], b)

absRetToRed :: ExprEnv -> Walkers -> FuncCall -> Maybe Expr
absRetToRed eenv ds (FuncCall { returns = r })
    | not . normalForm eenv $ r
    , Just strict_e <- mkStrict_maybe ds r =
        Just $ fillLHDictArgs ds strict_e 
    | otherwise = Nothing

-- | Accepts a state when it is in SWHNF, true_assert is true,
-- and all abstracted functions have reduced returns.
-- Discards it if in SWHNF and true_assert is false
lhAcceptIfViolatedHalter :: Monad m => Halter m () LHTracker
lhAcceptIfViolatedHalter = mkSimpleHalter (const ()) (\_ _ _ -> ()) stop (\_ _ _ _ -> ())
    where
        stop _ _ s =
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

lhSWHNFHalter :: Monad m => Halter m () LHTracker
lhSWHNFHalter = mkSimpleHalter (const ()) (\_ _ _ -> ()) stop (\_ _ _ _ -> ())
    where
        stop _ _ s =
            let
                eenv = expr_env s
                abs_calls = abstract_calls (track s)
            in
            case isExecValueForm s  && all (normalForm eenv . returns) abs_calls of
                True -> return Accept
                False -> return Continue

