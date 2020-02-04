{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module G2.Execution.Reducer ( Reducer (..)
                            , Halter (..)
                            , Orderer (..)
                            , MinOrderer (..)
                            , ToOrderer (..)

                            , Processed (..)
                            , mapProcessed

                            , ReducerRes (..)
                            , HaltC (..)

                            , SomeReducer (..)
                            , SomeHalter (..)
                            , SomeOrderer (..)

                            -- Reducers
                            , RCombiner (..)
                            , StdRed (..)
                            , NonRedPCRed (..)
                            , TaggerRed (..)
                            , Logger (..)

                            , (<~)
                            , (<~?)
                            , (<~|)

                            -- Halters
                            , AcceptHalter (..)
                            , HCombiner (..)
                            , ZeroHalter (..)
                            , DiscardIfAcceptedTag (..)
                            , MaxOutputsHalter (..)
                            , SwitchEveryNHalter (..)
                            , BranchAdjSwitchEveryNHalter (..)
                            , RecursiveCutOff (..)
                            , VarLookupLimit (..)
                            , BranchAdjVarLookupLimit (..)

                            -- Orderers
                            , OCombiner (..)
                            , NextOrderer (..)
                            , PickLeastUsedOrderer (..)
                            , BucketSizeOrderer (..)
                            , CaseCountOrderer (..)
                            , SymbolicADTOrderer (..)
                            , ADTHeightOrderer (..)
                            , IncrAfterN (..)

                            , runReducer 
                            , runReducerMerge ) where

import G2.Config.Config
import qualified G2.Language.ExprEnv as E
import G2.Execution.Rules
import qualified G2.Execution.WorkGraph as WG
import G2.Execution.LogZipper
import G2.Language
import qualified G2.Language.Monad as MD
import qualified G2.Language.Stack as Stck
import G2.Solver
import G2.Lib.Printers
import G2.Execution.StateMerging

import Data.Foldable
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM
import qualified Data.Map as M
import Data.Maybe
import qualified Data.List as L
import System.Directory

-- | Used when applying execution rules
-- Allows tracking extra information to control halting of rule application,
-- and to reorder states
-- see also, the Reducer, Halter, Orderer typeclasses
-- cases is used for logging states
data ExState rv hv sov t = ExState { state :: State t
                                   , reducer_val :: rv
                                   , halter_val :: hv
                                   , order_val :: sov
                                   }

-- | Keeps track of type a's that have either been accepted or dropped
data Processed a = Processed { accepted :: [a]
                             , discarded :: [a] }

mapProcessed :: (a -> b) -> Processed a -> Processed b
mapProcessed f pr = Processed { accepted = map f (accepted pr)
                              , discarded = map f (discarded pr)}

-- | Used by Reducers to indicate their progress reducing.
data ReducerRes = NoProgress | InProgress | Finished | Split | MergePoint | MaxDepth deriving (Eq, Ord, Show, Read)

progPrioritizer :: ReducerRes -> ReducerRes -> ReducerRes
progPrioritizer MaxDepth _ = MaxDepth
progPrioritizer _ MaxDepth = MaxDepth
progPrioritizer Split _ = Split
progPrioritizer _ Split = Split
progPrioritizer MergePoint _ = MergePoint
progPrioritizer _ MergePoint = MergePoint
progPrioritizer InProgress _ = InProgress
progPrioritizer _ InProgress = InProgress
progPrioritizer Finished _ = Finished
progPrioritizer _ Finished = Finished
progPrioritizer _ _ = NoProgress

-- | Used by members of the Halter typeclass to control whether to continue
-- evaluating the current State, or switch to evaluating a new state.
data HaltC = Discard -- ^ Switch to evaluating a new state, and reject the current state
           | Accept -- ^ Switch to evaluating a new state, and accept the current state
           | Switch -- ^ Switch to evaluating a new state, but continue evaluating the current state later
           | Continue -- ^ Continue evaluating the current State
           deriving (Eq, Ord, Show, Read)

-- | A Reducer is used to describe a set of Reduction Rules.
-- Reduction Rules take a State, and output new states.
-- The type parameter r is used to disambiguate between different producers.
-- To create a new reducer, define some new type, and use it as r. 
-- The reducer value, rv, can be used to track special, per Reducer, information.
class Reducer r rv t | r -> rv where
    -- | Initialized the reducer value
    initReducer :: r -> State t -> rv

    -- | Takes a State, and performs the appropriate Reduction Rule
    redRules :: r -> rv -> State t -> Bindings -> IO (ReducerRes, [(State t, rv)], Bindings, r) 
    
    -- | Gives an opportunity to update with all States and Reducer Val's,
    -- output by all Reducer's, visible
    -- Errors if the returned list is too short.
    {-# INLINE updateWithAll #-}
    updateWithAll :: r -> [(State t, rv)] -> [rv]
    updateWithAll _ = map snd 


-- | Determines when to stop evaluating a state
-- The type parameter h is used to disambiguate between different producers.
-- To create a new Halter, define some new type, and use it as h.
class Halter h hv t | h -> hv where
    -- | Initializes each state halter value
    initHalt :: h -> State t -> hv

    -- | Runs whenever we switch to evaluating a different state,
    -- to update the halter value of that new state
    updatePerStateHalt :: h -> hv -> Processed (State t) -> State t -> hv

    -- | Runs when we start execution on a state, immediately after
    -- `updatePerStateHalt`.  Allows a State to be discarded right
    -- before execution is about to (re-)begin.
    -- Return True if execution should proceed, False to discard
    discardOnStart :: h -> hv -> Processed (State t) -> State t -> Bool
    discardOnStart _ _ _ _ = False

    -- | Determines whether to continue reduction on the current state
    stopRed :: h -> hv -> Processed (State t) -> State t -> HaltC

    -- | Takes a state, and updates it's halter record field
    stepHalter :: h -> hv -> Processed (State t) -> [State t] -> State t -> hv

-- | Picks an order to evaluate the states, to allow prioritizing some over others 
-- The type parameter or is used to disambiguate between different producers.
-- To create a new reducer, define some new type, and use it as or.
class Ord b => Orderer or sov b t | or -> sov, or -> b where
    -- | Initializing the per state ordering value 
    initPerStateOrder :: or -> State t -> sov

    -- | Assigns each state some value of an ordered type, and then proceeds with execution on the
    -- state assigned the minimal value
    orderStates :: or -> sov -> State t -> b

    -- | Run on the selected state, to update it's sov field
    updateSelected :: or -> sov -> Processed (State t) -> State t -> sov

    -- | Run on the state at each step, to update it's sov field
    stepOrderer :: or -> sov -> Processed (State t) -> [State t] -> State t -> sov 
    stepOrderer _ sov _ _ _ = sov

    getState :: forall s . or -> Processed (State t) -> M.Map b s -> Maybe ((b, s), M.Map b s)
    getState _ _ = M.minViewWithKey

class Ord b => MinOrderer or sov b t | or -> sov, or -> b where
    -- | Initializing the per state ordering value 
    minInitPerStateOrder :: or -> State t -> sov

    -- | Assigns each state some value of an ordered type, and then proceeds with execution on the
    -- state assigned the minimal value
    minOrderStates :: or -> sov -> State t -> b

    -- | Run on the selected state, to update it's sov field
    minUpdateSelected :: or -> sov -> Processed (State t) -> State t -> sov

    -- | Run on the state at each step, to update it's sov field
    minStepOrderer :: or -> sov -> Processed (State t) -> [State t] -> State t -> sov 
    minStepOrderer _ sov _ _ _ = sov

newtype ToOrderer min_ord = ToOrderer min_ord

instance (MinOrderer min_ord sov b t, Ord b) => Orderer (ToOrderer min_ord) sov b t where
    initPerStateOrder (ToOrderer min_ord) = minInitPerStateOrder min_ord
    orderStates (ToOrderer min_ord) = minOrderStates min_ord
    updateSelected (ToOrderer min_ord) = minUpdateSelected min_ord
    stepOrderer (ToOrderer min_ord) = minStepOrderer min_ord
    getState _ _ = M.minViewWithKey

data SomeReducer t where
    SomeReducer :: forall r rv t . Reducer r rv t => r -> SomeReducer t

data SomeHalter t where
    SomeHalter :: forall h hv t . Halter h hv t => h -> SomeHalter t

data SomeOrderer t where
    SomeOrderer :: forall or sov b t . Orderer or sov b t => or -> SomeOrderer t

-- | Combines reducers in various ways
-- updateWithAll is called by all Reducers, regardless of which combinator is used
data RCombiner r1 r2 = r1 :<~ r2 -- ^ Apply r2, followed by r1.  Takes the leftmost update to r1
                     | r1 :<~? r2 -- ^ Apply r2, apply r1 only if r2 returns NoProgress
                     | r1 :<~| r2 -- ^ Apply r2, apply r1 only if r2 returns Finished
                     deriving (Eq, Show, Read)

-- We use RC to combine the reducer values for RCombiner
-- We should never define any other instance of Reducer with RC, or export it
-- because this could lead to undecidable instances
data RC a b = RC a b

instance (Reducer r1 rv1 t, Reducer r2 rv2 t) => Reducer (RCombiner r1 r2) (RC rv1 rv2) t where
    initReducer (r1 :<~ r2) s =
        let
            rv1 = initReducer r1 s
            rv2 = initReducer r2 s
        in
        RC rv1 rv2
    initReducer (r1 :<~? r2) s =
        let
            rv1 = initReducer r1 s
            rv2 = initReducer r2 s
        in
        RC rv1 rv2
    initReducer (r1 :<~| r2) s =
        let
            rv1 = initReducer r1 s
            rv2 = initReducer r2 s
        in
        RC rv1 rv2

    redRules (r1 :<~ r2) (RC rv1 rv2) s b = do
        (rr2, srv2, b', r2') <- redRules r2 rv2 s b
        (rr1, srv1, b'', r1') <- redRulesToStates r1 rv1 srv2 b'

        return (progPrioritizer rr1 rr2, srv1, b'', r1' :<~ r2')

    redRules (r1 :<~? r2) (RC rv1 rv2) s b = do
        (rr2, srv2, b', r2') <- redRules r2 rv2 s b
        let (s', rv2') = unzip srv2

        case rr2 of
            NoProgress -> do
                (rr1, ss, b'', r1') <- redRulesToStates r1 rv1 srv2 b'
                return (rr1, ss, b'', r1' :<~? r2')
            _ -> return (rr2, zip s' (map (uncurry RC) (zip (repeat rv1) rv2')), b', r1 :<~? r2')

    redRules (r1 :<~| r2) (RC rv1 rv2) s b = do
        (rr2, srv2, b', r2') <- redRules r2 rv2 s b
        let (s', rv2') = unzip srv2

        case rr2 of
            Finished -> do
                (rr1, ss, b'', r1') <- redRulesToStates r1 rv1 srv2 b'
                return (rr1, ss, b'', r1' :<~| r2')
            _ -> return (rr2, zip s' (map (uncurry RC) (zip (repeat rv1) rv2')), b', r1 :<~| r2')

    updateWithAll (r1 :<~ r2) = updateWithAllRC r1 r2
    updateWithAll (r1 :<~? r2) = updateWithAllRC r1 r2
    updateWithAll (r1 :<~| r2) = updateWithAllRC r1 r2

{-# INLINE updateWithAllRC #-}
updateWithAllRC :: (Reducer r1 rv1 t, Reducer r2 rv2 t) => r1 -> r2 -> [(State t, RC rv1 rv2)] -> [RC rv1 rv2]
updateWithAllRC r1 r2 srv =
    let
        srv1 = map (\(s, RC rv1 _) -> (s, rv1)) srv
        srv2 = map (\(s, RC _ rv2) -> (s, rv2)) srv

        rv1' = updateWithAll r1 srv1
        rv2' = updateWithAll r2 srv2
    in
    map (uncurry RC) $ zip rv1' rv2'

redRulesToStatesAux :: Reducer r rv t => r -> rv -> Bindings -> (State t, rv2) -> IO (Bindings, (ReducerRes, [(State t, RC rv rv2)], r))
redRulesToStatesAux r rv1 b (is, rv2) = do
        (rr_, is', b', r') <- redRules r rv1 is b
        return (b', (rr_, map (\(is'', rv1') -> (is'', RC rv1' rv2) ) is', r'))
    
redRulesToStates :: Reducer r rv t => r -> rv -> [(State t, rv2)] -> Bindings -> IO (ReducerRes, [(State t, RC rv rv2)], Bindings, r)
redRulesToStates r rv1 s b = do
    let redRulesToStatesAux' = redRulesToStatesAux r rv1
    (b', rs) <- MD.mapMAccumB redRulesToStatesAux' b s

    let (rr, s', r') = L.unzip3 rs

    let rf = foldr progPrioritizer NoProgress rr

    return $ (rf, concat s', b', head r')

{-# INLINE (<~) #-}
-- | Combines two @`SomeReducer`@s with a @`:<~`@
(<~) :: SomeReducer t -> SomeReducer t -> SomeReducer t
SomeReducer r1 <~ SomeReducer r2 = SomeReducer (r1 :<~ r2)

{-# INLINE (<~?) #-}
-- | Combines two @`SomeReducer`@s with a @`:<~?`@
(<~?) :: SomeReducer t -> SomeReducer t -> SomeReducer t
SomeReducer r1 <~? SomeReducer r2 = SomeReducer (r1 :<~? r2)

{-# INLINE (<~|) #-}
-- | Combines two @`SomeReducer`@s with a @`:<~|`@
(<~|) :: SomeReducer t -> SomeReducer t -> SomeReducer t
SomeReducer r1 <~| SomeReducer r2 = SomeReducer (r1 :<~| r2)

data StdRed solver simplifier = StdRed Sharing Merging solver simplifier

instance (Solver solver, Simplifier simplifier) => Reducer (StdRed solver simplifier) () t where
    initReducer _ _ = ()

    redRules stdr@(StdRed share mergeStates solver simplifier) _ s b = do
        (r, s', b') <- stdReduce share mergeStates solver simplifier s b
        let res = case r of
                    RuleHitMergePt -> MergePoint
                    RuleEvalCaseSym -> Split
                    RuleMaxDepth -> MaxDepth
                    RuleIdentity -> Finished
                    _ -> InProgress

        return (res, s', b', stdr)

-- | Removes and reduces the values in a State's non_red_path_conds field. 
data NonRedPCRed = NonRedPCRed

instance Reducer NonRedPCRed () t where
    initReducer _ _ = ()

    redRules nrpr _  s@(State { expr_env = eenv
                              , curr_expr = cexpr
                              , exec_stack = stck
                              , non_red_path_conds = nr:nrs
                              , symbolic_ids = si
                              , model = m })
                      b@(Bindings { higher_order_inst = inst }) = do
        let stck' = Stck.push (CurrExprFrame cexpr) stck

        let cexpr' = CurrExpr Evaluate nr

        let eenv_si_ces = substHigherOrder eenv m si inst cexpr'

        let s' = s { exec_stack = stck'
                   , non_red_path_conds = nrs
                   }
            xs = map (\(eenv', m', si', ce) -> (s' { expr_env = eenv'
                                                   , model = m'
                                                   , curr_expr = ce
                                                   , symbolic_ids = si' }, ())) eenv_si_ces

        return (InProgress, xs, b, nrpr)
    redRules nrpr _ s b = return (Finished, [(s, ())], b, nrpr)

-- [Higher-Order Model]
-- Substitutes all possible higher order functions for symbolic higher order functions.
-- We insert the substituted higher order function directly into the model, because, due
-- to the VAR-RED rule, the function name will (if the function is called) be lost during execution.
substHigherOrder :: ExprEnv -> Model -> SymbolicIds -> [Name] -> CurrExpr -> [(ExprEnv, Model, SymbolicIds, CurrExpr)]
substHigherOrder eenv m si ns ce =
    let
        is = mapMaybe (\n -> case E.lookup n eenv of
                                Just e -> Just $ Id n (typeOf e)
                                Nothing -> Nothing) ns

        higherOrd = filter (isTyFun . typeOf) . mapMaybe varId . symbVars eenv $ ce
        higherOrdSub = map (\v -> (v, mapMaybe (genSubstitutable v) is)) higherOrd
    in
    substHigherOrder' [(eenv, m, si, ce)] higherOrdSub
    where
        genSubstitutable v i
            | (True, bm) <- specializes M.empty (typeOf v )(typeOf i) =
                let
                    bnds = map idName $ leadingTyForAllBindings i
                    tys = mapMaybe (\b -> fmap Type $ M.lookup b bm) bnds
                in
                Just . mkApp $ Var i:tys
            | otherwise = Nothing

substHigherOrder' :: [(ExprEnv, Model, SymbolicIds, CurrExpr)] -> [(Id, [Expr])] -> [(ExprEnv, Model, SymbolicIds, CurrExpr)]
substHigherOrder' eenvsice [] = eenvsice
substHigherOrder' eenvsice ((i, es):iss) =
    substHigherOrder'
        (concatMap (\e_rep -> 
                        map (\(eenv, m, si, ce) -> ( E.insert (idName i) e_rep eenv
                                                   , M.insert (idName i) e_rep m
                                                   , HS.delete i si
                                                   , replaceASTs (Var i) e_rep ce)
                            ) eenvsice)
        es) iss

data TaggerRed = TaggerRed Name NameGen

instance Reducer TaggerRed () t where
    initReducer _ _ = ()

    redRules tr@(TaggerRed n ng) _ s@(State {tags = ts}) b =
        let
            (n'@(Name n_ m_ _ _), ng') = freshSeededName n ng
        in
        if null $ HS.filter (\(Name n__ m__ _ _) -> n_ == n__ && m_ == m__) ts then
            return (Finished, [(s {tags = HS.insert n' ts}, ())], b, TaggerRed n ng')
        else
            return (Finished, [(s, ())], b, tr)

-- | A Reducer to producer logging output 
data Logger = Logger String

instance Reducer Logger [Int] t where
    initReducer _ _ = []

    redRules l@(Logger fn) li s b = do
        outputState fn li s b
        return (NoProgress, [(s, li)], b, l)
    
    updateWithAll _ [(_, l)] = [l]
    updateWithAll _ ss = map (\(l, i) -> l ++ [i]) $ zip (map snd ss) [1..]

outputState :: String -> [Int] -> State t -> Bindings -> IO ()
outputState fdn is s b = do
    let dir = fdn ++ "/" ++ foldl' (\str i -> str ++ show i ++ "/") "" is
    createDirectoryIfMissing True dir

    let fn = dir ++ "state" ++ show (length $ rules s) ++ ".txt"
    let write = pprExecStateStr s b
    writeFile fn write

    putStrLn fn

-- | Allows executing multiple halters.
-- If the halters disagree, prioritizes the order:
-- Discard, Accept, Switch, Continue
data HCombiner h1 h2 = h1 :<~> h2 deriving (Eq, Show, Read)

-- We use C to combine the halter values for HCombiner
-- We should never define any other instance of Halter with C, or export it
-- because this could lead to undecidable instances
data C a b = C a b

instance (ASTContainer a Expr, ASTContainer b Expr) => ASTContainer (C a b) Expr where
    containedASTs (C a b) = containedASTs a ++ containedASTs b
    modifyContainedASTs f (C a b) = C (modifyContainedASTs f a) (modifyContainedASTs f b)

instance (ASTContainer a Type, ASTContainer b Type) => ASTContainer (C a b) Type where
    containedASTs (C a b) = containedASTs a ++ containedASTs b
    modifyContainedASTs f (C a b) = C (modifyContainedASTs f a) (modifyContainedASTs f b)

instance (Named a, Named b) => Named (C a b) where
    names (C a b) = names a ++ names b
    rename old new (C a b) = C (rename old new a) (rename old new b)
    renames hm (C a b) = C (renames hm a) (renames hm b)

instance (Halter h1 hv1 t, Halter h2 hv2 t) => Halter (HCombiner h1 h2) (C hv1 hv2) t where
    initHalt (h1 :<~> h2) s =
        let
            hv1 = initHalt h1 s
            hv2 = initHalt h2 s
        in
        C hv1 hv2

    updatePerStateHalt (h1 :<~> h2) (C hv1 hv2) proc s =
        let
            hv1' = updatePerStateHalt h1 hv1 proc s
            hv2' = updatePerStateHalt h2 hv2 proc s
        in
        C hv1' hv2'

    discardOnStart (h1 :<~> h2) (C hv1 hv2) proc s =
        let
            b1 = discardOnStart h1 hv1 proc s
            b2 = discardOnStart h2 hv2 proc s
        in
        b1 || b2

    stopRed (h1 :<~> h2) (C hv1 hv2) proc s =
        let
            hc1 = stopRed h1 hv1 proc s
            hc2 = stopRed h2 hv2 proc s
        in
        min hc1 hc2

    stepHalter (h1 :<~> h2) (C hv1 hv2) proc xs s =
        let
            hv1' = stepHalter h1 hv1 proc xs s
            hv2' = stepHalter h2 hv2 proc xs s
        in
        C hv1' hv2'

-- | Accepts a state when it is in ExecNormalForm
data AcceptHalter = AcceptHalter

instance Halter AcceptHalter () t where
    initHalt _ _ = ()
    updatePerStateHalt _ _ _ _ = ()
    stopRed _ _ _ s =
        case isExecValueForm s && true_assert s of
            True -> Accept
            False -> Continue
    stepHalter _ _ _ _ _ = ()

-- | Allows execution to continue until the step counter hits 0, then discards the state
data ZeroHalter = ZeroHalter Int

instance Halter ZeroHalter Int t where
    initHalt (ZeroHalter n) _ = n
    updatePerStateHalt _ hv _ _ = hv
    stopRed = halterIsZero
    stepHalter = halterSub1

halterSub1 :: Halter h Int t => h -> Int -> Processed (State t) -> [State t] -> State t -> Int
halterSub1 _ h _ _ _ = h - 1

halterIsZero :: Halter h Int t => h -> Int -> Processed (State t) -> State t -> HaltC
halterIsZero _ 0 _ _ = Discard
halterIsZero _ _ _ _ = Continue

data MaxOutputsHalter = MaxOutputsHalter (Maybe Int)

instance Halter MaxOutputsHalter (Maybe Int) t where
    initHalt (MaxOutputsHalter m) _ = m
    updatePerStateHalt _ hv _ _ = hv
    stopRed _ m (Processed {accepted = acc}) _ =
        case m of
            Just m' -> if length acc >= m' then Discard else Continue
            _ -> Continue
    stepHalter _ hv _ _ _ = hv

-- | Switch execution every n steps
data SwitchEveryNHalter = SwitchEveryNHalter Int

instance Halter SwitchEveryNHalter Int t where
    initHalt (SwitchEveryNHalter sw) _ = sw
    updatePerStateHalt (SwitchEveryNHalter sw) _ _ _ = sw
    stopRed _ i _ _ = if i <= 0 then Switch else Continue
    stepHalter _ i _ _ _ = i - 1

-- | Switches execution every n steps, where n is divided every time
-- a case split happens, by the number of states.
-- That is, if n is 2100, and the case splits into 3 states, each new state will
-- will then get only 700 steps
data BranchAdjSwitchEveryNHalter = BranchAdjSwitchEveryNHalter { switch_def :: Int
                                                               , switch_min :: Int }

data SwitchingPerState = SwitchingPerState { switch_at :: Int -- ^ Max number of steps
                                           , counter :: Int -- ^ Current step counter
                                           }

instance Halter BranchAdjSwitchEveryNHalter SwitchingPerState t where
    initHalt (BranchAdjSwitchEveryNHalter { switch_def = sw }) _ =
        SwitchingPerState { switch_at = sw, counter = sw }
    updatePerStateHalt _ sps@(SwitchingPerState { switch_at = sw }) _ _ =
        sps { counter = sw }
    stopRed _ (SwitchingPerState { counter = i }) _ _ =
        if i <= 0 then Switch else Continue
    stepHalter (BranchAdjSwitchEveryNHalter { switch_min = mi })
               sps@(SwitchingPerState { switch_at = sa, counter = i }) _ xs _ =
        let
            new_sa = max mi (sa `div` length xs)
            new_i = min (i - 1) new_sa
        in
        sps { switch_at = new_sa, counter = new_i}

data BranchAdjVarLookupLimit = BranchAdjVarLookupLimit { var_switch_def :: Int
                                                       , var_switch_min :: Int }

instance Halter BranchAdjVarLookupLimit SwitchingPerState t where
    initHalt (BranchAdjVarLookupLimit { var_switch_def = sw }) _ =
        SwitchingPerState { switch_at = sw, counter = sw }
    updatePerStateHalt _ sps@(SwitchingPerState { switch_at = sw }) _ _ =
        sps { counter = sw }
    stopRed _ (SwitchingPerState { counter = i }) _ _ =
        if i <= 0 then Switch else Continue

    stepHalter (BranchAdjVarLookupLimit { var_switch_min = mi })
               sps@(SwitchingPerState { switch_at = sa, counter = i }) _ xs
               (State { curr_expr = CurrExpr Evaluate (Var _) }) =
        let
            new_sa = max mi (sa `div` length xs)
            new_i = min (i - 1) new_sa
        in
        sps { switch_at = new_sa, counter = new_i}
    stepHalter _ sps _ _ _ = sps


-- Cutoff recursion after n recursive calls
data RecursiveCutOff = RecursiveCutOff Int

instance Halter RecursiveCutOff (HM.HashMap SpannedName Int) t where
    initHalt _ _ = HM.empty
    updatePerStateHalt _ hv _ _ = hv

    stopRed (RecursiveCutOff co) hv _ (State { curr_expr = CurrExpr _ (Var (Id n _)) }) =
        case HM.lookup (SpannedName n) hv of
            Just i
                | i > co -> Discard
                | otherwise -> Continue
            Nothing -> Continue
    stopRed _ _ _ _ = Continue

    stepHalter _ hv _ _ s@(State { curr_expr = CurrExpr _ (Var (Id n _)) })
        | not $ E.isSymbolic n (expr_env s) =
            case HM.lookup sn hv of
                Just i -> HM.insert sn (i + 1) hv
                Nothing -> HM.insert sn 1 hv
        | otherwise = hv
        where
            sn = SpannedName n
    stepHalter _ hv _ _ _ = hv

-- | If the Name, disregarding the Unique, in the DiscardIfAcceptedTag
-- matches a Tag in the Accepted State list,
-- and in the State being evaluated, discard the State
data DiscardIfAcceptedTag = DiscardIfAcceptedTag Name 

instance Halter DiscardIfAcceptedTag (HS.HashSet Name) t where
    initHalt _ _ = HS.empty
    
    -- updatePerStateHalt gets the intersection of the accepted States Tags,
    -- and the Tags of the State being evaluated.
    -- Then, it filters further by the name in the Halter
    updatePerStateHalt (DiscardIfAcceptedTag (Name n m _ _)) 
                       _ 
                       (Processed {accepted = acc})
                       (State {tags = ts}) =
        let
            allAccTags = HS.unions $ map tags acc
            matchCurrState = HS.intersection ts allAccTags
        in
        HS.filter (\(Name n' m' _ _) -> n == n' && m == m') matchCurrState

    stopRed _ ns _ _ =
        if not (HS.null ns) then Discard else Continue

    stepHalter _ hv _ _ _ = hv

-- | Counts the number of variable lookups are made, and switches the state
-- whenever we've hit a threshold

data VarLookupLimit = VarLookupLimit Int

instance Halter VarLookupLimit Int t where
    initHalt (VarLookupLimit lim) _ = lim
    updatePerStateHalt (VarLookupLimit lim) _ _ _ = lim
    stopRed _ lim _ _ = if lim <= 0 then Switch else Continue

    stepHalter _ lim _ _ (State { curr_expr = CurrExpr Evaluate (Var _) }) = lim - 1
    stepHalter _ lim _ _ _ = lim


-- Orderer things

-- | Does not respect getState, but simply uses the default Ord instance
data OCombiner o1 o2 = o1 :<-> o2 deriving (Eq, Show, Read)

instance (MinOrderer or1 sov1 b1 t, MinOrderer or2 sov2 b2 t)
      => MinOrderer (OCombiner or1 or2) (C sov1 sov2) (b1, b2) t where
  
    -- | Initializing the per state ordering value 
    minInitPerStateOrder (or1 :<-> or2) s =
      let
          sov1 = minInitPerStateOrder or1 s
          sov2 = minInitPerStateOrder or2 s
      in
      C sov1 sov2

    -- | Assigns each state some value of an ordered type, and then proceeds with execution on the
    -- state assigned the minimal value
    minOrderStates (or1 :<-> or2) (C sov1 sov2) s =
      let
          sov1' = minOrderStates or1 sov1 s
          sov2' = minOrderStates or2 sov2 s
      in
      (sov1', sov2')

    -- | Run on the selected state, to update it's sov field
    minUpdateSelected (or1 :<-> or2) (C sov1 sov2) proc s = 
      let
          sov1' = minUpdateSelected or1 sov1 proc s
          sov2' = minUpdateSelected or2 sov2 proc s
      in
      C sov1' sov2'

    minStepOrderer (or1 :<-> or2) (C sov1 sov2) proc xs s =
        let
            sov1' = minStepOrderer or1 sov1 proc xs s
            sov2' = minStepOrderer or2 sov2 proc xs s
        in
        C sov1' sov2'


data NextOrderer = NextOrderer

instance Orderer NextOrderer () Int t where
    initPerStateOrder _ _ = ()
    orderStates _ _ _ = 0
    updateSelected _ v _ _ = v

-- | Continue execution on the state that has been picked the least in the past. 
data PickLeastUsedOrderer = PickLeastUsedOrderer

instance Orderer PickLeastUsedOrderer Int Int t where
    initPerStateOrder _ _ = 0
    orderStates _ v _ = v
    updateSelected _ v _ _ = v + 1

-- | Floors and does bucket size
data BucketSizeOrderer = BucketSizeOrderer Int

instance MinOrderer BucketSizeOrderer Int Int t where
    minInitPerStateOrder _ _ = 0

    minOrderStates (BucketSizeOrderer b) v _ = floor (fromIntegral v / fromIntegral b :: Float)

    minUpdateSelected _ v _ _ = v + 1

-- | Order by the number of PCs
data CaseCountOrderer = CaseCountOrderer

instance Orderer CaseCountOrderer Int Int t where
    initPerStateOrder _ _ = 0

    orderStates _ v _ = v

    updateSelected _ v _ _ = v

    stepOrderer _ v _ _ (State { curr_expr = CurrExpr _ (Case _ _ _) }) = v + 1
    stepOrderer _ v _ _ _ = v


-- Orders by the smallest symbolic ADTs
data SymbolicADTOrderer = SymbolicADTOrderer

instance Orderer SymbolicADTOrderer (HS.HashSet Name) Int t where
    initPerStateOrder _ = HS.map idName . symbolic_ids
    orderStates _ v _ = HS.size v

    updateSelected _ v _ _ = v

    stepOrderer _ v _ _ s =
        v `HS.union` (HS.map idName $ symbolic_ids s)

-- Orders by the largest (in terms of height) (previously) symbolic ADT
data ADTHeightOrderer = ADTHeightOrderer

instance MinOrderer ADTHeightOrderer (HS.HashSet Name) Int t where
    minInitPerStateOrder _ = HS.map idName . symbolic_ids
    minOrderStates _ v s = maximum . HS.toList $ HS.map (flip adtHeight s) v

    minUpdateSelected _ v _ _ = v

    -- stepOrderer _ v _ _ s =
    --     v `HS.union` (HS.fromList . map idName . symbolic_ids $ s)

adtHeight :: Name -> State t -> Int
adtHeight n s@(State { expr_env = eenv })
    | Just (E.Sym _) <- v = 0
    | Just (E.Conc e) <- v =
        1 + adtHeight' e s
    | otherwise = 0
    where
        v = E.lookupConcOrSym n eenv

adtHeight' :: Expr -> State t -> Int
adtHeight' e s =
    let
        _:es = unApp e 
    in
    maximum $ map (\e' -> case e' of
                        Var (Id n _) -> adtHeight n s
                        _ -> 0) es

-- Wraps an existing Orderer, and increases it's value by 1, every time
-- it doesn't change after N steps 
data IncrAfterN ord = IncrAfterN Int ord

data IncrAfterNTr sov = IncrAfterNTr { steps_since_change :: Int
                                     , incr_by :: Int
                                     , underlying :: sov }

instance (Eq sov, Enum b, MinOrderer ord sov b t) => MinOrderer (IncrAfterN ord) (IncrAfterNTr sov) b t where
    minInitPerStateOrder (IncrAfterN _ ord) s =
        IncrAfterNTr { steps_since_change = 0
                     , incr_by = 0
                     , underlying = minInitPerStateOrder ord s }
    minOrderStates (IncrAfterN _ ord) sov s =
        let
            b = minOrderStates ord (underlying sov) s
        in
        succNTimes (incr_by sov) b
    minUpdateSelected (IncrAfterN _ ord) sov pr s =
        sov { underlying = minUpdateSelected ord (underlying sov) pr s }
    minStepOrderer (IncrAfterN ma ord) sov pr xs s
        | steps_since_change sov >= ma =
            sov' { incr_by = incr_by sov' + 1
                 , steps_since_change = 0 }
        | under /= under' =
            sov' { steps_since_change = 0 }
        | otherwise =
            sov' { steps_since_change = steps_since_change sov' + 1}
        where
            under = underlying sov
            under' = minStepOrderer ord under pr xs s
            sov' = sov { underlying = under' }


succNTimes :: Enum b => Int -> b -> b
succNTimes x b
    | x <= 0 = b
    | otherwise = succNTimes (x - 1) (succ b)

--------
--------

-- | Uses a passed Reducer, Halter and Orderer to execute the reduce on the State, and generated States
runReducer :: (Reducer r rv t, Halter h hv t, Orderer or sov b t) => r -> h -> or -> State t -> Bindings -> IO (Processed (State t), Bindings)
runReducer red hal ord s b = do
    let pr = Processed {accepted = [], discarded = []}
    let s' = ExState { state = s
                    , reducer_val = initReducer red s
                    , halter_val = initHalt hal s
                    , order_val = initPerStateOrder ord s }

    (states, b') <- runReducer' red hal ord pr s' b M.empty
    let states' = mapProcessed state states
    return (states', b')

runReducer' :: (Reducer r rv t, Halter h hv t, Orderer or sov b t) 
            => r 
            -> h 
            -> or 
            -> Processed (ExState rv hv sov t) 
            -> ExState rv hv sov t 
            -> Bindings
            -> M.Map b [ExState rv hv sov t] 
            -> IO (Processed (ExState rv hv sov t), Bindings)
runReducer' red hal ord pr rs@(ExState { state = s, reducer_val = r_val, halter_val = h_val, order_val = o_val }) b xs
    | hc == Accept =
        let
            pr' = pr {accepted = rs:accepted pr}
            jrs = minState ord pr' xs
        in
        case jrs of
            Just (rs', xs') -> do
                switchState red hal ord pr' rs' b xs'
                -- runReducer' red hal ord pr' (updateExStateHalter hal pr' rs') b xs'
            Nothing -> return (pr', b)
    | hc == Discard =
        let
            pr' = pr {discarded = rs:discarded pr}
            jrs = minState ord pr' xs
        in
        case jrs of
            Just (rs', xs') ->
                switchState red hal ord pr' rs' b xs'
                -- runReducer' red hal ord pr' (updateExStateHalter hal pr' rs') b xs'
            Nothing -> return (pr', b)
    | hc == Switch =
        let
            k = orderStates ord (order_val rs') (state rs)
            rs' = rs { order_val = updateSelected ord (order_val rs) ps (state rs) }

            Just (rs'', xs') = minState ord pr (M.insertWith (++) k [rs'] xs)
        in
        switchState red hal ord pr rs'' b xs'
        -- if not $ discardOnStart hal (halter_val rs''') ps (state rs''')
        --     then runReducer' red hal ord pr rs''' b xs'
        --     else runReducerList red hal ord (pr {discarded = rs''':discarded pr}) xs' b
    | otherwise = do
        (_, reduceds, b', red') <- redRules red r_val s b
        let reduceds' = map (\(r, rv) -> (r {num_steps = num_steps r + 1}, rv)) reduceds

        let r_vals = updateWithAll red reduceds' ++ error "List returned by updateWithAll is too short."
            new_states = map fst reduceds'
        
            mod_info = map (\(s', r_val') ->
                                rs { state = s'
                                   , reducer_val = r_val'
                                   , halter_val = stepHalter hal h_val ps new_states s'
                                   , order_val = stepOrderer ord o_val ps new_states s'}) $ zip new_states r_vals
        
        case mod_info of
            (s_h:ss_tail) -> do
                let xs' = foldr (\s' -> M.insertWith (++) (orderStates ord (order_val s') (state s')) [s']) xs ss_tail
                runReducer' red' hal ord pr s_h b' xs'
            [] -> runReducerList red' hal ord pr xs b' 
    where
        hc = stopRed hal h_val ps s
        ps = processedToState pr

switchState :: (Reducer r rv t, Halter h hv t, Orderer or sov b t)
            => r
            -> h
            -> or
            -> Processed (ExState rv hv sov t) 
            -> ExState rv hv sov t 
            -> Bindings
            -> M.Map b [ExState rv hv sov t] 
            -> IO (Processed (ExState rv hv sov t), Bindings)
switchState red hal ord  pr rs b xs
    | not $ discardOnStart hal (halter_val rs') ps (state rs') =
        runReducer' red hal ord pr rs' b xs
    | otherwise =
        runReducerListSwitching red hal ord (pr {discarded = rs':discarded pr}) xs b
    where
        ps = processedToState pr
        rs' = rs { halter_val = updatePerStateHalt hal (halter_val rs) ps (state rs) }

-- To be used when we we need to select a state without switching 
runReducerList :: (Reducer r rv t, Halter h hv t, Orderer or sov b t) 
               => r 
               -> h 
               -> or 
               -> Processed (ExState rv hv sov t)
               -> M.Map b [ExState rv hv sov t]
               -> Bindings
               -> IO (Processed (ExState rv hv sov t), Bindings)
runReducerList red hal ord pr m binds =
    case minState ord pr m of
        Just (x, m') -> runReducer' red hal ord pr x binds m'
        Nothing -> return (pr, binds)

-- To be used when we are possibly switching states 
runReducerListSwitching :: (Reducer r rv t, Halter h hv t, Orderer or sov b t) 
                        => r 
                        -> h 
                        -> or 
                        -> Processed (ExState rv hv sov t)
                        -> M.Map b [ExState rv hv sov t]
                        -> Bindings
                        -> IO (Processed (ExState rv hv sov t), Bindings)
runReducerListSwitching red hal ord pr m binds =
    case minState ord pr m of
        Just (x, m') -> switchState red hal ord pr x binds m'
        Nothing -> return (pr, binds)

processedToState :: Processed (ExState rv hv sov t) -> Processed (State t)
processedToState (Processed {accepted = app, discarded = dis}) =
    Processed {accepted = map state app, discarded = map state dis}

-- Uses the Orderer to determine which state to continue execution on.
-- Returns that State, and a list of the rest of the states 
minState :: (Orderer or sov b t)
         => or
         -> Processed (ExState rv hv sov t)
         -> M.Map b [ExState rv hv sov t]
         -> Maybe ((ExState rv hv sov t), M.Map b [ExState rv hv sov t])
minState ord pr m =
    case getState ord ps m of
      Just ((k, x:xs), _) -> Just (x, M.insert k xs m)
      Just ((_, []), m') -> minState ord pr m'
      Nothing -> Nothing
      where
          ps = processedToState pr

--------------------------------------------------------------------------------------------------------------------------------------

runReducerMerge :: (Show t, Eq t, Named t, Reducer r rv t, Halter h hv t, Simplifier simplifier)
                 => r -> h -> simplifier -> State t -> Bindings
                 -> IO ([State t], Bindings)
runReducerMerge red hal simplifier s b = do
    let pr = Processed {accepted = [], discarded = []}
        s' = ExState {state = s, halter_val = initHalt hal s, reducer_val = initReducer red s, order_val = Nothing}
        -- workGraph = WG.initGraph s' (red, hal, simplifier, b, pr) runReducerMerge' mergeStates resetSaturated logState
        zipper = initZipper s' (red, hal, simplifier, b, pr) runReducerMerge' mergeStates resetMergingZipper logState

    -- (_, (_, _, _, b', pr')) <- WG.work workGraph
    (_, _, _, b', pr') <- evalZipper zipper
    res <- mapM (\ExState {state = st} -> return st) (accepted pr')
    return (res, b')

-- | work_func for both WorkGraph and ZipperTree. Reduces the ExState `exS` and returns the reduceds along with the appropriate Status
runReducerMerge' :: (Show t, Eq t, Named t, Reducer r rv t, Halter h hv t, Simplifier simplifier)
                 => ExState rv hv sov t
                 -> (r, h, simplifier, Bindings, Processed (ExState rv hv sov t))
                 -> IO ([(ExState rv hv sov t)], (r, h, simplifier, Bindings, Processed (ExState rv hv sov t)), WG.Status)
runReducerMerge' exS (red, hal, simplifier, bdg, pr) = do
    let rs@(ExState {state = s, halter_val = h_val, reducer_val = r_val}) = exS
        ps = processedToState pr -- need to deal with processed
        hc = stopRed hal h_val ps s
    case hc of
        Accept -> return ([rs], (red, hal, simplifier, bdg, pr {accepted = rs:accepted pr}), WG.Accept)
        Discard -> return ([rs], (red, hal, simplifier, bdg, pr {discarded = rs:discarded pr}), WG.Discard)
        _ -> do
            (reducerRes, reduceds, bdg', red') <- redRules red r_val s bdg
            let reduceds' = map (\(r, rv) -> (r {num_steps = num_steps r + 1}, rv)) reduceds
            let r_vals = updateWithAll red reduceds' ++ error "List returned by updateWithAll is too short.."
            let new_states = map fst reduceds'
            let reduceds'' = map (\(s', r_val') -> rs { state = s'
                                                      , reducer_val = r_val'
                                                      , halter_val = stepHalter hal h_val ps new_states s'})
                                                      $ zip new_states r_vals
            let status = case reducerRes of MergePoint -> WG.Mergeable; MaxDepth -> WG.WorkSaturated; Split -> WG.Split; _ -> WG.WorkNeeded
            return (reduceds'', (red', hal, simplifier, bdg', pr), status)

-- | Reset counts of all unmerged Case Expressions to 0
resetSaturated :: (ExState rv hv sov t) -> (ExState rv hv sov t)
resetSaturated rs@(ExState {state = s}) =
    let s' = s {cases = M.empty, depth_exceeded = False}
    in rs {state = s'}

-- | Merge Func for WorkGraph and Tree Zipper. Attempts to merge 2 states
mergeStates :: (Eq t, Named t, Reducer r rv t, Halter h hv t, Simplifier simplifier)
            => (ExState rv hv sov t) -> (ExState rv hv sov t) -> (r, h, simplifier, Bindings, Processed (ExState rv hv sov t))
            -> (Maybe (ExState rv hv sov t), (r, h, simplifier, Bindings, Processed (ExState rv hv sov t)))
mergeStates ex1 ex2 (r, h, smplfr, b, pr) =
    let res = mergeState (name_gen b) smplfr (state ex1) (state ex2)
    in case res of
        (ng', Just s') -> (Just ex1 {state = s'}, (r, h, smplfr, b {name_gen = ng'}, pr)) -- todo: which reducer_val and halter_val to keep
        (ng', Nothing) -> (Nothing, (r, h, smplfr, b {name_gen = ng'}, pr))

-- | Function for Logger in workGraph that outputs curr_expr
logState :: Show t => ExState rv hv sov t -> (r,h,s,Bindings,p) -> String
logState (ExState { state = s }) (_,_,_,b,_) = pprExecStateStr s b

-- | Remove any MergePtFrame-s in the exec_stack of the ExState. Called when we float states to Root when tree grows too deep
resetMergingZipper :: (ExState rv hv sov t) -> (ExState rv hv sov t)
resetMergingZipper rs@(ExState {state = s}) =
    let st = exec_stack s
        st' = delMergePtFrames st
        s' = s {exec_stack = st', cases = M.empty, depth_exceeded = False}
    in rs {state = s'}

delMergePtFrames :: Stck.Stack Frame -> Stck.Stack Frame
delMergePtFrames st =
    let xs = Stck.toList st
        xs' = filter (\fr -> case fr of
                                MergePtFrame _ -> False
                                _ -> True) xs
    in Stck.fromList xs'
