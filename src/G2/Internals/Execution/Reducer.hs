{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module G2.Internals.Execution.Reducer ( Reducer (..)
                                      , Halter (..)
                                      , Orderer (..)
                                      , Processed (..)
                                      , ReducerRes (..)
                                      , HaltC (..)
                                      , HCombiner (..)
                                      , StdRed (..)
                                      , ZeroHalter (..)
                                      , MaxOutputsHalter (..)
                                      , NextOrderer (..)
                                      , getState
                                      , getOrderVal
                                      , setOrderVal
                                      , executeNext
                                      , halterSub1
                                      , halterIsZero

                                      , reduce
                                      , runReducer ) where

import G2.Internals.Config
import G2.Internals.Execution.Rules
import G2.Internals.Language
import G2.Internals.Solver
import G2.Lib.Printers

import Data.Foldable
import Data.Maybe
import System.Directory

import Debug.Trace

-- | ExState
-- Used when applying execution rules
-- Allows tracking extra information to control halting of rule application,
-- and to reorder states
-- see also, the Reducer, Halter, Orderer typeclasses
-- cases is used for logging states
data ExState hv sov t = ExState { state :: State t
                                , halter_val :: hv
                                , order_val :: sov
                                , cases :: [Int]
                                }

getState :: ExState hv sov t -> State t
getState (ExState {state = s}) = s

getOrderVal :: ExState hv sov t -> sov
getOrderVal (ExState {order_val = ord}) = ord

setOrderVal :: ExState hv sov t -> sov -> ExState hv sov t
setOrderVal s sv = s {order_val = sv}

-- | Processed a
-- Keeps track of type a's that have either been accepted or dropped
data Processed a = Processed { accepted :: [a]
                             , discarded :: [a] }

-- | ReducerRes
-- Used by Reducers to indicate there progress reducing
data ReducerRes = NoProgress | InProgress | Finished deriving (Eq, Ord, Show, Read)

progPrioritizer :: ReducerRes -> ReducerRes -> ReducerRes
progPrioritizer InProgress _ = InProgress
progPrioritizer _ InProgress = InProgress
progPrioritizer Finished _ = Finished
progPrioritizer _ Finished = Finished
progPrioritizer _ _ = NoProgress

-- HaltC
-- Used by members of the Halter typeclass to control whether to continue
-- evaluating the current State, or switch to evaluating a new state.
data HaltC = Discard -- Switch to evaluating a new state, and reject the current state
           | Accept -- Switch to evaluating a new state, and accept the current state
           | Switch -- Switch to evaluating a new state, but continue evaluating the current state later
           | Continue -- Continue evaluating the current State
           deriving (Eq, Ord, Show, Read)

-- | Reducer r t
-- A Reducer is used to describe a set of Reduction Rules
-- A set of Reduction Rules takes a State, and outputs new states
-- The type parameter r is used to disambiguate between different producers.
-- To create a new reducer, define some new type, and use it as r.
class Reducer r  t | r -> t where
    -- | redRules
    -- Takes a State, and performs the appropriate Reduction Rule
    redRules :: r -> State t -> IO (ReducerRes, [State t])

-- | Halter h hv t
-- Determines when to stop evaluating a state
-- The type parameter h is used to disambiguate between different producers.
-- To create a new reducer, define some new type, and use it as h.
class Halter h hv t | h -> hv where
    -- | initHalt
    -- Initializes each state halter value
    initHalt :: h -> Config -> State t -> hv

    -- | reInitHalt
    -- Runs whenever we switch to evaluating a different state,
    -- to update the halter value of that new state
    reInitHalt :: h -> hv -> Processed (State t) -> State t -> hv

    -- | stopRed
    -- Determines whether to continue reduction on the current state
    stopRed :: h -> hv -> Processed (State t) -> State t -> HaltC

    -- | stepHalter
    -- Takes a state, and updates it's halter record field
    stepHalter :: h -> hv -> Processed (State t) -> State t -> hv

-- | Orderer or orv t
-- Picks an order to evaluate the states, to allow prioritizing some over others 
-- The type parameter or is used to disambiguate between different producers.
-- To create a new reducer, define some new type, and use it as or.
-- Law: Given
--    (exs', _) = orderStates or orv proc exs
-- it must be the case that length exs' == length exs
-- An Orderer should never eliinate a state, only reorder the states
-- To not evaluate certain states, use a Halterer
class Orderer or orv sov t | or -> orv, or -> sov where
    -- | initOrdering
    -- Initializing the overall ordering value 
    initOrder :: or -> Config -> State t -> orv

    -- | initPerStateOrdering
    -- Initializing the per state ordering value 
    initPerStateOrder :: or -> Config -> State t -> sov

    --  orderStates
    -- Takes a list of states that have finished executing, and been kept
    -- and states that still have to be run through reduction rules.
    -- Reorders the latter list, to set the priority of each state
    -- The State at the head of the list is the next executed.
    -- Takes and returns some extra data that it can use however it wants
    orderStates :: or -> orv -> Processed (ExState hv sov t) -> [ExState hv sov t] -> ([ExState hv sov t], orv)    

-- | HCombiner h1 h2
-- Allows executing multiple halters.
-- If the halters disagree, prioritizes the order:
-- Discard, Accept, Switch, Continue
data HCombiner h1 h2 = h1 :<~> h2 deriving (Eq, Show, Read)

-- We use C to combine the halter values for HCombiner
-- We should never define any other instance of Halter with C, or export it
-- because this could lead to undecidable instances
data C a b = C a b

instance {-# OVERLAPPING #-} (ASTContainer a Expr, ASTContainer b Expr) => ASTContainer (C a b) Expr where
    containedASTs (C a b) = containedASTs a ++ containedASTs b
    modifyContainedASTs f (C a b) = C (modifyContainedASTs f a) (modifyContainedASTs f b)

instance {-# OVERLAPPING #-} (ASTContainer a Type, ASTContainer b Type) => ASTContainer (C a b) Type where
    containedASTs (C a b) = containedASTs a ++ containedASTs b
    modifyContainedASTs f (C a b) = C (modifyContainedASTs f a) (modifyContainedASTs f b)

instance {-# OVERLAPPING #-} (Named a, Named b) => Named (C a b) where
    names (C a b) = names a ++ names b
    rename old new (C a b) = C (rename old new a) (rename old new b)
    renames hm (C a b) = C (renames hm a) (renames hm b)

instance (Halter h1 hv1 t, Halter h2 hv2 t) => Halter (HCombiner h1 h2) (C hv1 hv2) t where
    initHalt (h1 :<~> h2) config s =
        let
            hv1 = initHalt h1 config s
            hv2 = initHalt h2 config s
        in
        C hv1 hv2

    reInitHalt (h1 :<~> h2) (C hv1 hv2) proc s =
        let
            hv1' = reInitHalt h1 hv1 proc s
            hv2' = reInitHalt h2 hv2 proc s
        in
        C hv1' hv2'

    stopRed (h1 :<~> h2) (C hv1 hv2) proc s =
        let
            hc1 = stopRed h1 hv1 proc s
            hc2 = stopRed h2 hv2 proc s
        in
        min hc1 hc2

    stepHalter (h1 :<~> h2) (C hv1 hv2) proc s =
        let
            hv1' = stepHalter h1 hv1 proc s
            hv2' = stepHalter h2 hv2 proc s
        in
        C hv1' hv2'

-- RCombiner r1 r2
-- Combines reducers in various ways
data RCombiner r1 r2 = r1 :<~ r2 -- | Apply r2, followed by r1
                     | r1 :<~? r2 -- | Apply r2, apply r1 only if r2 returns NoProgress
                     | r1 :<~| r2 -- | Apply r2, apply r1 only if r2 returns Finished

instance (Reducer r1 t, Reducer r2 t) => Reducer (RCombiner r1 r2) t where
    redRules (r1 :<~ r2) s = do
        (r', s') <- redRules r2 s
        rs <- mapM (redRules r1) s'
        let (r'', s'') = unzip rs

        let rf = foldr1 progPrioritizer (r':r'')

        return $ (rf, concat s'')
    redRules (r1 :<~? r2) s = do
        rs@(r', s') <- redRules r2 s
        case r' of
            NoProgress -> redRules r1 s
            _ -> return rs
    redRules (r1 :<~? r2) s = do
        rs@(r', s') <- redRules r2 s
        case r' of
            Finished -> redRules r1 s
            _ -> return rs

data StdRed ast out io = StdRed (SMTConverter ast out io) io Config
data ZeroHalter = ZeroHalter
data MaxOutputsHalter = MaxOutputsHalter
data NextOrderer = NextOrderer

instance Reducer (StdRed ast out io) () where
    redRules (StdRed smt io config) s = do
        (r, s) <- reduce stdReduce smt io config s
        
        return (if r == RuleIdentity then Finished else InProgress, s)

instance Halter ZeroHalter Int t where
    initHalt _ config _ = steps config
    reInitHalt _ hv _ _ = hv
    stopRed = halterIsZero
    stepHalter = halterSub1

instance Halter MaxOutputsHalter (Maybe Int) t where
    initHalt _ config _ = maxOutputs config
    reInitHalt _ hv _ _ = hv
    stopRed _ m (Processed {accepted = acc}) _ =
        case m of
            Just m' -> if length acc >= m' then Discard else Continue
            _ -> Continue
    stepHalter _ hv _ _ = hv

instance Orderer NextOrderer () () t where
    initOrder _ _ _ = ()
    initPerStateOrder _ _ _ = ()
    orderStates = executeNext

executeNext :: Orderer r () () t => r -> p -> Processed (ExState hv sov t) -> [ExState hv sov t] -> ([ExState hv sov t], ())
executeNext _ _ _ xs = (xs, ())

halterSub1 :: Halter h Int t => h -> Int -> Processed (State t) -> State t -> Int
halterSub1 _ h _ _ = h - 1

halterIsZero :: Halter h Int t => h -> Int -> Processed (State t) -> State t -> HaltC
halterIsZero _ 0 _ s =
    case isExecValueForm s && true_assert s of
        True -> Accept
        False -> Discard
halterIsZero _ _ _ _ = Continue

--------
--------

reduce :: (State t -> (Rule, [ReduceResult t])) -> SMTConverter ast out io -> io -> Config -> State t -> IO (Rule, [State t])
reduce red con hpp config s = do
    let (rule, res) = red s
    sts <- resultsToState con hpp config rule s res
    return (rule, sts)

-- | runReducer
-- Uses a passed Reducer, Halter and Orderer to execute the reduce on the State, and generated States
runReducer :: (Reducer r t, Halter h hv t, Orderer or orv sov t) => r -> h -> or -> SMTConverter ast out io -> io -> orv -> [State t] -> Config -> IO [([Int], State t)]
runReducer red hal ord con hpp p states config =
    mapM (\ExState {state = s, cases = c} -> return (c, s))
        =<< (runReducer' red hal ord p (Processed {accepted = [], discarded = []}) $ map (\s -> ExState { state = s
                                                                                                       , halter_val = initHalt hal config s
                                                                                                       , order_val = initPerStateOrder ord config s
                                                                                                       , cases = []}) states)
  where
    runReducer' :: (Reducer r t, Halter h hv t, Orderer or orv sov t) => r -> h -> or -> orv -> Processed (ExState hv sov t) -> [ExState hv sov t] -> IO [ExState hv sov t]
    runReducer' _ _ _ _ _ [] = return []
    runReducer' red' hal' ord' p' fnsh (rss@(ExState {state = s, halter_val = h_val, cases = is}):xs)
        | hc == Accept =
            let
                fnsh' = fnsh {accepted = rss:accepted fnsh}
                (xs', p'') = orderStates ord' p' fnsh' xs
            in
            return . (:) rss =<< runReducer' red' hal' ord' p'' fnsh' (reInitFirstHalter hal' fnsh' xs')
        | hc == Discard =
            let
                fnsh' = fnsh {discarded = rss:discarded fnsh}
                (xs', p'') = orderStates ord' p' fnsh' xs
            in
            runReducer' red' hal' ord' p'' fnsh' (reInitFirstHalter hal' fnsh' xs')
        | hc == Switch =
            let
                (xs', p'') = orderStates ord' p' fnsh (rss:xs)
            in
            runReducer' red' hal' ord' p'' fnsh (reInitFirstHalter hal' fnsh xs')
        | otherwise = do
            case logStates config of
                Just f -> outputState f is s
                Nothing -> return ()

            (_, reduceds) <- redRules red' s

            let isred = if length (reduceds) > 1 then zip (map Just [1..]) reduceds else zip (repeat Nothing) reduceds
            
            let mod_info = map (\(i, s') -> rss {state = s', halter_val = stepHalter hal' h_val (processedToState fnsh) s', cases = is ++ maybe [] (\i' -> [i']) i}) isred
            
            runReducer' red' hal' ord' p' fnsh (mod_info ++ xs)
        where
            hc = stopRed hal' h_val (processedToState fnsh) s

reInitFirstHalter :: Halter h hv t => h -> Processed (ExState hv sov t) -> [ExState hv sov t] -> [ExState hv sov t]
reInitFirstHalter h proc (es@ExState {state = s, halter_val = hv}:xs) =
    let
        hv' = reInitHalt h hv (processedToState proc) s
    in
    es {halter_val = hv'}:xs
reInitFirstHalter _ _ [] = []

processedToState :: Processed (ExState hv sov t) -> Processed (State t)
processedToState (Processed {accepted = app, discarded = dis}) =
    Processed {accepted = map state app, discarded = map state dis}

outputState :: String -> [Int] -> State t -> IO ()
outputState fdn is s = do
    let dir = fdn ++ "/" ++ foldl' (\str i -> str ++ show i ++ "/") "" is
    createDirectoryIfMissing True dir

    let fn = dir ++ "state" ++ show (length $ rules s) ++ ".txt"
    let write = pprExecStateStr s
    writeFile fn write

    putStrLn fn
