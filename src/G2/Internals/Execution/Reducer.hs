{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module G2.Internals.Execution.Reducer ( Reducer (..)
                                      , Halter (..)
                                      , Orderer (..)
                                      , ExState (..)
                                      , Processed (..)
                                      , HaltC (..)
                                      , HCombiner (..)
                                      , StdRed (..)
                                      , ZeroHalter (..)
                                      , NextOrderer (..)
                                      , executeNext
                                      , halterSub1
                                      , halterIsZero ) where

import G2.Internals.Config
import G2.Internals.Execution.Rules
import G2.Internals.Language

-- | ExState
-- Used when applying execution rules
-- Allows tracking extra information to control halting of rule application,
-- and to reorder states
-- see also, the Reducer, Halter, Orderer typeclasses
-- cases is used for logging states
data ExState hv sov t = ExState { state :: State t
                                , halter_val :: hv
                                , order_val :: sov
                                , cases :: [Int]}

-- | Processed a
-- Keeps track of type a's that have either been accepted or dropped
data Processed a = Processed { accepted :: [a]
                             , discarded :: [a] }

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
    redRules :: r -> State t -> (Rule, [ReduceResult t])

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
    orderStates :: or -> orv -> Processed (ExState h sov t) -> [ExState h sov t] -> ([ExState h sov t], orv)    

-- HCombiner h1 h2
-- Allows executing multiple halters.
-- If the halters disagree, prioritizes the order:
-- Discard, Accept, Switch, Continue
data HCombiner h1 h2 = h1 :<~ h2 deriving (Eq, Show, Read)

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
    initHalt (h1 :<~ h2) config s =
        let
            hv1 = initHalt h1 config s
            hv2 = initHalt h2 config s
        in
        C hv1 hv2

    reInitHalt (h1 :<~ h2) (C hv1 hv2) proc s =
        let
            hv1' = reInitHalt h1 hv1 proc s
            hv2' = reInitHalt h2 hv2 proc s
        in
        C hv1' hv2'

    stopRed (h1 :<~ h2) (C hv1 hv2) proc s =
        let
            hc1 = stopRed h1 hv1 proc s
            hc2 = stopRed h2 hv2 proc s
        in
        min hc1 hc2

    stepHalter (h1 :<~ h2) (C hv1 hv2) proc s =
        let
            hv1' = stepHalter h1 hv1 proc s
            hv2' = stepHalter h2 hv2 proc s
        in
        C hv1' hv2'

data StdRed = StdRed
data ZeroHalter = ZeroHalter
data NextOrderer = NextOrderer

instance Reducer StdRed () where
    redRules _ = stdReduce

instance Halter ZeroHalter Int t where
    initHalt _ config _ = steps config
    reInitHalt _ hv _ _ = hv
    stopRed = halterIsZero
    stepHalter = halterSub1

instance Orderer NextOrderer () () t where
    initOrder _ _ _ = ()
    initPerStateOrder _ _ _ = ()
    orderStates = executeNext

executeNext :: Orderer r () () t => r -> p -> Processed (ExState h sov t) -> [ExState h sov t] -> ([ExState h sov t], ())
executeNext _ _ _ xs = (xs, ())

halterSub1 :: Halter h Int t => h -> Int -> Processed (State t) -> State t -> Int
halterSub1 _ h _ _ = h - 1

halterIsZero :: Halter h Int t => h -> Int -> Processed (State t) -> State t -> HaltC
halterIsZero _ 0 _ s =
    case isExecValueForm s && true_assert s of
        True -> Accept
        False -> Discard
halterIsZero _ _ _ _ = Continue
