{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Internals.Execution.Reducer ( Reducer (..)
                                      , Halter (..)
                                      , Orderer (..)
                                      , HaltC (..)
                                      , StdRed (..)
                                      , ZeroHalter (..)
                                      , NextOrderer (..)
                                      , executeNext
                                      , halterSub1
                                      , halterIsZero ) where

import G2.Internals.Config
import G2.Internals.Execution.Rules
import G2.Internals.Language.Support

-- | Reducer r t
-- A Reducer is used to describe a set of Reduction Rules
-- A set of Reduction Rules takes a State, and outputs new states
-- The type parameter r is used to disambiguate between different producers.
-- To create a new reducer, define some new type, and use it as r.
class Reducer r  t | r -> t where
    -- | redRules
    -- Takes a State, and performs the appropriate Reduction Rule
    redRules :: r -> State h t -> (Rule, [ReduceResult t])

-- HaltC
-- Used by members of the Halter typeclass to control whether to continue
-- evaluating the current State, or switch to evaluating a new state.
data HaltC = Continue -- Continue evaluating the current State
           | Switch -- Switch to evaluating a new state, but continue evaluating the current state later
           | Accept -- Switch to evaluating a new state, and accept the current state
           | Discard -- Switch to evaluating a new state, and reject the current state
           deriving (Eq, Show, Read)

-- | Halter h hv t
-- Determines when to stop evaluating a state
-- The type parameter h is used to disambiguate between different producers.
-- To create a new reducer, define some new type, and use it as h.
class Halter h hv t | h -> hv where
    -- | initHalt
    -- Initializes each state halter value
    initHalt :: h -> Config -> State hv2 t -> hv

    -- | stopRed
    -- Determines whether to continue reduction on the current state
    stopRed :: h -> State hv t -> HaltC

    -- | stepHalter
    -- Takes a state, and updates it's halter record field
    stepHalter :: h -> State hv t -> hv

-- | Orderer or orv t
-- Picks an order to evaluate the states, to allow prioritizing some over others 
-- The type parameter or is used to disambiguate between different producers.
-- To create a new reducer, define some new type, and use it as or.
class Orderer or orv t | or -> orv where
    -- | initOrdering
    -- Initializing each states ordering value 
    initOrder :: or -> Config -> State h t -> orv

    --  orderStates
    -- Takes a list of states that have finished executing, and been kept
    -- and states that still have to be run through reduction rules.
    -- Reorders the latter list, to set the priority of each state
    -- The State at the head of the list is the next executed.
    -- Takes and returns some extra data that it can use however it wants
    orderStates :: or -> orv -> [([Int], State h t)] -> [([Int], State h t)] -> ([([Int], State h t)], orv)

data StdRed = StdRed
data ZeroHalter = ZeroHalter
data NextOrderer = NextOrderer

instance Reducer StdRed () where
    redRules _ = stdReduce

instance Halter ZeroHalter Int t where
    initHalt _ config _ = steps config
    stopRed = halterIsZero
    stepHalter = halterSub1

instance Orderer NextOrderer () t where
    initOrder _ _ _ = ()
    orderStates = executeNext

executeNext :: Orderer r () t => r -> p -> [([Int], State h t)] -> [([Int], State h t)] -> ([([Int], State h t)], ())
executeNext _ _ _ xs = (xs, ())

halterSub1 :: Halter h Int t => h -> State Int t -> Int
halterSub1 _ (State {halter = h}) = h - 1

halterIsZero :: Halter h Int t => h -> State Int t -> HaltC
halterIsZero _ s@(State {halter = 0}) =
    case isExecValueForm s && true_assert s of
        True -> Accept
        False -> Discard
halterIsZero _ _ = Continue
