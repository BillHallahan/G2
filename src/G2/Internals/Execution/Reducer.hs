{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Internals.Execution.Reducer ( Reducer (..)
                                      , Halter (..)
                                      , Orderer (..)
                                      , StdRed (..)
                                      , ZeroHalter (..)
                                      , NextOrderer (..)
                                      , executeNext
                                      , halterSub1
                                      , halterIsZero ) where

import G2.Internals.Execution.Rules
import G2.Internals.Language.Support

-- | Reducer r t
-- A Reducer is used to describe a set of Reduction Rules
-- A set of Reduction Rules takes a State, and outputs new states
class Reducer r  t | r -> t where
    -- | redRules
    -- Takes a State, and performs the appropriate Reduction Rule
    redRules :: r -> State h t -> (Rule, [ReduceResult t])

-- | Halter h hv
-- Determines when to stop evaluating a state
class Halter h hv t | h -> hv where
    -- | initHalt
    -- Initializes each state halter value
    initHalt :: h -> State hv t -> hv

    -- | stopRed
    -- Determines whether to continue reduction on the current state
    stopRed :: h -> State hv t -> Bool

    -- | stepHalter
    -- Takes a state, and updates it's halter record field
    stepHalter :: h -> State hv t -> hv

-- | Orderer r p
-- Picks an order to evaluate the states, to allow prioritizing some over others 
class Orderer or orv t | or -> orv where
    -- | initOrdering
    -- Initializing each states ordering value 
    initOrder :: or -> State h t -> orv

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
    stopRed = halterIsZero
    stepHalter = halterSub1

instance Orderer NextOrderer () t where
    initOrder _ _ = ()
    orderStates = executeNext

executeNext :: Orderer r () t => r -> p -> [([Int], State h t)] -> [([Int], State h t)] -> ([([Int], State h t)], ())
executeNext _ _ _ xs = (xs, ())

halterSub1 :: Halter h Int t => h -> State Int t -> Int
halterSub1 _ (State {halter = h}) = h - 1

halterIsZero :: Halter h Int t => h -> State Int t -> Bool
halterIsZero _ (State {halter = 0}) = True
halterIsZero _ _ = False
