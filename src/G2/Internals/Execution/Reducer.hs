{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Internals.Execution.Reducer ( Reducer (..)
                                      , StdRed (..)
                                      , executeNext
                                      , halterSub1
                                      , halterIsZero ) where

import G2.Internals.Execution.Rules
import G2.Internals.Language.Support

-- | Reducer r h t
-- A Reducer is used to describe a set of Reduction Rules
-- A set of Reduction Rules takes a State, and outputs new states
class Reducer r p h t | r -> p, r -> h, r -> t where
    -- | redRules
    -- Takes a State, and performs the appropriate Reduction Rule
    redRules :: r -> State h t -> (Rule, [ReduceResult t])

    -- | stopRed
    -- Determines whether to continue reduction on the current state
    stopRed :: r -> State h t -> Bool

    -- | stepHalter
    -- Takes a state, and updates it's halter record field
    stepHalter :: r -> State h t -> h

    --  orderStates
    -- Takes a list of states that have finished executing, and been kept
    -- and states that still have to be run through reduction rules.
    -- Reorders the latter list, to set the priority of each state
    -- The State at the head of the list is the next executed.
    -- Takes and returns some extra data that it can use however it wants
    orderStates :: r -> p -> [([Int], State h t)] -> [([Int], State h t)] -> ([([Int], State h t)], p)

data StdRed = StdRed

instance Reducer StdRed () Int () where
    redRules _ = stdReduce
    stopRed = halterIsZero
    stepHalter = halterSub1
    orderStates = executeNext

executeNext :: Reducer r p h t => r -> p -> [([Int], State h t)] -> [([Int], State h t)] -> ([([Int], State h t)], ())
executeNext _ _ _ xs = (xs, ())

halterSub1 :: Reducer r p h t => r -> State Int t -> Int
halterSub1 _ (State {halter = h}) = h - 1

halterIsZero :: Reducer r p h t => r -> State Int t -> Bool
halterIsZero _ (State {halter = 0}) = True
halterIsZero _ _ = False
