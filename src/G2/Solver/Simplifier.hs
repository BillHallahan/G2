{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Solver.Simplifier ( Simplifier (..)
                            , IdSimplifier (..)) where

import G2.Language

class Simplifier simplifier where
    -- | Simplifies a PC, by converting it to a form that is easier for the Solver's to handle
    simplifyPC :: forall t . simplifier -> State t -> PathCond -> (State t, [PathCond])

    {-# INLINE simplifyPCs #-}
    simplifyPCs :: forall t. simplifier -> State t -> PathCond -> PathConds -> PathConds
    simplifyPCs _ _ _ = id

    -- | Reverses the affect of simplification in the model, if needed.
    reverseSimplification :: forall t . simplifier -> State t -> Bindings -> Model -> Model

-- | A simplifier that does no simplification
data IdSimplifier = IdSimplifier

instance Simplifier IdSimplifier where
    simplifyPC _ s pc = (s, [pc])
    reverseSimplification _ _ _ m = m
