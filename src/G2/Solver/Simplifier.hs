{-# LANGUAGE RankNTypes #-}

module G2.Solver.Simplifier ( Simplifier (..)
							, IdSimplifir (..)) where

import G2.Language

class Simplifier simplifier where
	-- | Simplifies a PC, by converting it to a form that is easier for the Solver's to handle
	simplifyPC :: forall t . simplifier -> State t -> PathCond -> [PathCond]

	-- | Reverses the affect of simplification in the model, if needed.
	reverseSimplification :: forall t . simplifier -> State t -> Model -> Model

-- | A simplifier that does no simplification
data IdSimplifir = IdSimplifier

instance Simplifier IdSimplifir where
	simplifyPC _ _ pc = [pc]
	reverseSimplification _ _ m = m