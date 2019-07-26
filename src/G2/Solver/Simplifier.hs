{-# LANGUAGE RankNTypes #-}

module G2.Solver.Simplifier ( Simplifier (..)
							, IdSimplifir (..)) where

import G2.Language

class Simplifier simplifier where
	simplifyPC :: forall t . simplifier -> State t -> PathCond -> [PathCond]

	reverseSimplification :: forall t . simplifier -> State t -> Model -> Model

-- | A simplifier that does no simplification
data IdSimplifir = IdSimplifier

instance Simplifier IdSimplifir where
	simplifyPC _ _ pc = [pc]
	reverseSimplification _ _ m = m