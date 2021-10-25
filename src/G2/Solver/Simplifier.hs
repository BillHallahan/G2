{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Solver.Simplifier ( Simplifier (..)
                            , IdSimplifier (..)
                            , CombineSimplifiers (..)
                            , EliminateAssumePCs (..)) where

import G2.Language
import qualified G2.Language.PathConds as PC

import Data.List
import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.Maybe
import Data.Tuple

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

data CombineSimplifiers a b = a :<< b

instance (Simplifier a, Simplifier b) => Simplifier (CombineSimplifiers a b) where
    simplifyPC (a :<< b) s pc =
        let
            (s', pcs) = simplifyPC b s pc
            (s'', pcs') = mapAccumL (simplifyPC a) s' pcs
        in
        (s'', concat pcs')

    simplifyPCs (a :<< b) s pc pcs = simplifyPCs a s pc $ simplifyPCs b s pc pcs

    reverseSimplification (a :<< b) s binds m = reverseSimplification a s binds $ reverseSimplification b s binds m

-- Eliminates AssumePC's when the Id is set
data EliminateAssumePCs = EliminateAssumePCs

instance Simplifier EliminateAssumePCs where
    -- | Simplifies a PC, by converting it to a form that is easier for the Solver's to handle
    simplifyPC _ s pc = (s, [pc])

    simplifyPCs _ _ (AltCond (LitInt n) (Var i) True) pcs =
        PC.unionAlterHashed (simpAssumePC i n) pcs
    simplifyPCs _ _ (ExtCond (App (App (Prim Eq _) x) y) True) pcs
        | Var i <- x
        , Lit (LitInt n) <- y = PC.unionAlterHashed (simpAssumePC i n) pcs
    simplifyPCs _ _ (ExtCond (App (App (Prim Eq _) x) y) True) pcs
        | Var i <- y
        , Lit (LitInt n) <- x = PC.unionAlterHashed (simpAssumePC i n) pcs
    simplifyPCs _ _ _ pcs = pcs

    -- | Reverses the affect of simplification in the model, if needed.
    reverseSimplification _ _ _ = id

simpAssumePC :: Id -> Integer -> PC.HashedPathCond -> HS.HashSet PC.HashedPathCond
simpAssumePC i n exc
    | ExtCond (App (App (Prim Implies _) x) y) True <- PC.unhashedPC exc =
        case x of
            (App (App (Prim Eq _) e1) e2)
                | Lit (LitInt n') <- e1
                , Var i' <- e2 -> simpAssumePC' i n i' n' . PC.hashedPC $ ExtCond y True
                | Lit (LitInt n') <- e2
                , Var i' <- e1 -> simpAssumePC' i n i' n' . PC.hashedPC $ ExtCond y True
            _ -> HS.singleton exc
simpAssumePC i n p
    | AssumePC i' n' pc <- PC.unhashedPC p = simpAssumePCHS i n i' n' (PC.unhashedHHS pc)
simpAssumePC _ _ pc = HS.singleton pc

simpAssumePC' :: Id -> Integer -> Id -> Integer -> PC.HashedPathCond -> HS.HashSet PC.HashedPathCond
simpAssumePC' i n i' n' pc
    | i == i' && n == n' = HS.singleton pc
    | i == i' && n /= n' = HS.empty
    | otherwise =
        let
            pc' = simpAssumePC i n pc
        in
        if HS.null pc' then HS.empty else HS.singleton (PC.hashedPC (PC.mkAssumePC i' n' pc'))

simpAssumePCHS :: Id -> Integer -> Id -> Integer -> HS.HashSet PC.HashedPathCond -> HS.HashSet PC.HashedPathCond
simpAssumePCHS i n i' n' pc
    | i == i' && n == n' = pc
    | i == i' && n /= n' = HS.empty
    | otherwise =
        let
            pc' = foldl' HS.union HS.empty $ HS.map (simpAssumePC i n) pc
        in
        if HS.null pc' then HS.empty else HS.singleton (PC.hashedPC (PC.mkAssumePC i' n' pc'))
