module G2.Liquid.Inference.Sygus.UnsatCoreElim (unsatCoreElim) where

import Sygus.Syntax

import Data.Maybe

-- | Eliminates negative constraints that would lead to an unsat core
unsatCoreElim :: [Cmd] -> [Cmd]
unsatCoreElim cmds =
    let
        true_terms = mapMaybe getTrueTerm cmds
    in
    mapMaybe (unsatCoreElim' true_terms) cmds

unsatCoreElim' :: [Term] -> Cmd -> Maybe Cmd
unsatCoreElim' ts cmd@(Constraint t) =
    if mustBeFalse ts t then Nothing else Just cmd
unsatCoreElim' _ cmd = Just cmd

mustBeFalse :: [Term] -> Term -> Bool
mustBeFalse ts c@(TermCall (ISymb "=>") [t1, t2]) =
    mustBeTrue ts t1 && mustBeFalse ts t2
mustBeFalse ts (TermCall (ISymb "not") [t1]) = mustBeTrue ts t1
mustBeFalse ts (TermCall (ISymb "and") and_ts) = any (mustBeFalse ts) and_ts
mustBeFalse ts (TermLit (LitBool False)) = True
mustBeFalse ts _ = False

mustBeTrue :: [Term] -> Term -> Bool
mustBeTrue ts c@(TermCall (ISymb "=>") [t1, t2]) = mustBeFalse ts t1 || mustBeTrue ts t2
mustBeTrue ts (TermCall (ISymb "and") and_ts) = all (mustBeTrue ts) and_ts
mustBeTrue ts (TermLit (LitBool True)) = True
mustBeTrue ts t = t `elem` ts
mustBeTrue ts _ = False

getTrueTerm :: Cmd -> Maybe Term
getTrueTerm (Constraint t) = Just t
getTrueTerm _ = Nothing
