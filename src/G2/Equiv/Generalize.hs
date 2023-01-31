{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Generalize
    ( prevFiltered
    , generalizeFull
    )
    where

import G2.Language

import qualified G2.Language.ExprEnv as E

import Data.Maybe

import qualified Data.HashSet as HS
import qualified G2.Solver as S

import G2.Equiv.G2Calls
import G2.Equiv.Tactics

import Data.Monoid (Any (..))

import qualified Control.Monad.Writer.Lazy as W

innerScrutinees :: Expr -> [Expr]
innerScrutinees (Tick _ e) = innerScrutinees e
innerScrutinees e@(Case e' _ _ _) = e:(innerScrutinees e')
innerScrutinees e = [e]

replaceScrutinee :: Expr -> Expr -> Expr -> Expr
replaceScrutinee e1 e2 e | e1 == e = e2
replaceScrutinee e1 e2 (Tick nl e) = Tick nl (replaceScrutinee e1 e2 e)
replaceScrutinee e1 e2 (Case e i t a) = Case (replaceScrutinee e1 e2 e) i t a
replaceScrutinee _ _ e = e

generalizeAux :: S.Solver solver =>
                 solver ->
                 Int ->
                 HS.HashSet Name ->
                 Lemmas ->
                 [StateET] ->
                 StateET ->
                 W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
generalizeAux solver num_lems ns lemmas s1_list s2 = do
  -- Originally, this equality check did not allow for lemma usage
  -- because it was supposed to check only for syntactic equality.
  -- However, there do not seem to be any soundness issues with
  -- enabling lemma usage here to make the tactic more powerful.
  let check_equiv s1_ = moreRestrictiveEqual solver num_lems ns lemmas s1_ s2
  res <- mapM check_equiv s1_list
  let res' = filter isJust res
  case res' of
    [] -> return Nothing
    h:_ -> return h

adjustStateForGeneralization :: Expr -> Name -> StateET -> StateET
adjustStateForGeneralization e_old fresh_name s =
  let e = exprExtract s
      fresh_id = Id fresh_name (typeOf e)
      fresh_var = Var fresh_id
      e' = replaceScrutinee e fresh_var e_old
      h = expr_env s
      h' = E.insertSymbolic fresh_id h
  in s {
    curr_expr = CurrExpr Evaluate e'
  , expr_env = h'
  }

-- replace the largest sub-expression possible with a fresh symbolic var
generalize :: S.Solver solver =>
              solver ->
              Int ->
              HS.HashSet Name ->
              Lemmas ->
              Name ->
              (StateET, StateET) ->
              W.WriterT [Marker] IO (Maybe (StateET, StateET))
generalize solver num_lems ns lemmas fresh_name (s1, s2) | dc_path (track s1) == dc_path (track s2) = do
  -- expressions are ordered from outer to inner
  -- the largest ones are on the outside
  -- take the earliest array entry that works
  -- for anything on one side, there can only be one match on the other side
  let e1 = exprExtract s1
      scr1 = innerScrutinees e1
      scr_states1 = map (\e -> s1 { curr_expr = CurrExpr Evaluate e }) scr1
      e2 = exprExtract s2
      scr2 = innerScrutinees e2
      scr_states2 = map (\e -> s2 { curr_expr = CurrExpr Evaluate e }) scr2
  res <- mapM (generalizeAux solver num_lems ns lemmas scr_states1) scr_states2
  -- no equiv tracker changes seem to be necessary
  let res' = filter isJust res
  case res' of
    (Just pm):_ -> let (s1', s2') = present pm
                       s1'' = adjustStateForGeneralization e1 fresh_name s1'
                       s2'' = adjustStateForGeneralization e2 fresh_name s2'
                   in return $ Just $ syncSymbolic s1'' s2''
    _ -> return Nothing
  | otherwise = return Nothing

generalizeFoldL :: S.Solver solver =>
                   solver ->
                   Int ->
                   HS.HashSet Name ->
                   Lemmas ->
                   Name ->
                   [StateET] ->
                   StateET ->
                   W.WriterT [Marker] IO (Maybe (StateET, StateET, StateET, StateET))
generalizeFoldL solver num_lems ns lemmas fresh_name prev2 s1 = do
  case prev2 of
    [] -> return Nothing
    p2:t -> do
      gen <- generalize solver num_lems ns lemmas fresh_name (s1, p2)
      case gen of
        Just (s1', s2') -> return $ Just (s1, p2, s1', s2')
        _ -> generalizeFoldL solver num_lems ns lemmas fresh_name t s1

generalizeFold :: S.Solver solver =>
                  solver ->
                  Int ->
                  HS.HashSet Name ->
                  Lemmas ->
                  Name ->
                  (StateH, StateH) ->
                  (StateET, StateET) ->
                  W.WriterT [Marker] IO (Maybe (StateET, StateET, StateET, StateET))
generalizeFold solver num_lems ns lemmas fresh_name (sh1, sh2) (s1, s2) = do
  fl <- generalizeFoldL solver num_lems ns lemmas fresh_name (s2:history sh2) s1
  case fl of
    Just _ -> return fl
    Nothing -> do
      fr <- generalizeFoldL solver num_lems ns lemmas fresh_name (s1:history sh1) s2
      case fr of
        Just (q2, q1, q2', q1') -> return $ Just (q1, q2, q1', q2')
        Nothing -> return Nothing

generalizeFull :: S.Solver s => Tactic s
generalizeFull solver num_lems ns lemmas (fresh_name:_) sh_pair s_pair = do
  gfold <- generalizeFold solver num_lems ns lemmas fresh_name sh_pair s_pair
  case gfold of
    Nothing -> return $ NoProof []
    Just (s1, s2, q1, q2) -> let lem = mkProposedLemma "Generalization" s1 s2 q1 q2
                             in return $ NoProof $ [lem]
generalizeFull _ _ _ _ _ _ _ = return $ NoProof []

-- TODO new tactics, somewhat like generalization
-- make lemmas from arbitrary sub-expression pairs
-- should these lemmas have access to history?

-- notes from 1/19/23
{-
The goal is to allow Nebula to handle theorems like p47 from the Zeno
suite.  Simply increasing the number of lemmas that can be applied at once
is not sufficient.  For p47, the expressions that would need to be paired
with each other for lemmas do not align nicely.  The mirror function
rearranges the symbolic variables in an inconvenient way.

A new possible system for generating lemmas is to search for pairs of
sub-expressions of the same type between the two sides.  Most combinations
would be useless, so, presumably, we would require two paired
sub-expressions to have at least one non-concretized symbolic variable in
common.

For p47 at least, a lemma system like this may not be sufficient.  For
p47, the useful lemmas that would be formed by this are equivalent to the
original rule.  This wouldn't present an opportunity for coinduction
because lemmas don't have access to the histories of the state pairs that
spawn them.

It is possible that we could create a new kind of lemma that uses the
history of the state pair that spawned it in a sound way.  It could be an
"alternative proof obligation" or something like that.

However, the mere existence of a sub-expression that reduces to something
that looks like the original expression doesn't necessarily give us
anything valuable.  That sub-expression could be unreachable.  I would
need a more thorough set of requirements for soundness.

If I break up function application obligations, it might be sound, but
that won't work directly for p47 because of mirror.

(1/20) Maybe I need a "generalized" version of the generalization lemmas
that I have now in order to prove p47.  Would that allow me to get
something like "max a b = max b a" as a lemma for p47?

It seems that the answer is no.  For p47, there's no point when we have
"max a b" on one side when "max b a" is on the other side.  The mirror
function really throws everything off.

For p58, on the right-hand side, we keep getting more and more successors
along with more and more list elements.  This keeps us hung up evaluating
drop forever.  More specifically, the drop application in the scrutinee
of the outermost case statement gets stuck evaluating forever.

Why can't a lemma take care of the issue?  I should be able to apply two
lemmas here to get the approximation that I want, one for the outermost
drop application and one for the inner drop application.

A lot of the unresolved lemmas that I'm seeing aren't actually true.  All
of them involve drop, but they're trying to prove equivalences that are
not correct.  More importantly, the things that I want to line up with
lemmas aren't equivalent to each other.  For the outer drop application,
things are equivalent, but they aren't for the inner one.

Actually, I could prove this with only one lemma, but that lemma isn't
being generated, I think.  I want something like this:

drop1 a (S fs9) (fs12:fs17) = drop1 a fs9 fs17

If I applied that to the outer drop application in b9, I could get a
correspondence between b2 and b9.  What would cause Nebula to generate
that lemma?  It would be good to have a general approach that isn't
overfitted to p58.

Effectively, this lemma would just be undoing evaluation steps, wouldn't
it?  Is that a problem?  Would it be unsound to use lemmas like this?
This would be unguarded coinduction rather than guarded coinduction.
Neither b2 nor b9 is in SWHNF, but the left-hand states would both be in
SWHNF because they're [].  That throws off unguarded coinduction.  Are
b2 and b9 in distinct blocks?  They shouldn't be in distinct blocks since
no constructors are getting removed on the left-hand side.  The left side
is just stuck at [] with no change.

There will never be any new blocks formed for this theorem on the
unresolved branches that I can see.  This puts me in an awkward
situation.  I need to do guarded coinduction because of the left side,
but the inability to make new blocks makes it impossible to do guarded
coinduction at all.

TODO p58 is misclassified.  It requires finiteness.  Check the other
theorems that are listed as requiring totality but not finiteness.

p47:  genuine, I think
p58:  n infinite, xs infinite, ys empty
p72
p73
p74
p83
p84

I can get a relatively high depth for p04fin.  Is this another situation
like what I had for p58?

(1/30) Can I use something like my new technique for finding cycle
counterexamples to help with p47?  I can't just look for cycles within
scrutinees.

I think p04 is an easier target.  I can see the spots where lemma
substitution would be helpful, but the things that get generated as
lemma candidates aren't really true.
-}

-- TODO do I have functions like this already?
-- get the list of symbolic variables contained in an expression
-- there is printVars in the summary file
-- varsFullList and varsFull, also varsInExpr
getSymVars :: Expr -> [Name]
getSymVars = error "TODO"
