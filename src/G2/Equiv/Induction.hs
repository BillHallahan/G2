{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Induction
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
                 HS.HashSet Name ->
                 [StateET] ->
                 StateET ->
                 W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
generalizeAux solver ns s1_list s2 = do
  -- TODO add lemmas here later?
  let check_equiv s1_ = moreRestrictiveEqual solver 0 ns emptyLemmas s1_ s2
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
              HS.HashSet Name ->
              Name ->
              (StateET, StateET) ->
              W.WriterT [Marker] IO (Maybe (StateET, StateET))
generalize solver ns fresh_name (s1, s2) | dc_path (track s1) == dc_path (track s2) = do
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
  res <- mapM (generalizeAux solver ns scr_states1) scr_states2
  -- TODO also may want to adjust the equivalence tracker
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
                   HS.HashSet Name ->
                   Name ->
                   [StateET] ->
                   StateET ->
                   W.WriterT [Marker] IO (Maybe (StateET, StateET, StateET, StateET))
generalizeFoldL solver ns fresh_name prev2 s1 = do
  case prev2 of
    [] -> return Nothing
    p2:t -> do
      gen <- generalize solver ns fresh_name (s1, p2)
      case gen of
        Just (s1', s2') -> return $ Just (s1, p2, s1', s2')
        _ -> generalizeFoldL solver ns fresh_name t s1

-- TODO make a new marker type for this?
generalizeFold :: S.Solver solver =>
                  solver ->
                  HS.HashSet Name ->
                  Name ->
                  (StateH, StateH) ->
                  (StateET, StateET) ->
                  W.WriterT [Marker] IO (Maybe (StateET, StateET, StateET, StateET))
generalizeFold solver ns fresh_name (sh1, sh2) (s1, s2) = do
  fl <- generalizeFoldL solver ns fresh_name (s2:history sh2) s1
  case fl of
    Just _ -> return fl
    Nothing -> do
      fr <- generalizeFoldL solver ns fresh_name (s1:history sh1) s2
      case fr of
        Just (q2, q1, q2', q1') -> return $ Just (q1, q2, q1', q2')
        Nothing -> return Nothing

generalizeFull :: S.Solver s => Tactic s
generalizeFull solver _ ns _ (fresh_name:_) sh_pair s_pair = do
  gfold <- generalizeFold solver ns fresh_name sh_pair s_pair
  case gfold of
    Nothing -> return $ NoProof []
    Just (s1, s2, q1, q2) -> let lem = mkProposedLemma "Generalization" s1 s2 q1 q2
                             in return $ NoProof $ [lem]
generalizeFull _ _ _ _ _ _ _ = return $ NoProof []
