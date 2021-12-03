{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Induction
    ( inductionFull
    , prevFiltered
    )
    where

-- TODO may not need all imports

import G2.Language

import G2.Config

import G2.Interface

import qualified Control.Monad.State.Lazy as CM

import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Typing as T
import qualified G2.Language.CallGraph as G

import Data.List
import Data.Maybe
import Data.Tuple
import qualified Data.Text as DT

import qualified Data.HashSet as HS
import qualified G2.Solver as S

import qualified G2.Language.PathConds as P

import G2.Equiv.InitRewrite
import G2.Equiv.EquivADT
import G2.Equiv.G2Calls
import G2.Equiv.Tactics

import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import G2.Execution.Memory
import Data.Monoid (Any (..))

import Debug.Trace

import G2.Execution.NormalForms
import qualified G2.Language.Stack as Stck
import Control.Monad

import Data.Time

import G2.Execution.Reducer
import G2.Lib.Printers

import qualified Control.Monad.Writer.Lazy as W

otherSide :: Side -> Side
otherSide ILeft = IRight
otherSide IRight = ILeft

-- TODO still getting bad induction summary results
reverseIndMarker :: IndMarker -> IndMarker
reverseIndMarker im = IndMarker {
    ind_real_present = swap $ ind_real_present im
  , ind_used_present = swap $ ind_used_present im
  , ind_past = swap $ ind_past im
  , ind_result = swap $ ind_result im
  , ind_present_scrutinees = swap $ ind_present_scrutinees im
  , ind_past_scrutinees = swap $ ind_past_scrutinees im
  , ind_side = otherSide $ ind_side im
  , ind_fresh_name = ind_fresh_name im
}

empty_name :: Name
empty_name = Name (DT.pack "") Nothing 1 Nothing

-- TODO keep track of case statements with no stamp
readStamps :: Expr -> [Name]
readStamps (Tick _ e) = readStamps e
readStamps (Case e i a) =
  case a of
    (Alt am1 a1):_ -> case a1 of
      Tick (NamedLoc n) _ -> n:(readStamps e)
      _ -> empty_name:(readStamps e)
    _ -> error "Empty Alt List"
readStamps _ = []

innerScrutinees :: Expr -> [Expr]
innerScrutinees (Tick _ e) = innerScrutinees e
innerScrutinees e@(Case e' _ _) = e:(innerScrutinees e')
innerScrutinees e = [e]

replaceScrutinee :: Expr -> Expr -> Expr -> Expr
replaceScrutinee e1 e2 e | e1 == e = e2
replaceScrutinee e1 e2 (Tick nl e) = Tick nl (replaceScrutinee e1 e2 e)
replaceScrutinee e1 e2 (Case e i a) = Case (replaceScrutinee e1 e2 e) i a
replaceScrutinee _ _ e = e

-- checking for depth of first expression within second
scrutineeDepth :: Expr -> Expr -> Int
scrutineeDepth e1 e2 | e1 == e2 = 0
scrutineeDepth e1 (Tick _ e) = scrutineeDepth e1 e
scrutineeDepth e1 (Case e i a) = 1 + scrutineeDepth e1 e
scrutineeDepth _ _ = error "Not Contained"

-- the depths do not need to be the same
-- however, the stamps should match up to the depth of the old one
validScrutinee :: StateET -> StateET -> StateET -> Bool
validScrutinee s p_inner p_outer =
  let d = scrutineeDepth (exprExtract p_inner) (exprExtract p_outer)
      stamps_old = take d $ readStamps (exprExtract p_outer)
      stamps_new = take d $ readStamps (exprExtract s)
  in stamps_old == stamps_new

innerScrutineeStates :: State t -> [State t]
innerScrutineeStates s@(State { curr_expr = CurrExpr _ e }) =
  map (\e' -> s { curr_expr = CurrExpr Evaluate e' }) (innerScrutinees e)

-- TODO keep track of the whole expression that was used for the inner scrutinee
moreRestrictiveIndRight :: S.Solver solver =>
                           solver ->
                           HS.HashSet Name ->
                           [(StateET, StateET)] ->
                           (StateET, StateET) ->
                           W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
moreRestrictiveIndRight solver ns prev (s1, s2) =
  let prev1 = map (\(p1, p2) -> (p1, p2, innerScrutineeStates p2)) prev
      prev2 = [(p1, p2', p2) | (p1, p2, p2l) <- prev1, p2' <- p2l]
  in moreRestrictivePairAux solver ns prev2 (s1, s2)

-- substitution happens on the left here; no right-side state returned
-- TODO collect information about the expressions used for induction
inductionL :: S.Solver solver =>
              solver ->
              HS.HashSet Name ->
              [(StateET, StateET)] ->
              (StateET, StateET) ->
              W.WriterT [Marker] IO (Bool, StateET, IndMarker)
inductionL solver ns prev (s1, s2) = do
  let scr1 = innerScrutinees $ exprExtract s1
      scr2 = innerScrutinees $ exprExtract s2
      scr_pairs = [(sc1, sc2) | sc1 <- scr1, sc2 <- scr2]
      scr_states = [(s1 { curr_expr = CurrExpr Evaluate sc1 }, s2 { curr_expr = CurrExpr Evaluate sc2 }) | (sc1, sc2) <- scr_pairs]
  mr_pairs <- mapM (moreRestrictiveIndRight solver ns prev) scr_states
  let mr_zipped = zip scr_pairs mr_pairs
      working_info = [(sc1, sc2, pm) | ((sc1, sc2), Just pm) <- mr_zipped]
      working_info' = filter (\(_, _, PrevMatch _ (_, p2) _ pc2) -> validScrutinee s2 p2 pc2) working_info
  case working_info' of
    [] -> return (False, s1, undefined)
    h:_ -> let (sc1, sc2, PrevMatch (q1, q2) (p1, p2) (mapping, _) pc2) = h
               e2_old = exprExtract pc2
               hm_list = HM.toList mapping
               e2_old' = foldr (\(i, e) acc -> replaceASTs (Var i) e acc) e2_old hm_list
               e1_new = replaceScrutinee sc1 e2_old' $ exprExtract s1
               h1_new = E.union (expr_env s1) (expr_env pc2)
               s1' = s1 {
                 curr_expr = CurrExpr Evaluate e1_new
               , expr_env = h1_new
               }
               -- TODO past
               -- TODO should result include generalization?
               -- TODO p1, p2, q1, q2, present scrutinees
               -- TODO do I really need q1 and q2?
               -- TODO placeholders for real present and name to avoid undefined errors
               im = IndMarker {
                 ind_real_present = (s1, s2)
               , ind_used_present = (s1, s2)
               , ind_past = (p1, pc2)
               , ind_result = (s1', s2)
               , ind_present_scrutinees = (sc1, sc2)
               , ind_past_scrutinees = (p1, p2)
               , ind_side = ILeft
               , ind_fresh_name = Name "" Nothing 0 Nothing
               }
           in return (True, s1', im)

-- precedence goes to left-side substitution
-- right-side substitution only happens if left-side fails
-- TODO reverse prev for the right side
-- TODO right-sided induction can happen here, even if it's called left
induction :: S.Solver solver =>
             solver ->
             HS.HashSet Name ->
             [(StateET, StateET)] ->
             (StateET, StateET) ->
             W.WriterT [Marker] IO (Bool, StateET, StateET, IndMarker)
induction solver ns prev (s1, s2) = do
  (bl, s1l, iml) <- inductionL solver ns prev (s1, s2)
  if bl then return (bl, s1l, s2, iml)
  else do
    let prev' = map swap prev
    (br, s2r, imr) <- inductionL solver ns prev' (s2, s1)
    return (br, s1, s2r, reverseIndMarker imr)

-- left side stays constant
-- TODO complex conditional, but avoids needless generalization
-- TODO returning marker in case of failure
inductionFoldL :: S.Solver solver =>
                  solver ->
                  HS.HashSet Name ->
                  Name ->
                  (StateH, StateH) ->
                  (StateET, StateET) ->
                  W.WriterT [Marker] IO (Int, StateET, StateET, IndMarker)
inductionFoldL solver ns fresh_name (sh1, sh2) (s1, s2) = do
  let prev = prevFiltered (sh1, sh2)
  (b, s1', s2', im) <- induction solver ns prev (s1, s2)
  if b then do
    (b', s1'', s2'') <- generalize solver ns fresh_name (s1', s2')
    if b' then return (length $ history sh2, s1'', s2'', im)
    else case history sh2 of
      [] -> return (-1, s1, s2, im)
      p2:_ -> inductionFoldL solver ns fresh_name (sh1, backtrackOne sh2) (s1, p2)
  else case history sh2 of
    [] -> return (-1, s1, s2, im)
    p2:_ -> inductionFoldL solver ns fresh_name (sh1, backtrackOne sh2) (s1, p2)

-- TODO somewhat crude solution:  record how "far back" it needed to go
-- negative one means that it failed
-- TODO only use histories from sh1 and sh2
-- TODO no induction without substitution now
-- TODO failure marker return
inductionFold :: S.Solver solver =>
                 solver ->
                 HS.HashSet Name ->
                 Name ->
                 (StateH, StateH) ->
                 (StateET, StateET) ->
                 W.WriterT [Marker] IO ((Int, Int), StateET, StateET)
inductionFold solver ns fresh_name (sh1, sh2) (s1, s2) = do
  (nl, s1l, s2l, iml) <- inductionFoldL solver ns fresh_name (sh1, sh2) (s1, s2)
  let length1 = length $ history sh1
      length2 = length $ history sh2
  if nl >= 0 then do
    W.liftIO $ putStrLn $ "IL " ++ show (map (folder_name . track) [s1, s2, s1l, s2l])
    let iml' = iml {
      ind_real_present = (s1, s2)
    , ind_fresh_name = fresh_name
    }
    W.tell $ [Marker (sh1, sh2) $ Induction iml']
    return ((0, length2 - nl), s1l, s2l)
  else do
    (nr, s2r, s1r, imr) <- inductionFoldL solver ns fresh_name (sh2, sh1) (s2, s1)
    if nr >= 0 then do
      W.liftIO $ putStrLn $ "IR " ++ show (map (folder_name . track) [s1, s2, s1r, s2r])
      -- TODO still reverse here?
      let imr' = reverseIndMarker (imr {
        ind_real_present = (s2, s1)
      , ind_fresh_name = fresh_name
      })
      W.tell $ [Marker (sh1, sh2) $ Induction imr']
      return ((length1 - nr, 0), s1r, s2r)
    else return ((-1, -1), s1, s2)

generalizeAux :: S.Solver solver =>
                 solver ->
                 HS.HashSet Name ->
                 [StateET] ->
                 StateET ->
                 W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
generalizeAux solver ns s1_list s2 = do
  let check_equiv s1_ = moreRestrictiveEquiv solver ns s1_ s2
  res <- mapM check_equiv s1_list
  let res' = filter isJust res
  case res' of
    [] -> return Nothing
    h:_ -> return h

-- TODO don't add stack ticks here; only do it before execution
adjustStateForGeneralization :: Expr -> Name -> StateET -> StateET
adjustStateForGeneralization e_old fresh_name s =
  let e = exprExtract s
      fresh_id = Id fresh_name (typeOf e)
      fresh_var = Var fresh_id
      e' = replaceScrutinee e fresh_var e_old
      h = expr_env s
      h' = E.insertSymbolic fresh_name fresh_id h
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
              W.WriterT [Marker] IO (Bool, StateET, StateET)
generalize solver ns fresh_name (s1, s2) = do
  W.liftIO $ putStrLn $ "Starting G " ++ show fresh_name
  W.liftIO $ putStrLn $ printHaskellDirty $ exprExtract s1
  W.liftIO $ putStrLn $ printHaskellDirty $ exprExtract s2
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
  W.liftIO $ putStrLn "Generalized"
  -- TODO expression environment adjustment?  Only for the fresh var
  -- TODO also may want to adjust the equivalence tracker
  let res' = filter isJust res
  case res' of
    (Just pm):_ -> let (s1', s2') = present pm
                       e1' = exprExtract s1'
                       s1'' = adjustStateForGeneralization e1 fresh_name s1'
                       s2'' = adjustStateForGeneralization e2 fresh_name s2'
                   in return (True, s1'', s2'')
    _ -> return (False, s1, s2)

-- TODO does this throw off history logging?  I don't think so
-- TODO might not matter with s1 and s2 naming
inductionFull :: S.Solver solver =>
                 solver ->
                 HS.HashSet Name ->
                 Name ->
                 (StateH, StateH) ->
                 (StateET, StateET) ->
                 W.WriterT [Marker] IO ((Int, Int), StateET, StateET)
inductionFull solver ns fresh_name sh_pair s_pair@(s1, s2) = do
  ((n1, n2), s1', s2') <- inductionFold solver ns fresh_name sh_pair s_pair
  if n1 < 0 || n2 < 0 then trace ("NO INDUCTION " ++ show n1) return ((n1, n2), s1, s2)
  else return ((n1, n2), s1', s2')
