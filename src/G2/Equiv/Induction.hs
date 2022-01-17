{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Induction
    ( inductionFull
    , prevFiltered
    , generalizeFull
    )
    where

-- TODO may not need all imports

import G2.Language

import G2.Config

import G2.Interface

import qualified G2.Language.ExprEnv as E

import Data.List
import Data.Maybe
import Data.Tuple
import qualified Data.Text as DT

import qualified Data.HashSet as HS
import qualified G2.Solver as S

import G2.Equiv.InitRewrite
import G2.Equiv.EquivADT
import G2.Equiv.G2Calls
import G2.Equiv.Tactics

import qualified Data.HashMap.Lazy as HM
import G2.Execution.Memory
import Data.Monoid (Any (..))

import Debug.Trace

import G2.Execution.NormalForms
import Control.Monad

import Data.Either.Extra
import Data.Time

import G2.Execution.Reducer
import G2.Lib.Printers

import qualified Control.Monad.Writer.Lazy as W

otherSide :: Side -> Side
otherSide ILeft = IRight
otherSide IRight = ILeft

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

-- the output list includes entries for case statements with no stamp
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

-- This tries to find a pair of previously-encountered states that match the
-- present state pair.  Rather than simply using the right-hand present state's
-- current expression as it really is, this function attempts to find matches
-- with all of the different "inner scrutinees" on the right-hand side.  The
-- left-hand present state's expression stays constant, though.
moreRestrictiveIndRight :: S.Solver solver =>
                           solver ->
                           HS.HashSet Name ->
                           [(StateET, StateET)] ->
                           (StateET, StateET) ->
                           W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
moreRestrictiveIndRight solver ns prev (s1, s2) =
  let prev1 = map (\(p1, p2) -> (p1, p2, innerScrutineeStates p2)) prev
      prev2 = [(p1, p2', p2) | (p1, p2, p2l) <- prev1, p2' <- p2l]
  in
  return . eitherToMaybe =<< moreRestrictivePairAux solver ns prev2 (s1, s2)

-- substitution happens on the left here; no right-side state returned
inductionL :: S.Solver solver =>
              solver ->
              HS.HashSet Name ->
              [(StateET, StateET)] ->
              (StateET, StateET) ->
              W.WriterT [Marker] IO (Maybe (StateET, IndMarker))
inductionL solver ns prev (s1, s2) = do
  let scr1 = innerScrutinees $ exprExtract s1
      scr2 = innerScrutinees $ exprExtract s2
      scr_pairs = [(sc1, sc2) | sc1 <- scr1, sc2 <- scr2]
  mr_pairs <- mapM (\(sc1, sc2) -> do
                      let s1_ = s1 { curr_expr = CurrExpr Evaluate sc1 }
                          s2_ = s2 { curr_expr = CurrExpr Evaluate sc2 }
                      moreRestrictiveIndRight solver ns prev (s1_, s2_)) scr_pairs
  let mr_zipped = zip scr_pairs mr_pairs
      working_info = [(sc1, sc2, pm) | ((sc1, sc2), Just pm) <- mr_zipped]
      working_info' = filter (\(_, _, PrevMatch _ (_, p2) _ p_outer2) -> validScrutinee s2 p2 p_outer2) working_info
  case working_info' of
    [] -> return Nothing
    h:_ -> let (sc1, sc2, PrevMatch _ (p1, p2) (mapping, _) p_outer2) = h
               e2_old = exprExtract p_outer2
               mapping_list = HM.toList mapping
               e2_old' = foldr (\(i, e) acc -> replaceASTs (Var i) e acc) e2_old mapping_list
               e1_new = replaceScrutinee sc1 e2_old' $ exprExtract s1
               h1_new = E.union (expr_env s1) (expr_env p_outer2)
               s1' = s1 {
                 curr_expr = CurrExpr Evaluate e1_new
               , expr_env = h1_new
               }
               -- TODO should result include generalization?
               -- TODO p1, p2, q1, q2, present scrutinees
               -- placeholders for real present and name to avoid undefined errors
               im = IndMarker {
                 ind_real_present = (s1, s2)
               , ind_used_present = (s1, s2)
               , ind_past = (p1, p_outer2)
               , ind_result = (s1', s2)
               , ind_present_scrutinees = (sc1, sc2)
               , ind_past_scrutinees = (p1, p2)
               , ind_side = ILeft
               , ind_fresh_name = Name "" Nothing 0 Nothing
               }
           in return $ Just (s1', im)

-- TODO check the criterion at a different level
-- only attempt induction if we have recursion in the right spots in the present
-- TODO be more generous instead; try induction whenever there's a Case
caseRecursion :: Expr -> Bool
caseRecursion (Tick _ e) = caseRecursion e
caseRecursion (Case e _ _) =
  (getAny . evalASTs (\e' -> Any $ caseRecHelper e')) e
caseRecursion _ = False

-- TODO this shouldn't need to look more deeply since it's used with evalASTs
caseRecHelper :: Expr -> Bool
caseRecHelper (Tick (NamedLoc (Name t _ _ _)) _) = t == DT.pack "REC"
caseRecHelper _ = False

-- This attempts to perform induction on both the left side and the right side.
-- Precedence goes to the left side:  induction will only happen on the right
-- if induction on the left fails.
-- We only apply induction to a pair of expressions if both expressions are
-- Case statements whose scrutinee includes a recursive function or variable
-- use.  Induction is sound as long as the two expressions are Case statements,
-- but, if no recursion is involved, ordinary coinduction is just as useful.
-- We prefer coinduction in that scenario because it is more efficient.
-- TODO (12/9) As a slight optimization, I could avoid using coinduction in
-- situations like this where induction is applicable.
induction :: S.Solver solver =>
             solver ->
             HS.HashSet Name ->
             [(StateET, StateET)] ->
             (StateET, StateET) ->
             W.WriterT [Marker] IO (Maybe (StateET, StateET, IndMarker))
induction solver ns prev (s1, s2) | caseRecursion (exprExtract s1)
                                  , caseRecursion (exprExtract s2) = do
  ind <- inductionL solver ns prev (s1, s2)
  case ind of
    Just (s1l, iml) -> return $ Just (s1l, s2, iml)
    Nothing -> do
      let prev' = map swap prev
      ind' <- inductionL solver ns prev' (s2, s1)
      case ind' of
        Just (s2r, imr) -> return $ Just (s1, s2r, reverseIndMarker imr)
        Nothing -> return Nothing
  | otherwise = return Nothing

-- TODO complex conditional, but avoids needless generalization
-- TODO returning marker in case of failure
-- This attempts to perform both left-side and right-side induction with
-- multiple different combinations of present states.  The actual substitution
-- for induction can happen on either side.  All of the present-state
-- combinations tried have the same left-hand state, but the right-hand state
-- varies between attempts.
inductionFoldL :: S.Solver solver =>
                  solver ->
                  HS.HashSet Name ->
                  Name ->
                  (StateH, StateH) ->
                  (StateET, StateET) ->
                  W.WriterT [Marker] IO (Maybe (Int, StateET, StateET, IndMarker))
inductionFoldL solver ns fresh_name (sh1, sh2) (s1, s2) = do
  let prev = prevFiltered (sh1, sh2)
  ind <- induction solver ns prev (s1, s2)
  case ind of
    Nothing -> case backtrackOne sh2 of
      Nothing -> return Nothing
      Just sh2' -> inductionFoldL solver ns fresh_name (sh1, sh2') (s1, latest sh2')
    Just (s1', s2', im) -> do
      g <- generalize solver ns fresh_name (s1', s2')
      case g of
        Nothing -> case backtrackOne sh2 of
          Nothing -> return Nothing
          Just sh2' -> inductionFoldL solver ns fresh_name (sh1, sh2') (s1, latest sh2')
        Just (s1'', s2'') -> return $ Just (length $ history sh2, s1'', s2'', im)

-- TODO somewhat crude solution:  record how "far back" it needed to go
-- This tries all of the possible combinations of present states for induction.
-- First it tries using the real left-hand present state with all of the
-- right-hand states.  If none of those work, the function tries all of the
-- left-hand states with the real right-hand present state.  There is no need
-- to try combinations where both the left-hand state and the right-hand state
-- come from the past:  any such combination would have been tried during a
-- previous loop iteration.
-- TODO Right now, we only try induction on a state pair if both of the real
-- present states fit the pattern for induction.  Should we have a looser
-- requirement instead?
inductionFold :: S.Solver solver =>
                 solver ->
                 HS.HashSet Name ->
                 Name ->
                 (StateH, StateH) ->
                 (StateET, StateET) ->
                 W.WriterT [Marker] IO (Maybe ((Int, Int), StateET, StateET))
inductionFold solver ns fresh_name (sh1, sh2) (s1, s2) = do
  fl <- inductionFoldL solver ns fresh_name (sh1, sh2) (s1, s2)
  case fl of
    Just (nl, s1l, s2l, iml) -> do
      W.liftIO $ putStrLn $ "IL " ++ show (map (folder_name . track) [s1, s2, s1l, s2l])
      let iml' = iml {
        ind_real_present = (s1, s2)
      , ind_fresh_name = fresh_name
      }
      W.tell $ [Marker (sh1, sh2) $ Induction iml']
      return $ Just ((0, (length $ history sh2) - nl), s1l, s2l)
    Nothing -> do
      fr <- inductionFoldL solver ns fresh_name (sh2, sh1) (s2, s1)
      case fr of
        Just (nr, s2r, s1r, imr) -> do
          W.liftIO $ putStrLn $ "IR " ++ show (map (folder_name . track) [s1, s2, s1r, s2r])
          let imr' = reverseIndMarker (imr {
            ind_real_present = (s2, s1)
          , ind_fresh_name = fresh_name
          })
          W.tell $ [Marker (sh1, sh2) $ Induction imr']
          return $ Just (((length $ history sh1) - nr, 0), s1r, s2r)
        Nothing -> return Nothing

generalizeAux :: S.Solver solver =>
                 solver ->
                 HS.HashSet Name ->
                 [StateET] ->
                 StateET ->
                 W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
generalizeAux solver ns s1_list s2 = do
  -- TODO add lemmas here later?
  let check_equiv s1_ = moreRestrictiveEqual solver ns emptyLemmas s1_ s2
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
generalize solver ns fresh_name (s1, s2) = do
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
                       e1' = exprExtract s1'
                       s1'' = adjustStateForGeneralization e1 fresh_name s1'
                       s2'' = adjustStateForGeneralization e2 fresh_name s2'
                   in return $ Just (s1'', s2'')
    _ -> return Nothing

-- TODO does this throw off history logging?  I don't think so
-- TODO might not matter with s1 and s2 naming
-- TODO needs at least one fresh name
inductionFull :: S.Solver s => Tactic s
inductionFull solver ns _ (fresh_name:_) sh_pair s_pair = do
  ifold <- inductionFold solver ns fresh_name sh_pair s_pair
  case ifold of
    Nothing -> return $ NoProof HS.empty
    Just ((n1, n2), s1', s2') -> return $ Success (Just (n1, n2, s1', s2'))
inductionFull _ _ _ _ _ _ = return $ NoProof HS.empty

-- TODO new functions for generalization without induction
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
-- TODO make this more like equalFold?
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
    Just (q1, q2, q1', q2') -> return fl
    Nothing -> do
      fr <- generalizeFoldL solver ns fresh_name (s1:history sh1) s2
      case fr of
        Just (q2, q1, q2', q1') -> return $ Just (q1, q2, q1', q2')
        Nothing -> return Nothing

-- TODO this should come before induction in the list of tactics
-- TODO this uses the same fresh name that induction uses currently
generalizeFull :: S.Solver s => Tactic s
generalizeFull solver ns _ (fresh_name:_) sh_pair s_pair = do
  gfold <- generalizeFold solver ns fresh_name sh_pair s_pair
  case gfold of
    Nothing -> return $ NoProof HS.empty
    Just (s1, s2, q1, q2) -> let lem = mkPropEquivLemma "Generalization" s1 s2 q1 q2
                             in return $ NoProof $ HS.singleton lem
generalizeFull _ _ _ _ _ _ = return $ NoProof HS.empty
