{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.G2Calls ( StateET
                        , emptyEquivTracker
                        , runG2ForRewriteV) where

import G2.Config
import G2.Execution
import G2.Interface
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Solver

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Text ()

import Debug.Trace

-- get names from symbolic ids in the state
runG2ForRewriteV :: StateET -> Config -> Bindings -> IO ([ExecRes EquivTracker], Bindings)
runG2ForRewriteV state config bindings = do
    SomeSolver solver <- initSolver config
    let simplifier = IdSimplifier
        sym_ids = symbolic_ids state
        sym_names = map idName sym_ids
        sym_config = addSearchNames (names $ track state)
                   $ addSearchNames (input_names bindings) emptyMemConfig

    (in_out, bindings') <- case rewriteRedHaltOrd solver simplifier config of
                (red, hal, ord) ->
                    runG2WithSomes red hal ord solver simplifier sym_config state bindings

    close solver

    return (in_out, bindings')

rewriteRedHaltOrd :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> Config -> (SomeReducer EquivTracker, SomeHalter EquivTracker, SomeOrderer EquivTracker)
rewriteRedHaltOrd solver simplifier config =
    let
        share = sharing config

        tr_ng = mkNameGen ()
        state_name = Name "state" Nothing 0 Nothing
    in
    (case logStates config of
            Just fp -> SomeReducer (StdRed share solver simplifier :<~ ConcSymReducer :<~? (Logger fp :<~ EquivReducer))
            Nothing -> SomeReducer (StdRed share solver simplifier :<~ ConcSymReducer :<~? EquivReducer)
     , SomeHalter
         (DiscardIfAcceptedTag state_name
         :<~> GuardedHalter)
     , SomeOrderer $ PickLeastUsedOrderer)

type StateET = State EquivTracker

-- Maps higher order function calles to symbolic replacements.
-- This allows the same call to be replaced by the same Id consistently.
newtype EquivTracker = EquivTracker (HM.HashMap Expr Id) deriving Show

emptyEquivTracker :: EquivTracker
emptyEquivTracker = EquivTracker HM.empty

data EquivReducer = EquivReducer

instance Reducer EquivReducer () EquivTracker where
    initReducer _ _ = ()
    redRules r _ s@(State { expr_env = eenv
                          , curr_expr = CurrExpr Evaluate e
                          , symbolic_ids = symbs
                          , track = EquivTracker et })
                 b@(Bindings { name_gen = ng })
        | isSymFuncApp eenv e =
            let
                -- We inline variables to have a higher chance of hitting in the Equiv Tracker
                e' = inlineApp eenv e
            in
            case HM.lookup e' et of
                Just v ->
                    let
                        s' = s { curr_expr = CurrExpr Evaluate (Var v) }
                    in
                    return (InProgress, [(s', ())], b, r)
                Nothing ->
                    let
                        (v, ng') = freshId (typeOf e) ng
                        et' = HM.insert e' v et
                        s' = s { curr_expr = CurrExpr Evaluate (Var v)
                               , track = EquivTracker et'
                               , expr_env = E.insertSymbolic (idName v) v eenv
                               , symbolic_ids = v:symbs }
                        b' = b { name_gen = ng' }
                    in
                    return (InProgress, [(s', ())], b', r)
    redRules r rv s b = return (NoProgress, [(s, rv)], b, r)

isSymFuncApp :: ExprEnv -> Expr -> Bool
isSymFuncApp eenv e
    | Var (Id f t):es@(_:_) <- unApp e = E.isSymbolic f eenv && hasFuncType (PresType t)
    | otherwise = False

inlineApp :: ExprEnv -> Expr -> Expr
inlineApp eenv = mkApp . map (inlineVars eenv) . unApp

inlineVars :: ExprEnv -> Expr -> Expr
inlineVars = inlineVars' HS.empty

inlineVars' :: HS.HashSet Name -> ExprEnv -> Expr -> Expr
inlineVars' seen eenv (Var (Id n _))
    | not (n `HS.member` seen)
    , Just e <- E.lookup n eenv = inlineVars' (HS.insert n seen) eenv e
inlineVars' seen eenv (App e1 e2) = App (inlineVars' seen eenv e1) (inlineVars' seen eenv e2)
inlineVars' _ _ e = e

instance ASTContainer EquivTracker Expr where
    containedASTs (EquivTracker hm) = HM.keys hm
    modifyContainedASTs f (EquivTracker hm) =
        EquivTracker . HM.fromList . map (\(k, v) -> (f k, v)) $ HM.toList hm

instance ASTContainer EquivTracker Type where
    containedASTs (EquivTracker hm) = containedASTs $ HM.keys hm
    modifyContainedASTs f (EquivTracker hm) =
          EquivTracker
        . HM.fromList
        . map (\(k, v) -> (modifyContainedASTs f k, modifyContainedASTs f v))
        $ HM.toList hm

instance Named EquivTracker where
    names (EquivTracker hm) = names hm
    rename old new (EquivTracker hm) = EquivTracker $ rename old new hm
