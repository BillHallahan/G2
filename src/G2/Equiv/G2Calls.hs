{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.G2Calls (runG2ForRewriteV) where

import G2.Config
import G2.Execution
import G2.Interface
import G2.Language
import G2.Solver

import Data.Text ()

-- get names from symbolic ids in the state
runG2ForRewriteV :: State () -> Config -> Bindings -> IO ([ExecRes ()], Bindings)
runG2ForRewriteV state config bindings = do
    SomeSolver solver <- initSolver config
    let simplifier = IdSimplifier
        sym_ids = symbolic_ids state
        sym_names = map idName sym_ids
        sym_config = addSearchNames (input_names bindings) emptyMemConfig

    (in_out, bindings') <- case rewriteRedHaltOrd solver simplifier config of
                (red, hal, ord) ->
                    runG2WithSomes red hal ord solver simplifier sym_config state bindings

    close solver

    return (in_out, bindings')

rewriteRedHaltOrd :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> Config -> (SomeReducer (), SomeHalter (), SomeOrderer ())
rewriteRedHaltOrd solver simplifier config =
    let
        share = sharing config

        tr_ng = mkNameGen ()
        state_name = Name "state" Nothing 0 Nothing
    in
    if higherOrderSolver config == AllFuncs
        then (SomeReducer (NonRedPCRed)
                 <~| (case logStates config of
                        Just fp -> SomeReducer (StdRed share solver simplifier :<~ ConcSymReducer :<~ Logger fp)
                        Nothing -> SomeReducer (StdRed share solver simplifier :<~ ConcSymReducer))
             , SomeHalter
                 (AcceptIfViolatedHalter)
             , SomeOrderer $ PickLeastUsedOrderer)
        else ( SomeReducer (NonRedPCRed :<~| TaggerRed state_name tr_ng)
                 <~| (case logStates config of
                        Just fp -> SomeReducer (StdRed share solver simplifier :<~ ConcSymReducer :<~ Logger fp)
                        Nothing -> SomeReducer (StdRed share solver simplifier :<~ ConcSymReducer))
             , SomeHalter
                 (DiscardIfAcceptedTag state_name
                 :<~> AcceptIfViolatedHalter)
             , SomeOrderer $ PickLeastUsedOrderer)

