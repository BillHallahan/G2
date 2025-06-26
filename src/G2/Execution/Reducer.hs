{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, MultiWayIf, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE TupleSections, UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}

{-| Module: G2.Execution.Reducer

Provides utilities to customize and abstract over the reduction of `State`s.
The key idea is that we can split the process of reducing states into three separate choices:
* What does it mean to reduce a State? What reduction rules do we use?
* When do we stop reducing a State?  Either because we want to (temporarily) reduce a different State instead,
or because we are finished reducing the State.
* Given a number of States, which State should we reduce first?

These three points are addressed, respectively, by `Reducer`s, `Halter`s, and `Orderer`s.  
The `Reducer` defines the reduction rules used to map a State to one or more further States.
The `Halter` determines when to accept (return) or completely discard a state,
and allows /temporarily/ stopping reduction of a particular state, to allow reduction of other states.
The `Orderer` determines which state should be executed next when the Halter chooses to accept, reject,
or switch to executing a different state.

The `runReducer` function reduces States, guided by a `Reducer`, `Halter`, and `Orderer`.
-}
module G2.Execution.Reducer ( Reducer (..)

                            , Halter (..)
                            , InitHalter
                            , UpdatePerStateHalt
                            , StopRed
                            , StepHalter

                            , Orderer (..)
                            , InitOrderer
                            , OrderStates
                            , UpdateSelected

                            , Processed (..)

                            , ReducerRes (..)
                            , HaltC (..)

                            , SomeReducer (..)
                            , SomeHalter (..)
                            , SomeOrderer (..)

                            -- * Reducers
                            , InitReducer
                            , RedRules
                            , mkSimpleReducer
                            , liftReducer
                            , liftSomeReducer

                            , stdRed
                            , nonRedPCSymFuncRed
                            , nonRedLibFuncsReducer
                            , nonRedHigherOrderReducer
                            , nonRedPCRed
                            , nonRedPCRedNoPrune
                            , nonRedPCRedConst

                            , ApproxPrevs
                            , emptyApproxPrevs
                            , nrpcApproxReducer
                            , strictRed
                            , taggerRed
                            , getLogger
                            , simpleLogger
                            , prettyLogger

                            , LimLogger (..)
                            , limLoggerConfig
                            , getLimLogger

                            , acceptTimeLogger
                            , numStepsLogger
                            , currExprLogger

                            , ReducerEq (..)
                            , (.==)
                            , (~>)
                            , (.~>)
                            , (-->)
                            , (.-->)

                            , (.|.)

                            -- * Halters
                            , mkSimpleHalter
                            , liftHalter
                            , liftSomeHalter

                            , swhnfHalter
                            , acceptIfViolatedHalter
                            , (<~>)
                            , (.<~>)
                            , zeroHalter
                            , discardIfAcceptedTagHalter
                            , maxOutputsHalter
                            , switchEveryNHalter
                            , varLookupLimitHalter

                            , hpcApproximationHalter
                            , approximationHalter
                            
                            , HPCMemoTable
                            , noNewHPCHalter
                            , acceptOnlyNewHPC
                            , stdTimerHalter
                            , timerHalter

                            , printOnHaltC

                            -- * Orderers
                            , mkSimpleOrderer
                            , liftOrderer
                            , liftSomeOrderer
                            , (<->)
                            , ordComb
                            , nextOrderer
                            , pickLeastUsedOrderer
                            , bucketSizeOrderer
                            , adtHeightOrderer
                            , adtSizeOrderer
                            , pcSizeOrderer
                            , incrAfterN
                            , quotTrueAssert

                            -- * Analyzers
                            , AnalyzeStates
                            , noAnalysis
                            , logStatesAtTime
                            , logRedRuleNum

                            , LogStatesAtStep
                            , logStatesAtStepTracker
                            , logStatesAtStep

                            -- * Execution
                            , SolveStates
                            , runReducer ) where

import G2.Config
import qualified G2.Language.ExprEnv as E
import G2.Execution.NormalForms
import G2.Execution.Rules
import G2.Interface.ExecRes
import G2.Execution.ExecSkip
import G2.Language
import G2.Language.Approximation
import G2.Language.KnownValues
import qualified G2.Language.Monad as MD
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as Stck
import G2.Solver
import G2.Lib.Printers

import Control.Monad.Extra
import Control.Monad.IO.Class
import qualified Control.Monad.State as SM
import Data.Foldable
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid hiding (Alt)
import qualified Data.List as L 
import qualified Data.Sequence as S
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Tuple
import Data.Time.Clock
import System.Clock
import System.Directory

import Debug.Trace

-- | Used when applying execution rules
-- Allows tracking extra information to control halting of rule application,
-- and to reorder states
-- see also, the Reducer, Halter, Orderer typeclasses
-- cases is used for logging states
data ExState rv hv sov t = ExState { state :: State t
                                   , reducer_val :: rv
                                   , halter_val :: hv
                                   , order_val :: sov
                                   }

-- | Keeps track of type a's that have either been accepted or dropped
data Processed acc dis = Processed { accepted :: [acc]
                                   , discarded :: [dis] }

-- | Used by Reducers to indicate their progress reducing.
data ReducerRes = NoProgress | InProgress | Finished deriving (Eq, Ord, Show, Read)

progPrioritizer :: ReducerRes -> ReducerRes -> ReducerRes
progPrioritizer InProgress _ = InProgress
progPrioritizer _ InProgress = InProgress
progPrioritizer Finished _ = Finished
progPrioritizer _ Finished = Finished
progPrioritizer _ _ = NoProgress

-- | Used by members of the Halter typeclass to control whether to continue
-- evaluating the current State, or switch to evaluating a new state.
data HaltC = Discard -- ^ Switch to evaluating a new state, and reject the current state
           | Accept -- ^ Switch to evaluating a new state, and accept the current state
           | Switch -- ^ Switch to evaluating a new state, but continue evaluating the current state later
           | Continue -- ^ Continue evaluating the current State
           deriving (Eq, Ord, Show, Read)

type InitReducer rv t = State t -> rv
type RedRules m rv t = rv -> State t -> Bindings -> m (ReducerRes, [(State t, rv)], Bindings)


-- | A Reducer is used to define a set of Reduction Rules.
-- Reduction Rules take a `State`, and output new `State`s.
-- The reducer value, rv, can be used to track extra information, on a per `State` basis.
data Reducer m rv t = Reducer {
        -- | Initializes the reducer value.
          initReducer :: InitReducer rv t

        -- | Takes a State, and performs the appropriate Reduction Rule.
        , redRules :: RedRules m rv t

        -- | After a reducer returns multiple states,
        -- gives an opportunity to update with all States and Reducer values's,
        -- visible.
        -- Errors if the returned list is too short.
        -- If only one state is returned by all reducers, updateWithAll does not run.
        , updateWithAll :: [State t] -> [State t]

        -- Action to run after a State is accepted.
        , onAccept :: State t -> Bindings -> rv -> m (State t, Bindings)

        -- Action to run after a State is solved.
        , onSolved :: m ()

        -- Action to run after a State is discared.
        , onDiscard :: State t -> rv -> m ()

        -- | Action to run after execution of all states has terminated.
        , afterRed :: m ()

    }

-- | A simple, default reducer.
-- `updateWithAll` does not change or adjust the reducer values.
-- `onAccept` and `afterRed` immediately returns the empty tuple.
mkSimpleReducer :: Monad m => InitReducer rv t -> RedRules m rv t -> Reducer m rv t
mkSimpleReducer init_red red_rules =
    Reducer {
      initReducer = init_red
    , redRules = red_rules
    , updateWithAll = id
    , onAccept = \s b _ -> return (s, b)
    , onSolved = return ()
    , onDiscard = \_ _ -> return ()
    , afterRed = return ()
    }
{-# INLINE mkSimpleReducer #-}

-- | Lift a reducer from a component monad to a constructed monad. 
liftReducer :: (Monad m1, SM.MonadTrans m2) => Reducer m1 rv t -> Reducer (m2 m1) rv t
liftReducer r = Reducer { initReducer = initReducer r
                        , redRules = \rv s b -> SM.lift ((redRules r) rv s b)
                        , updateWithAll = updateWithAll r
                        , onAccept = \s b rv -> SM.lift ((onAccept r) s b rv)
                        , onSolved = SM.lift (onSolved r)
                        , onDiscard = \s rv -> SM.lift ((onDiscard r) s rv)
                        , afterRed = SM.lift (afterRed r)}

-- | Lift a SomeReducer from a component monad to a constructed monad. 
liftSomeReducer :: (Monad m1, SM.MonadTrans m2) => SomeReducer m1 t -> SomeReducer (m2 m1) t
liftSomeReducer (SomeReducer r) = SomeReducer (liftReducer r )

type InitHalter hv t = State t -> hv
type UpdatePerStateHalt hv r t = hv -> Processed r (State t) -> State t -> hv
type StopRed m hv r t = hv -> Processed r (State t)  -> State t -> m HaltC
type StepHalter hv r t = hv -> Processed r (State t) -> [State t] -> State t -> hv

-- | Determines when to stop evaluating a state
-- The halter value, hv, can be used to track extra information, on a per `State` basis.
data Halter m hv r t = Halter {
    -- | Initializes each state halter value
      initHalt :: InitHalter hv t

    -- | Runs whenever we switch to evaluating a different state,
    -- to update the halter value of that new state
    , updatePerStateHalt :: UpdatePerStateHalt hv r t

    -- | Runs when we start execution on a state, immediately after
    -- `updatePerStateHalt`.  Allows a State to be discarded right
    -- before execution is about to (re-)begin.
    -- Return True if execution should proceed, False to discard
    , discardOnStart :: hv -> Processed r (State t) -> State t -> Bool

    -- | Determines whether to continue reduction on the current state
    , stopRed :: StopRed m hv r t

    -- | Takes a state, and updates its halter record field
    , stepHalter :: StepHalter hv r t

    -- | After multiple states, are returned
    -- gives an opportunity to update halters with all States and halter values visible.
    -- Errors if the returned list is too short.
    -- If only one state is returned, updateHalterWithAll does not run.
    , updateHalterWithAll :: [(State t, hv)] -> [hv]
    }

-- | A simple, default halter.
mkSimpleHalter :: Monad m => InitHalter hv t -> UpdatePerStateHalt hv r t -> StopRed m hv r t -> StepHalter hv r t -> Halter m hv r t
mkSimpleHalter initial update stop step = Halter { initHalt = initial
                                                 , updatePerStateHalt = update
                                                 , discardOnStart = \_ _ _ -> False
                                                 , stopRed = stop
                                                 , stepHalter = step
                                                 , updateHalterWithAll = map snd }
{-# INLINE mkSimpleHalter #-}

-- | Lift a halter from a component monad to a constructed monad. 
liftHalter :: (Monad m1, SM.MonadTrans m2) => Halter m1 rv r t -> Halter (m2 m1) rv r t
liftHalter h = Halter { initHalt = initHalt h
                      , updatePerStateHalt = updatePerStateHalt h
                      , discardOnStart = discardOnStart h
                      , stopRed = \hv pr s -> SM.lift ((stopRed h) hv pr s)
                      , stepHalter = stepHalter h
                      , updateHalterWithAll = updateHalterWithAll h }

-- | Lift a SomeHalter from a component monad to a constructed monad. 
liftSomeHalter :: (Monad m1, SM.MonadTrans m2) => SomeHalter m1 r t -> SomeHalter (m2 m1) r t
liftSomeHalter (SomeHalter r) = SomeHalter (liftHalter r)

{-# INLINE mkStoppingHalter #-}
mkStoppingHalter :: Monad m => StopRed m () r t -> Halter m () r t
mkStoppingHalter stop =
            mkSimpleHalter
                (const ())
                (\_ _ _ -> ())
                stop
                (\_ _ _ _ -> ())

type InitOrderer sov t = State t -> sov
type OrderStates m sov b r t = sov -> Processed r (State t) -> State t -> m b
type UpdateSelected sov r t = sov -> Processed r (State t) -> State t -> sov

-- | Picks an order to evaluate the states, to allow prioritizing some over others.
-- The orderer value, sov, can be used to track extra information, on a per `State` basis.
-- The ordering type b, is used to determine what order to execute the states in.
-- In practice, `b` must be an instance of `Ord`.  When the orderer is called, the `State` corresponding
-- to the minimal `b` is executed.
data Orderer m sov b r t = Orderer {
    -- | Initializing the per state ordering value 
      initPerStateOrder :: InitOrderer sov t

    -- | Assigns each state some value of an ordered type, and then proceeds with execution on the
    -- state assigned the minimal value
    , orderStates :: OrderStates m sov b r t

    -- | Run on the selected state, to update it's sov field
    , updateSelected :: UpdateSelected sov r t

    -- | Run on the state at each step, to update it's sov field
    , stepOrderer :: sov -> Processed r (State t) -> [State t] -> State t -> m sov
    }

-- | A simple, default orderer.
mkSimpleOrderer :: Monad m => InitOrderer sov t -> OrderStates m sov b r t -> UpdateSelected sov r t -> Orderer m sov b r t
mkSimpleOrderer initial order update = Orderer { initPerStateOrder = initial
                                               , orderStates = order
                                               , updateSelected = update
                                               , stepOrderer = \sov _ _ _ -> return sov}

-- | Lift a Orderer from a component monad to a constructed monad. 
liftOrderer :: (Monad m1, SM.MonadTrans m2) => Orderer m1 sov b r t -> Orderer (m2 m1) sov b r t
liftOrderer r = Orderer { initPerStateOrder = initPerStateOrder r
                        , orderStates = \sov pr s -> SM.lift ((orderStates r) sov pr s)
                        , updateSelected = updateSelected r
                        , stepOrderer = \sov pr xs s -> SM.lift ((stepOrderer r) sov pr xs s) }

-- | Lift a liftSomeOrderer from a component monad to a constructed monad. 
liftSomeOrderer :: (Monad m1, SM.MonadTrans m2) => SomeOrderer m1 r t -> SomeOrderer (m2 m1) r t
liftSomeOrderer (SomeOrderer r) = SomeOrderer (liftOrderer r)

getState :: M.Map b [s] -> Maybe (b, [s])
getState = M.lookupMin

-- | Hide the details of a Reducer's reducer value.
data SomeReducer m t where
    SomeReducer :: forall m rv t . Reducer m rv t -> SomeReducer m t

-- | Hide the details of a Halter's halter value.
data SomeHalter m r t where
    SomeHalter :: forall m hv r t . Halter m hv r t -> SomeHalter m r t

-- | Hide the details of an Orderer's orderer value and ordering type.
data SomeOrderer m r t where
    SomeOrderer :: forall m sov b r t . Ord b => Orderer m sov b r t -> SomeOrderer m r t

-- * Reducers
--
-- $reducers
--
-- Reducers define sets of reduction rules.


-- Combines multiple reducers together into a single reducer.

-- We use RC to combine the reducer values for RCombiner
-- We should never define any other instance of Reducer with RC, or export it
-- because this could lead to undecidable instances
data RC a b = RC a b

-- | Check if a `Reducer` returns some specific `ReducerRes`
data ReducerEq m t where
    (:==) :: forall m rv t . Reducer m rv t -> ReducerRes -> ReducerEq m t

(.==) :: SomeReducer m t -> ReducerRes -> ReducerEq m t
SomeReducer r .== res = r :== res

infixr 8 .==

infixr 7 ~>, .~>

infixr 5 -->, .-->

-- | @r1 ~> r2@ applies `Reducer` `r1`, followed by reducer `r2`. 
(~>) :: Monad m => Reducer m rv1 t -> Reducer m rv2 t -> Reducer m (RC rv1 rv2) t
r1 ~> r2 =
    Reducer { initReducer = \s -> RC (initReducer r1 s) (initReducer r2 s)

            , redRules = \(RC rv1 rv2) s b -> do
                (rr1, srv1, b') <- redRules r1 rv1 s b
                (rr2, srv2, b'') <- redRulesToStates r2 rv2 srv1 b'

                return (progPrioritizer rr1 rr2, srv2, b'')

            , updateWithAll = updateWithAllPair (updateWithAll r1) (updateWithAll r2)

            , onAccept = \s b (RC rv1 rv2) -> do
                (s', b') <- onAccept r1 s b rv1
                onAccept r2 s' b' rv2

            , onSolved = do
                onSolved r1
                onSolved r2

            , onDiscard = \s (RC rv1 rv2) -> do
                onDiscard r1 s rv1
                onDiscard r2 s rv2

            , afterRed = do
                afterRed r1
                afterRed r2

            }
{-# INLINE (~>) #-}

-- | `~>` adjusted to work on `SomeReducer`s, rather than `Reducer`s.
(.~>) :: Monad m => SomeReducer m t -> SomeReducer m t -> SomeReducer m t
SomeReducer r1 .~> SomeReducer r2 = SomeReducer (r1 ~> r2)
{-# INLINE (.~>) #-}

-- | @r1 := res --> r2@ applies `Reducer` `r1`.  If `r1` returns the `ReducerRes` `res`,
-- then `Reducer` `r2` is applied.  Otherwise, reduction halts.  
(-->) :: Monad m => ReducerEq m t -> Reducer m rv2 t -> SomeReducer m t
(r1 :== res) --> r2 =
    SomeReducer $
       Reducer { initReducer = \s -> RC (initReducer r1 s) (initReducer r2 s)

                , redRules = \(RC rv1 rv2) s b -> do
                    (rr1, srv1, b') <- redRules r1 rv1 s b
                    let (s', rv1') = unzip srv1

                    case rr1 == res of
                        True -> do
                            (rr2, ss, b'') <- redRulesToStates r2 rv2 srv1 b'
                            return (rr2, ss, b'')
                        False -> return (rr1, zip s' (map (flip RC rv2) rv1'), b')

                , updateWithAll = updateWithAllPair (updateWithAll r1) (updateWithAll r2)

                , onAccept = \s b (RC rv1 rv2) -> do
                    (s', b') <- onAccept r1 s b rv1
                    onAccept r2 s' b' rv2

                , onSolved = do
                    onSolved r1
                    onSolved r2

                , onDiscard = \s (RC rv1 rv2) -> do
                    onDiscard r1 s rv1
                    onDiscard r2 s rv2

                , afterRed = do
                    afterRed r1
                    afterRed r2
                }
{-# INLINE (-->) #-}

-- | `.-->` adjusted to take a `SomeReducer`, rather than a `Reducer`s.
(.-->) :: Monad m => ReducerEq m t -> SomeReducer m t -> SomeReducer m t
req .--> SomeReducer r = req --> r

redRulesToStatesAux :: Monad m =>  Reducer m rv2 t -> rv2 -> Bindings -> (State t, rv1) -> m (Bindings, (ReducerRes, [(State t, RC rv1 rv2)]))
redRulesToStatesAux r rv2 b (is, rv1) = do
        (rr_, is', b') <- redRules r rv2 is b
        return (b', (rr_, map (\(is'', rv2') -> (is'', RC rv1 rv2') ) is'))

redRulesToStates :: Monad m => Reducer m rv2 t -> rv2 -> [(State t, rv1)] -> Bindings -> m (ReducerRes, [(State t, RC rv1 rv2)], Bindings)
redRulesToStates r rv1 s b = do
    let redRulesToStatesAux' = redRulesToStatesAux r rv1
    (b', rs) <- MD.mapMAccumB redRulesToStatesAux' b s

    let (rr, s') = L.unzip rs

    let rf = foldr progPrioritizer NoProgress rr

    return $ (rf, concat s', b')

-- | @r1 .|. r2@ applies both Reducer r1 and Reducer r2 to the \inital\ state passed to the reducer,
-- and returns the list of states returned from both reducers combined.
-- Care should be taken to avoid unwanted duplication of states if, for example, neither of the reducers
-- makes progress.
(.|.) :: Monad m => Reducer m rv1 t -> Reducer m rv2 t -> Reducer m (RC rv1 rv2) t
r1 .|. r2 =
    Reducer { initReducer = \s -> RC (initReducer r1 s) (initReducer r2 s)

            , redRules = \(RC rv1 rv2) s b -> do
                (rr2, srv2, b') <- redRules r2 rv2 s b
                (rr1, srv1, b'') <- redRules r1 rv1 s b'

                let srv2' = map (\(s_, rv2_) -> (s_, RC rv1 rv2_) ) srv2
                    srv1' = map (\(s_, rv1_) -> (s_, RC rv1_ rv2) ) srv1

                return (progPrioritizer rr1 rr2, srv2' ++ srv1', b'')

            , updateWithAll = updateWithAllPair (updateWithAll r1) (updateWithAll r2)

            , onAccept = \s b (RC rv1 rv2) -> do
                (s', b') <- onAccept r1 s b rv1
                onAccept r2 s' b' rv2

            , onSolved = do
                onSolved r1
                onSolved r2

            , onDiscard = \s (RC rv1 rv2) -> do
                onDiscard r1 s rv1
                onDiscard r2 s rv2

            , afterRed = do
                afterRed r1
                afterRed r2

            }
{-# INLINE (.|.) #-}

updateWithAllPair :: ([State t] -> [State t]) -> ([State t] -> [State t]) -> [State t] -> [State t]
updateWithAllPair update1 update2 = update2 . update1

{-#INLINE stdRed #-}
{-# SPECIALIZE stdRed :: (Solver solver, Simplifier simplifier) => Sharing -> SymbolicFuncEval t -> solver -> simplifier -> Reducer IO () t #-}
stdRed :: (MonadIO m, Solver solver, Simplifier simplifier) => Sharing -> SymbolicFuncEval t -> solver -> simplifier -> Reducer m () t
stdRed share symb_func_eval solver simplifier =
        mkSimpleReducer (\_ -> ())
                        (\_ s b -> do
                            (r, s', b') <- liftIO $ stdReduce share symb_func_eval solver simplifier s b

                            return (if r == RuleIdentity then Finished else InProgress, s', b')
                        )

-- | Solves NRPCs, while handling higher order symbolic functions.
nonRedPCSymFuncRed :: Monad m => Reducer m (Maybe SymFuncTicks) t
nonRedPCSymFuncRed = mkSimpleReducer (\_ -> Nothing)
                        nonRedPCSymFunc

nonRedPCSymFunc :: Monad m => RedRules m (Maybe SymFuncTicks) t
nonRedPCSymFunc _
                s@(State {curr_expr = cexpr
                         , exec_stack = stck
                         , non_red_path_conds = (nre1, nre2) :*> nrs
                         })
                        b@(Bindings { name_gen = ng }) =
    
    let
        sft = defSymFuncTicks
        stck' = Stck.push (CurrExprFrame (EnsureEq nre2) cexpr) stck
        s' = s { exec_stack = stck', non_red_path_conds = nrs }

        stripCenterTick (Tick _ e) = e
        stripCenterTick (App e1 e2) = App (stripCenterTick e1) e2
        stripCenterTick e = e
    in
    case retReplaceSymbFuncTemplate sft s' ng (stripCenterTick nre1) of
        Just (_, s'', ng') ->
            return (InProgress, zip s'' (repeat (Just sft)), b {name_gen = ng'})
        Nothing ->
            let 
                s'' = s' {curr_expr = CurrExpr Evaluate nre1}
            in return (InProgress, [(s'', Just sft)], b { name_gen = ng })
nonRedPCSymFunc m_sft s b = return (Finished, [(s, m_sft)], b)

-- | (Symbolic) functions to not add to the NRPCs
type NoNRPC = HS.HashSet Name

-- | A reducer to add library functions to non reduced path constraints for solving later  
nonRedLibFuncsReducer :: MonadIO m =>
                         HS.HashSet Name -- ^ Names of functions that must be executed
                      -> HS.HashSet Name -- ^ Names of functions that should not reesult in a larger expression become EXEC,
                                         -- but should not be added to the NRPC at the top level.
                                         -- I.e. if `f` is in this set, `f x y` will not be added to the NRPCs, but a function `g` that includes
                                         -- `f in it's definition may still be added to the NRPCs.
                      -> Config
                      -> Reducer m (NRPCMemoTable, ReachesSymMemoTable, Int) t
nonRedLibFuncsReducer exec_names no_nrpc_names config =
    (mkSimpleReducer (\_ -> (HM.empty, HM.empty, 0))
        (nonRedLibFuncs exec_names no_nrpc_names))
        { onAccept = \s b (_, _, nrpc_count) -> do
            if print_num_nrpc config
                then liftIO . putStrLn $ "NRPCs Generated: " ++ show nrpc_count
                else return ()
            return (s, b) }

nonRedLibFuncs :: MonadIO m => HS.HashSet Name -- ^ Names of functions that must be executed
                          -> HS.HashSet Name -- ^ Names of functions that should not reesult in a larger expression become EXEC,
                                             -- but should not be added to the NRPC at the top level.
                          -> RedRules m (NRPCMemoTable, ReachesSymMemoTable, Int) t
nonRedLibFuncs exec_names no_nrpc_names 
                rv@(var_table, sym_table, nrpc_count)
                s@(State { expr_env = eenv
                         , curr_expr = CurrExpr _ ce
                         , known_values = kv
                         }) 
                b@(Bindings { name_gen = ng })
    | 
      -- We are NOT dealing with a symbolic function or a function that should not be put in the NRPCs
      Var (Id n _):_ <- unApp ce
    , Just (Id n' _) <- E.deepLookupVar n eenv
    , not (n' `HS.member` no_nrpc_names)
    , not (E.isSymbolic n' eenv)
    , Just (s'@(State { curr_expr = CurrExpr _ _ }), ce', ng') <- createNonRed ng s = 
        let
            (reaches_sym, sym_table') = reachesSymbolic sym_table eenv ce'
            (exec_skip, var_table') = if reaches_sym then checkDelayability eenv ce' ng exec_names var_table else (Skip, var_table)
        in
        case (reaches_sym, exec_skip) of
            (True, Skip) -> return (Finished, [(s', (var_table', sym_table', nrpc_count + 1))], b {name_gen = ng'})
            _ -> return (Finished, [(s, (var_table', sym_table', nrpc_count))], b)

    | Tick nl (Var (Id n _)) <- ce
    , isNonRedBlockerTick nl
    , Just e <- E.lookup n eenv = return (Finished, [(s { curr_expr = CurrExpr Evaluate e }, rv)], b)
    | otherwise = return (Finished, [(s, rv)], b)

-- | A reducer to add higher order functions to non reduced path constraints for solving later  
nonRedHigherOrderReducer :: MonadIO m =>
                            Config
                         -> Reducer m (NoNRPC, Int) t
nonRedHigherOrderReducer config =
    (mkSimpleReducer (\_ -> (HS.empty, 0)) nonRedHigherOrderFunc)
        { onAccept = \s b (_, nrpc_count) -> do
            if print_num_nrpc config
                then liftIO . putStrLn $ "NRPCs Generated: " ++ show nrpc_count
                else return ()
            return (s, b) }

nonRedHigherOrderFunc :: MonadIO m => RedRules m (NoNRPC, Int) t
nonRedHigherOrderFunc 
                (no_nrpc, nrpc_count)
                s@(State { expr_env = eenv
                         , curr_expr = CurrExpr _ ce
                         , known_values = kv
                         }) 
                b@(Bindings { name_gen = ng })
    | 
      -- We have a symbolic function
      Var (Id n t):es_ce <- unApp ce
    , E.isSymbolic n eenv
    , not (n `HS.member` no_nrpc)
    
    , (ae, stck') <- allApplyFrames (exec_stack s)
    , let es = es_ce ++ ae

    , Just (s', _, ng') <- createNonRed ng s 
    = 
        let
            -- If we have an EnsureEq on the stack, we do not want to add function argument states because
            -- (a) we have already added function argument states when we initially began reducing the NRPC
            -- and (b) we need to make sure that we actually do satisfy the equality, for soundness, and
            -- thus cannot clear out the stack
            (ng'', xs_new_g) = if noEnsureEq stck'
                            then L.mapAccumR
                                    (funcArgState (map typeOf es) (returnType $ PresType t)) ng'
                                    $ zip [0..] es
                            else (ng', [])
            xs = mapMaybe (fmap fst) xs_new_g
            new_g = catMaybes $ mapMaybe (fmap snd) xs_new_g
            no_nrpc' = foldr HS.insert no_nrpc new_g
            xs' = map (\new_s -> (new_s, (no_nrpc', nrpc_count))) xs
        in 
        return (Finished, (s', (no_nrpc', nrpc_count + 1)):xs', b {name_gen = ng''})

    | otherwise = return (Finished, [(s, (no_nrpc, nrpc_count))], b)
    where
        noEnsureEq stck | Just (CurrExprFrame (EnsureEq _) _, _) <- Stck.pop stck = False
                        | Just (_, stck') <- Stck.pop stck = noEnsureEq stck'
                        |otherwise = True

        -- | Generate `State`s to explore each function argument
        funcArgState all_args_ts ret_ty init_ng (this_arg_num, fa_e)
            | isTyFun (typeOf fa_e) = 
                    let
                        ts = anonArgumentTypes fa_e
                        (is, ng') = freshIds ts ng_args
                        vs = map Var is
                        fa_e' = mkApp $ fa_e:vs
                        (bindee, ng'') = freshId (typeOf this_arg) ng'
                        (ret_id, ng''') = freshId ret_ty ng''

                        -- Instantiate the symbolic function `n`
                        lam_center = Case (mkApp $ Var this_arg:vs) bindee ret_ty [Alt Default  (Var ret_id)]
                        f_def = mkLams (zip (repeat TermL) arg_is) lam_center
                        eenv' = E.insert n f_def eenv

                        -- Set up symbolic variables
                        eenv'' = E.insertSymbolic ret_id $ foldr E.insertSymbolic eenv' is
                    in
                    (ng''', Just $ (s { expr_env = eenv''
                                      , curr_expr = CurrExpr Evaluate fa_e'
                                      , exec_stack = stck }, Nothing))
            | isPrimType (typeOf fa_e) = (init_ng, Nothing)
            | otherwise =
                let
                    (g, ng') = freshId (TyFun (typeOf this_arg) ret_ty) ng_args
                    (bindee, ng'') = freshId (typeOf this_arg) ng'
                    g_app = Case (App (Var g) (Var this_arg)) bindee ret_ty [Alt Default  (Var bindee)]
                    f_def = mkLams (zip (repeat TermL) arg_is) g_app

                    fa_e' = App (Var g) fa_e

                    eenv' = E.insert n f_def eenv
                    eenv'' = E.insertSymbolic g eenv'
                in
                (ng'', Just $ (s { expr_env = eenv'', curr_expr = CurrExpr Evaluate fa_e', exec_stack = stck }, Just $ idName g))
            where
                n = case unApp ce of
                    Var (Id vn _):_ -> vn
                    _ -> error "funcArgState: impossible"

                (arg_is, ng_args) = freshIds all_args_ts init_ng
                this_arg = arg_is !! this_arg_num

                stck = Stck.singleton $ CurrExprFrame NoAction (CurrExpr Return $ Prim UnspecifiedOutput TyBottom)

data ApproxPrevs t = AP { ap_nrpc_states :: [State t], ap_halter_states :: [State t]}

emptyApproxPrevs :: ApproxPrevs t
emptyApproxPrevs = AP { ap_nrpc_states = [], ap_halter_states = [] }

-- | When a newly reached function application is approximated by a previously seen (and thus explored) function application,
-- shift the new function application into the NRPCs.
nrpcApproxReducer :: (Solver solver, SM.MonadState (ApproxPrevs t) m, MonadIO m) =>
                     solver
                  -> HS.HashSet Name -- ^ Names of functions that should not be approximated
                  -> HS.HashSet Name -- ^ Names that should not be inlined (often: top level names from the original source code)
                  -> Config
                  -> Reducer m Int t
nrpcApproxReducer solver no_inline no_nrpc_names config =
    (mkSimpleReducer (const 0) red)
            { onAccept = \s b nrpc_count -> do
            if print_num_nrpc config
                then liftIO . putStrLn $ "NRPCs Generated: " ++ show nrpc_count
                else return ()
            return (s, b) }

    where
        red rv s@(State { curr_expr = CurrExpr _ ce, expr_env = eenv }) b
            | maybe True (allowed_frame . fst) (Stck.pop (exec_stack s))
            
            , let e = applyWrap (getExpr s) (exec_stack s)
            , Var (Id n _):_:_ <- unApp e

            , Just (Id n' _) <- E.deepLookupVar n eenv
            , not (n' `HS.member` no_nrpc_names)
            , not (E.isSymbolic n' eenv)

            , not . isTyFun . typeOf $ e = do
                -- liftIO $ do
                --     putStrLn $ "curr_expr s = " ++ show (getExpr s)
                --     putStrLn $ "log_path s = " ++ show (log_path s)
                --     putStrLn $ "num_steps s = " ++ show (num_steps s)
                let s' = s { curr_expr = CurrExpr Evaluate e, exec_stack = Stck.empty }
                xs <- SM.gets ap_nrpc_states
                approx <- liftIO $ findM (\prev -> do
                                            -- liftIO $ do
                                            --      putStrLn $ "curr_expr s = " ++ show (getExpr s)
                                            --      putStrLn $ "log_path prev = " ++ show (log_path prev)
                                            --      putStrLn $ "num_steps prev = " ++ show (num_steps prev)
                                            moreRestrictiveIncludingPC
                                                        solver
                                                        mr_cont
                                                        gen_lemma
                                                        lookupConcOrSymState
                                                        no_inline
                                                        prev
                                                        s'
                                                ) xs
                
                let nr_s_ng = createNonRed (name_gen b) s

                case nr_s_ng of
                    Just (nr_s, _, ng') | isJust approx -> return (Finished, [(nr_s, rv + 1)], b { name_gen = ng' })
                    _ -> do SM.modify (\ap -> ap { ap_nrpc_states = s':xs }); return (Finished, [(s, rv)], b)
            | Tick nl (Var (Id n _)) <- ce
            , isNonRedBlockerTick nl
            , Just e <- E.lookup n eenv = return (Finished, [(s { curr_expr = CurrExpr Evaluate e }, rv)], b)
        red rv s b = return (Finished, [(s, rv)], b)
        
        mr_cont = mrContIgnoreNRPCTicks gen_lemma lookupConcOrSymState
        gen_lemma _ _ _ _ _ = ()

        allowed_frame (ApplyFrame _) = False
        allowed_frame _ = True

        applyWrap e stck | Just (ApplyFrame a, stck') <- Stck.pop stck = applyWrap (App e a) stck'
                         | otherwise = e

-- If doing so is possible, create an NRPC for the current expression of the passed state
createNonRed :: NameGen
             -> State t
             -> Maybe
                      ( State t -- ^ New state with NRPC applied
                      , Expr -- ^ Expression added into the NRPCs (and equated to some symbolic variable)
                      , NameGen)
createNonRed ng
             s@(State { curr_expr = CurrExpr _ ce
                      , expr_env = eenv
                      , non_red_path_conds = nrs
                      , known_values = kv })
            | v@(Var (Id _ t)):es_ce <- unApp ce
             -- Function is being fully applied 
            , (ae, stck) <- allApplyFrames (exec_stack s)
            , let es = es_ce ++ ae
                  ce' = mkApp (v:es)
            , hasFuncType (PresType t)
            
            , let ce_ty = typeOf ce'
            , not . hasFuncType . PresType $ ce_ty
            -- Don't turn functions manipulating "magic types"- types represented as Primitives, with special handling
            -- (for instance, MutVars, Handles) into NRPC symbolic variables.
            , not (hasMagicTypes kv ce) =
    let
        (new_sym, ng') = freshSeededString "sym" ng
        new_sym_id = Id new_sym ce_ty
        eenv' = E.insertSymbolic new_sym_id eenv
        cexpr' = CurrExpr Return (Var new_sym_id)
        -- when NRPC moves back to current expression, it immediately gets added as NRPC again.
        -- To stop falling into this infinite loop, instead of adding current expression in NRPC
        -- we associate a tick (nonRedBlocker) with the expression and then standard reducer reduces
        -- this tick.
        (te, ng'') = nonRedBlockerTick ng' v
        ce'' = mkApp $ te:es

        (ng''', nrs') = addNRPC ng'' ce'' (Var new_sym_id) nrs

        s' = s { expr_env = eenv'
               , curr_expr = cexpr'
               , non_red_path_conds = nrs'
               , exec_stack = stck }
    in
    Just (s', ce'', ng''')
createNonRed _ _ = Nothing

hasMagicTypes :: ASTContainer c Type => KnownValues -> c -> Bool
hasMagicTypes kv = getAny . evalASTs hmt
    where
        hmt (TyCon n _) = Any (n `elem` magicTypes kv)
        hmt _ = Any False

allApplyFrames :: Stck.Stack Frame -> ([Expr], Stck.Stack Frame)
allApplyFrames stck = go [] stck stck
    where
        go aes pop_stck stck_top_ups
                    | Just (ApplyFrame ae, stck') <- Stck.pop pop_stck = go (ae:aes) stck' stck'
                    | Just (UpdateFrame _, stck') <- Stck.pop pop_stck = go aes stck' stck_top_ups
                    | otherwise = (reverse aes, stck_top_ups)

nonRedBlockerTick :: NameGen -> Expr -> (Expr, NameGen)
nonRedBlockerTick ng e =
    let (n, ng') = freshSeededName (Name "NonRedBlocker" Nothing 0 Nothing) ng in
    (Tick (NamedLoc n) e, ng')

isNonRedBlockerTick :: Tickish -> Bool
isNonRedBlockerTick (NamedLoc n) = nameOcc n == "NonRedBlocker"
isNonRedBlockerTick _ = False

-- Note [Ignore Update Frames]
-- In `strictRed`, when deciding whether to split up an expression to force strict evaluation of subexpression,
-- we pop UpdateFrames off the stack and search down for a CurrExprFrame (or empty stack).
-- To see why we do this (rather than just letting UpdateFrames be handled by the stdRed) consider the following example.
--
-- Suppose we are reducing the following walk function:
-- @
--  walk [] = []
--  walk (x:xs) = x:walk xs 
-- @
-- on a symbolic variable ys:
-- @ walk ys @
-- we will reach a state where s has been concretized to `y:ys'` and we have the current expression:
-- @ y:walk ys' @
-- At this point strictRed will kick in.  It will introduce fresh bindings z and zs', such that:
-- @ z = y
--   zs' = ys'
-- @
-- and set up the stack as:
-- @ CurrExprFrame NoAction z
--   CurrExprFrame NoAction zs'
--   CurrExprFrame NoAction (z:zs') @
-- Then, we will eventually reduce zs', and get, for some symbolic y' and ys'':
-- @ y':walk ys''@
-- with `UpdateFrame zs'` on the top of the stack.
--
-- If we did NOT handle update frames in the strictRed, we would store `zs' -> walk ys''` in the heap,
-- and then strictRed would (similarly to before) introduce new symbolic variables z' and zs'',
-- rewriting the expression to
-- @z':zs''@
-- and updating the stack to hold:
-- @ CurrExprFrame NoAction z'
--   CurrExprFrame NoAction zs''
--   CurrExprFrame NoAction (z':zs'')
--   CurrExprFrame NoAction (z:zs') @
-- (Note: the first three Frames are new, the last frame is a holdover.)
-- But now, when we eventually move down the stack to reach the final frame:
-- @ CurrExprFrame NoAction (z:zs') @
-- we still have `zs' -> y':walk ys''` in the heap- and so we will just repeatedly try and reduce
-- this subexpression in a loop- we can never again update the binding of zs'.
-- Thus, we want to ensure all subexpressions of zs' are variables- which can then themselves hav
-- bindings be evaluated to SWHNF- skipping past `UpdateFrame`s allows us to accomplish this.


-- | Force the `curr_expr` of each `State` to be fully evaluated.
-- That is, we evaluate not just to SWHNF, but so that all subexpressions are in SWHNF.
--
-- Depending on the `Halter`s and other `Reducer`s being used, some care must be taken.
-- Suppose we have `strictRed --> stdRed` as a `Reducer`, and `swhnfHalter` as a `Halter`.
-- In this case, `stdRed` might reduce to a SWHNF expression, and the state would then be
-- accepted before `strictRed` has time to force full evaluation.
-- For this reason, it is typically preferable to make `strictRed` one of the last `Reducer`s
-- to fire on each step, i.e. we would prefer `stdRed --> strictRed`
strictRed :: Monad m => Reducer m () t
strictRed = mkSimpleReducer (\_ -> ())
                            strict_red
    where
        strict_red _ s@(State { curr_expr = ce@(CurrExpr Return e)
                              , expr_env = eenv
                              , exec_stack = stck })
                     b@(Bindings { name_gen = ng })
            -- If the next frame is ensuring equality with another structure, allow it to be handled by the rules
            -- for EnsureEq, so that we get i.e. pruning of expression which have different central data constructors
            | Just (CurrExprFrame (EnsureEq _) _, _) <- Stck.pop stck = return (NoProgress, [(s, ())], b)
            | Data d:es@(_:_) <- unApp e
            , exec_done
            -- must_red checks if the expression contains non-fully-reduced subexpressions.
            -- Without this check, the strictRed might repeatedly fire, fruitlessly arranging for already reduced
            -- subexpressions to be repeatedly reduced over and over, and preventing the involved `State` from
            -- being halted.
            , must_red HS.empty e =
                let
                    -- Given a `curr_expr` of the form:
                    --   @ D e1 ... ek @
                    -- Rewrites to:
                    --   @ D x1 ... xk@
                    -- and inserts @x1 -> e1@, ..., @xk -> ek@ in the heap.  This means we can then evaluate
                    -- `x1, ... xk` and rely on sharing to correctly get a fully evaluated expression.
                    (is, ng') = freshIds (map typeOf es) ng
                    eenv' = foldl' (\env (Id n _, e_) -> E.insert n e_ env) eenv $ zip is es
                    ce_expr = mkApp $ Data d:map Var is
                    ce' = CurrExpr Return ce_expr
                    stck'' = foldl' (\st i -> Stck.push (CurrExprFrame NoAction (CurrExpr Evaluate $ Var i)) st)
                                   (Stck.push (CurrExprFrame NoAction ce') stck' )
                                   (tail is)
                    -- Handle update frames
                    eenv'' = foldr (\n -> E.insert n ce_expr) eenv' updates
                    
                    s' = s { expr_env = eenv''
                           , curr_expr = CurrExpr Evaluate (Var $ head is)
                           , exec_stack = stck'' }
                in
                return (InProgress, [(s', ())], b { name_gen = ng' })
            where
                -- To decide when to apply the strictRed, we must 
                -- (1) remove all update frames from the top of the stack
                -- (2) check if the top of the stack is a CurrExprFrame (or if the stack is empty empty)
                -- We effectively ignore UpdateFrames when checking if we should split up an expression to force strictness
                -- See Note [Ignore Update Frames].
                (updates, stck') = pop_updates [] stck

                exec_done | Stck.null stck' = True
                          | Just (CurrExprFrame _ _, _) <- Stck.pop stck' = True
                          | otherwise = False

                pop_updates ns stck | Just (UpdateFrame n, stck_) <- Stck.pop stck = pop_updates (n:ns) stck_
                                    | otherwise = (ns, stck)

                -- | Does the expression contain non-fully-reduced subexpressions?
                --
                -- Looks through variables, but tracks seen variable names to avoid an infinite loop.
                --
                -- Lambdas that are not in the center of an application (or bound by top level variables/nested in top level casts)
                -- are fully reduced, but reduction must happen if a lambda is in the center of an `App`.
                must_red ns (Var (Id n _)) = mr_var must_red ns n
                must_red _ (Lam _ _ _) = False
                must_red ns (Cast c_e _) = must_red ns c_e
                must_red ns e_ = must_red_no_lam ns e_

                must_red_no_lam ns (Var (Id n _)) = mr_var must_red_no_lam ns n
                must_red_no_lam _ (Lit _) = False
                must_red_no_lam _ (Data _) = False
                must_red_no_lam _ (Type _) = False
                must_red_no_lam _ (Prim _ _) = False
                must_red_no_lam ns (App e1 e2) = must_red_no_lam ns e1 || must_red ns e2
                must_red_no_lam ns (Cast c_e _) = must_red_no_lam ns c_e
                must_red_no_lam _ (Coercion _) = False
                must_red_no_lam _ _ = True

                mr_var cont ns n | HS.member n ns = False -- If we have seen a variable already,
                                                          -- we will have already discovered if it needs to be reduced
                                 | E.isSymbolic n eenv = False
                                 | otherwise = maybe True (cont (HS.insert n ns)) (E.lookup n eenv)
        strict_red _ s b = return (NoProgress, [(s, ())], b)

-- | Removes and reduces the values in a State's non_red_path_conds field.
-- If a state has not yet violated an assertion, it is discarded.
{-#INLINE nonRedPCRed #-}
nonRedPCRed :: Monad m => Reducer m () t
nonRedPCRed = (mkSimpleReducer (\_ -> ())
                              (nonRedPCRedFunc True))

-- | Removes and reduces the values in a State's non_red_path_conds field.
-- Keep all states, regardless of whether they have violated an assertion.
{-#INLINE nonRedPCRedNoPrune #-}
nonRedPCRedNoPrune :: Monad m => Reducer m () t
nonRedPCRedNoPrune = (mkSimpleReducer (\_ -> ())
                              (nonRedPCRedFunc False))

nonRedPCRedFunc :: Monad m => Bool -- ^ If true, prune states that do not have true_assert == True
                           -> RedRules m () t
nonRedPCRedFunc prune _
                s@(State { expr_env = eenv
                         , curr_expr = cexpr
                         , exec_stack = stck
                         , non_red_path_conds = (nre1, nre2) :*> nrs
                         , model = m })
                b@(Bindings { higher_order_inst = inst })
    -- If our goal is to violate assertions, and we haven't violated an assertion yet when
    -- we get to NRPCs, just discard the state.
    -- Based on how we calculate the "exec" set, any assertion violations must occur before
    -- we get to NRPCs. 
    | not (true_assert s), prune = return (Finished, [], b)
    | Var (Id n t) <- nre2
    , E.isSymbolic n eenv
    , hasFuncType (PresType t) =
        let
            s' = s { expr_env = E.insert n nre1 eenv
                   , non_red_path_conds  = nrs }
        in
        return (InProgress, [(s', ())], b)
    | Var (Id n t) <- nre1
    , E.isSymbolic n eenv
    , hasFuncType (PresType t) =
        let
            s' = s { expr_env = E.insert n nre2 eenv
                   , non_red_path_conds  = nrs }
        in
        return (InProgress, [(s', ())], b)
    | otherwise = do
        let stck' = Stck.push (CurrExprFrame (EnsureEq nre2) cexpr) stck

        let cexpr' = CurrExpr Evaluate nre1

        let eenv_si_ces = substHigherOrder eenv m inst cexpr'

        let s' = s { exec_stack = stck'
                   , non_red_path_conds = nrs
                   }
            xs = map (\(eenv', m', ce) -> (s' { expr_env = eenv'
                                              , model = m'
                                              , curr_expr = ce }, ())) eenv_si_ces

        return (InProgress, xs, b)
nonRedPCRedFunc _ _ s b = return (Finished, [(s, ())], b)

-- [Higher-Order Model]
-- Substitutes all possible higher order functions for symbolic higher order functions.
-- We insert the substituted higher order function directly into the model, because, due
-- to the VAR-RED rule, the function name will (if the function is called) be lost during execution.
substHigherOrder :: ExprEnv -> Model -> HS.HashSet Name -> CurrExpr -> [(ExprEnv, Model, CurrExpr)]
substHigherOrder eenv m ns ce =
    let
        is = mapMaybe (\n -> case E.lookup n eenv of
                                Just e -> Just $ Id n (typeOf e)
                                Nothing -> Nothing) $ HS.toList ns

        higherOrd = filter (isTyFun . typeOf) . symbVars eenv $ ce
        higherOrdSub = map (\v -> (v, mapMaybe (genSubstitutable v) is)) higherOrd
    in
    substHigherOrder' [(eenv, m, ce)] higherOrdSub
    where
        genSubstitutable v i
            | Just bm <- specializes (typeOf v) (typeOf i) =
                let
                    bnds = map idName $ leadingTyForAllBindings i
                    tys = mapMaybe (\b -> fmap Type $ M.lookup b bm) bnds
                in
                Just . mkApp $ Var i:tys
            | otherwise = Nothing

substHigherOrder' :: [(ExprEnv, Model, CurrExpr)] -> [(Id, [Expr])] -> [(ExprEnv, Model, CurrExpr)]
substHigherOrder' eenvsice [] = eenvsice
substHigherOrder' eenvsice ((i, es):iss) =
    substHigherOrder'
        (concatMap (\e_rep ->
                        map (\(eenv, m, ce) -> ( E.insert (idName i) e_rep eenv
                                               , HM.insert (idName i) e_rep m
                                               , replaceASTs (Var i) e_rep ce)
                            ) eenvsice)
        es) iss

-- | Removes and reduces the values in a State's non_red_path_conds field
-- by instantiating higher order functions to be constant.
-- Does not return any states if the state does not contain at least one
-- higher order symbolic variable.
nonRedPCRedConst :: Monad m => Reducer m () t
nonRedPCRedConst = mkSimpleReducer (\_ -> ())
                                   nonRedPCRedConstFunc

nonRedPCRedConstFunc :: Monad m => RedRules m () t
nonRedPCRedConstFunc _
                     s@(State { expr_env = eenv
                              , curr_expr = cexpr
                              , exec_stack = stck
                              , non_red_path_conds = (nre1, nre2) :*> nrs
                              , model = m })
                     b@(Bindings { name_gen = ng })
    | higher_ord <- L.filter (isTyFun . typeOf) $ E.symbolicIds eenv
    , not (null higher_ord) = do
        let stck' = Stck.push (CurrExprFrame (EnsureEq nre2) cexpr) stck

        let cexpr' = CurrExpr Evaluate nre1

        let (ng', new_lam_is) = L.mapAccumL (\ng_ ts -> swap $ freshIds ts ng_) ng (map anonArgumentTypes higher_ord)
            (new_sym_gen, ng'') = freshIds (map returnType higher_ord) ng'

            es = map (\(f_id, lam_i, sg_i) -> (f_id, mkLams (zip (repeat TermL) lam_i) (Var sg_i)) )
               $ zip3 higher_ord new_lam_is new_sym_gen

            eenv' = foldr (uncurry E.insert) eenv (map (\(i, e) -> (idName i, e)) es)
            eenv'' = foldr E.insertSymbolic eenv' new_sym_gen
            m' = foldr (\(i, e) -> HM.insert (idName i) e) m es

        let s' = s { expr_env = eenv''
                , curr_expr = cexpr'
                , model = m'
                , exec_stack = stck'
                , non_red_path_conds = nrs
                }

        return (InProgress, [(s', ())], b { name_gen = ng'' })
nonRedPCRedConstFunc _ s b = return (Finished, [], b)

{-# INLINE taggerRed #-}
taggerRed :: Monad m => Name -> Reducer m () t
taggerRed n = mkSimpleReducer (const ()) (taggerRedStep n)

taggerRedStep :: Monad m => Name -> RedRules m () t
taggerRedStep n _ s@(State {tags = ts}) b@(Bindings { name_gen = ng }) =
    let
        (n'@(Name n_ m_ _ _), ng') = freshSeededName n ng
    in
    if null $ HS.filter (\(Name n__ m__ _ _) -> n_ == n__ && m_ == m__) ts then
        return (Finished, [(s {tags = HS.insert n' ts}, ())], b { name_gen = ng' })
    else
        return (Finished, [(s, ())], b)


getLogger :: (MonadIO m, SM.MonadState PrettyGuide m, Show t) => Config -> Maybe (Reducer m () t)
getLogger config = case logStates config of
                        Log Raw fp -> Just (simpleLogger fp)
                        Log Pretty fp -> Just (prettyLogger fp)
                        NoLog -> Nothing

-- | A Reducer to producer logging output 
simpleLogger :: (MonadIO m, Show t) => FilePath -> Reducer m () t
simpleLogger fn =
    (mkSimpleReducer (const ())
                     (\_ s b -> do
                        liftIO $ outputState fn (log_path s) s b pprExecStateStr
                        return (NoProgress, [(s, ())], b) ))
                    { updateWithAll = \s -> map (\(s, i) -> s { log_path = log_path s ++ [i]} ) $ zip s [1..] }

-- | A Reducer to producer logging output 
prettyLogger :: (MonadIO m, SM.MonadState PrettyGuide m, Show t) => FilePath -> Reducer m () t
prettyLogger fp =
    (mkSimpleReducer
        (const ())
        (\_ s b -> do
            pg <- SM.get
            let pg' = updatePrettyGuide (s { track = () }) pg
            SM.put pg'
            liftIO $ outputState fp (log_path s) s b (\s_ _ -> T.unpack $ prettyState pg' s_)
            return (NoProgress, [(s, ())], b)
        )

    ) { updateWithAll = \s -> map (\(s, i) -> s { log_path = log_path s ++ [i]} ) $ zip s [1..]
      , onAccept = \s b ll -> do 
                                liftIO . putStrLn $ "Accepted on path " ++ show ll
                                return (s,b)
      , onDiscard = \_ ll -> liftIO . putStrLn $ "Discarded path " ++ show ll }

-- | Used to restrict the LimLogger to only output paths that could reach or have reached
-- certain concretization, or that could satisfy certain path constraints.  For example,
-- if the ConcPCGuide has input_vars `x, y`, and path constraints `x > y && x > 10`, we
-- would log states with input_vars `a, b` and path constraints:
--      * `a > 0` since it could still be true that `a > b && a > 10`
--      * `a >= b` && b < -7`
-- We would not log states with the path constraints:
--      * `a < 10` since this violates the requirement that `a > 10` 
data ConcPCGuide = ConcPCGuide { l_input_ids :: [Name] -- ^ Logged input Ids for symbolic arguments
                               , l_sym_gens :: S.Seq Name -- ^ Logged variable names generated by logging `SymGen`s
                               , l_conc :: E.ExprEnv -- ^ Concretizations of (previously) symbolic variables 
                               , l_path_conds :: PathConds
                               }
                               deriving (Show, Read)

matchesConcPCGuide :: [Name] -> State t -> SomeSolver -> ConcPCGuide -> IO Bool
matchesConcPCGuide inp_ids
                   s@(State { expr_env = eenv, sym_gens = sgs, path_conds = pc })
                   some_solver
                     (ConcPCGuide { l_input_ids = cpc_ins, l_sym_gens = l_sgs, l_conc = cpc_eenv, l_path_conds = l_pc }) = do
    let ins_vars = map (Var . flip Id TyUnknown) inp_ids
        cpc_vars = map (Var . flip Id TyUnknown) cpc_ins

        sgs_vars = map (Var . flip Id TyUnknown) $ toList sgs
        l_sgs_vars = map (Var . flip Id TyUnknown) $ toList l_sgs

        m_hm = foldrMatchesExprEnv eenv cpc_eenv HM.empty ins_vars cpc_vars
        m_hm' = (\hm -> foldrMatchesExprEnv eenv cpc_eenv hm sgs_vars l_sgs_vars) =<< m_hm

    case m_hm' of
        Just hm -> do
            let hm_pc = PC.fromList 
                      . map (flip ExtCond True)
                      . map (\(i, e) -> (App (App (Prim Eq TyUnknown) (Var i)) e))
                      $ HM.toList hm
                chck_pc_eq = PC.union hm_pc $ PC.union pc l_pc
            
            case some_solver of
                SomeSolver solver -> do
                    res <- check solver s chck_pc_eq
                    return (case res of SAT _ -> True; _ -> False)
        Nothing -> return False

foldrMatchesExprEnv  :: ExprEnv -> ExprEnv -> HM.HashMap Id Expr -> [Expr] -> [Expr] -> Maybe (HM.HashMap Id Expr)
foldrMatchesExprEnv eenv1 eenv2 hm es1 es2 = 
    foldr
        (\(e1, e2) -> maybe Nothing (\hm' -> matchesExprEnvs eenv1 eenv2 hm' e1 e2))
        (Just hm)
        $ zip es1 es2

-- Is the first expr_env less specific (corresponds to more actual executions) than the second?
matchesExprEnvs :: ExprEnv -> ExprEnv -> HM.HashMap Id Expr -> Expr -> Expr -> Maybe (HM.HashMap Id Expr)
matchesExprEnvs eenv1 eenv2 hm (Var (Id n1 _)) (Var (Id n2 _))
    | Just (E.Sym i1@(Id _ t)) <- e1
    , Just (E.Sym i2) <- e2 =
        if isPrimType t then Just $ HM.insert i1 (Var i2) hm else Just hm

    | Just (E.Sym i1@(Id _ t)) <- e1
    , Just (E.Conc e2') <- e2 =
        if isPrimType t then Just $ HM.insert i1 e2' hm else Just hm

    | Just (E.Conc e1') <- e1
    , Just (E.Sym i2@(Id _ t)) <- e2 =
        if isPrimType t then Just $ HM.insert i2 e1' hm else Just hm

    | Just (E.Conc c1) <- e1
    , Just (E.Conc c2) <- e2 = matchesExprEnvs eenv1 eenv2 hm c1 c2
    where
        e1 = E.lookupConcOrSym n1 eenv1
        e2 = E.lookupConcOrSym n2 eenv2
matchesExprEnvs _ _ hm (Lit l1) (Lit l2) = if l1 == l2 then Just hm else Nothing
matchesExprEnvs eenv1 eenv2 hm e1 e2
    | Data d1:es1 <- unApp e1
    , Data d2:es2 <- unApp e2
    , dc_name d1 == dc_name d2 = foldrMatchesExprEnv eenv1 eenv2 hm es1 es2
matchesExprEnvs eenv1 eenv2 hm (Cast e1 _) (Cast e2 _) = matchesExprEnvs eenv1 eenv2 hm e1 e2
matchesExprEnvs _ _ _ _ _ = Nothing

-- | A Reducer to producer limited logging output.
data LimLogger =
    LimLogger { every_n :: Int -- Output a state every n steps
              , after_n :: Int -- Only begin outputting after passing a certain n
              , before_n :: Maybe Int -- Only output before a certain n
              , down_path :: [Int] -- Output states that have gone down or are going down the given path prefix
              , conc_pc_guide :: Maybe (SomeSolver, ConcPCGuide)
              , lim_output_path :: String
              }

limLoggerConfig :: FilePath -> LimLogger
limLoggerConfig fp = LimLogger { every_n = 0
                               , after_n = 0
                               , before_n = Nothing
                               , down_path = []
                               , conc_pc_guide = Nothing
                               , lim_output_path = fp }

newtype LLTracker = LLTracker { ll_count :: Int }

getLimLogger :: (MonadIO m, SM.MonadState PrettyGuide m, Show t) => Config -> IO (Maybe (Reducer m LLTracker t))
getLimLogger config = do
    cpg <- maybe
                (return Nothing)
                (\fp -> do
                    con <- getZ3 False 10000
                    let solver = ADTNumericalSolver arbValue con
                    c <- readFile fp
                    return $ Just (SomeSolver solver, read c))
                $ logConcPCGuide config
    let ll_config = case logStates config of
                        Log _ fp -> (limLoggerConfig fp) { after_n = logAfterN config
                                                         , every_n = logEveryN config
                                                         , conc_pc_guide = cpg
                                                         , down_path = logPath config }
                        NoLog -> limLoggerConfig ""
    
    case logStates config of
            Log Raw _ -> return . Just . limLogger $ ll_config
            Log Pretty _ -> return . Just . prettyLimLogger $ ll_config
            NoLog -> return Nothing

genLimLogger :: (MonadIO m, Show t) => ([Int] -> State t -> Bindings -> m ()) -> LimLogger -> Reducer m LLTracker t
genLimLogger out_f ll@(LimLogger { after_n = aft, before_n = bfr, down_path = down, conc_pc_guide = cpg }) =
    (mkSimpleReducer (const $ LLTracker { ll_count = every_n ll }) rr)
        { updateWithAll = updateWithAllLL
        , onAccept = \s b _ -> do
                    whenM (liftIO $ maybe (return True) (uncurry (matchesConcPCGuide (input_names b) s)) cpg)
                          (liftIO $ outputConcPCGuide (lim_output_path ll) (log_path s) s b)
                    liftIO . putStrLn $ "Accepted on path " ++ show (log_path s)
                    return (s, b)
        , onDiscard = \s _ -> liftIO . putStrLn $ "Discarded path " ++ show (log_path s)}
    where
        rr llt@(LLTracker { ll_count = c }) s b
            | down `L.isPrefixOf` log_path s || log_path s `L.isPrefixOf` down
            , aft <= length_rules && maybe True (length_rules <=) bfr
            , c <= 1 = do
                whenM (liftIO $ maybe (return True) (uncurry (matchesConcPCGuide (input_names b) s)) cpg)
                      (out_f (log_path s) s b)
                return (NoProgress, [(s, llt { ll_count = every_n ll })], b)
            | c <= 1 =
                return (NoProgress, [(s, llt { ll_count = every_n ll })], b)
            where
                length_rules = length (rules s)
        rr llt@(LLTracker {ll_count = n}) s b =
            return (NoProgress, [(s, llt { ll_count = n - 1 })], b)

        updateWithAllLL [s] = [s]
        updateWithAllLL ss =
            map (\(s, i) -> s { log_path = log_path s ++ [i] }) $ zip ss [1..]

limLogger :: (MonadIO m, Show t) => LimLogger -> Reducer m LLTracker t
limLogger ll = genLimLogger (\off s b -> liftIO $ outputState (lim_output_path ll) off s b pprExecStateStr) ll

prettyLimLogger :: (MonadIO m, SM.MonadState PrettyGuide m, Show t) => LimLogger -> Reducer m LLTracker t
prettyLimLogger ll =
    genLimLogger (\off s b -> do
                pg <- SM.get
                let pg' = updatePrettyGuide (s { track = () }) pg
                SM.put pg'
                liftIO $ outputState (lim_output_path ll) off s b (\s_ _ -> T.unpack $ prettyState pg' s_)
    ) ll
 

outputState :: FilePath -> [Int] -> State t -> Bindings -> (State t -> Bindings -> String) -> IO ()
outputState dn is s b printer = do
    fn <- getFile dn is ("state" ++ show (length $ rules s))

    -- Don't re-output states that  already exist
    exists <- doesPathExist fn

    if not exists
        then do
            let write = printer s b
            writeFile fn write

            putStrLn fn
        else return ()

outputConcPCGuide :: FilePath -> [Int] -> State t -> Bindings -> IO ()
outputConcPCGuide fp is s b = do
    conc_file <- liftIO $ getFile fp is "conc_pc_guide"
    putStrLn conc_file
    let cpg = ConcPCGuide  { l_input_ids = input_names b
                           , l_sym_gens = sym_gens s
                           , l_conc = expr_env s
                           , l_path_conds = path_conds s
                           }
    -- Don't re-output states that  already exist
    exists <- doesPathExist conc_file

    if not exists
        then do
            writeFile conc_file (show cpg)
        else return ()


getFile :: String -> [Int] -> String -> IO String
getFile dn is n = do
    let dir = dn ++ "/" ++ foldl' (\str i -> str ++ show i ++ "/") "" is
    createDirectoryIfMissing True dir
    let fn = dir ++ n ++ ".txt"
    return fn

-- | Output each path and current expression on the command line
currExprLogger :: (MonadIO m, SM.MonadState PrettyGuide m, Show t) => LimLogger -> Reducer m LLTracker t
currExprLogger ll@(LimLogger { after_n = aft, before_n = bfr, down_path = down }) = 
    (mkSimpleReducer (const $ LLTracker { ll_count = every_n ll }) rr)
        { updateWithAll = updateWithAllLL
        , onAccept = \s b _ -> do
                                liftIO . putStrLn $ "Accepted on path " ++ show (log_path s)
                                return (s, b)
        , onDiscard = \s _ -> liftIO . putStrLn $ "Discarded path " ++ show (log_path s)}
    where
        rr llt@(LLTracker { ll_count = 0  }) s b
            | down `L.isPrefixOf` log_path s || log_path s `L.isPrefixOf` down
            , aft <= length_rules && maybe True (length_rules <=) bfr = do
                liftIO $ print (log_path s)
                pg <- SM.get
                let pg' = updatePrettyGuide (s { track = () }) pg
                SM.put pg'
                liftIO . T.putStrLn $ printHaskellDirtyPG pg' (getExpr s)
                return (NoProgress, [(s, llt { ll_count = every_n ll })], b)
            | otherwise =
                return (NoProgress, [(s, llt { ll_count = every_n ll })], b)
            where
                length_rules = length (rules s)
        rr llt@(LLTracker {ll_count = n}) s b =
            return (NoProgress, [(s, llt { ll_count = n - 1 })], b)

        updateWithAllLL [s] = [s]
        updateWithAllLL ss =
            map (\(s, i) -> s { log_path = log_path s ++ [i] }) $ zip ss [1..]

acceptTimeLogger :: MonadIO m => IO (Reducer m () t)
acceptTimeLogger = do
    init_time <- getTime Realtime
    return (mkSimpleReducer (\_ -> ()) (\rv s b -> return (NoProgress, [(s, rv)], b)))
                        { onSolved = liftIO $ do
                            accept_time <- getTime Realtime
                            let diff = diffTimeSpec accept_time init_time
                                diff_secs = (fromInteger (toNanoSecs diff)) / (10 ^ (9 :: Int) :: Double)
                            putStr "State Accepted Time: "
                            print diff_secs
                            return () }

numStepsLogger :: MonadIO m => Reducer m () t
numStepsLogger = do
    (mkSimpleReducer (\_ -> ()) (\rv s b -> return (NoProgress, [(s, rv)], b)))
                        { onAccept = \s b _ -> liftIO $ do
                            putStr "State Accepted Num Steps: "
                            print (num_steps s)
                            return (s, b) }

-- * Halters
--
-- $halters
--

-- We use C to combine the halter values for HCombiner
-- We should never define any other instance of Halter with C, or export it
-- because this could lead to undecidable instances
data C a b = C a b deriving Eq

instance (ASTContainer a Expr, ASTContainer b Expr) => ASTContainer (C a b) Expr where
    containedASTs (C a b) = containedASTs a ++ containedASTs b
    modifyContainedASTs f (C a b) = C (modifyContainedASTs f a) (modifyContainedASTs f b)

instance (ASTContainer a Type, ASTContainer b Type) => ASTContainer (C a b) Type where
    containedASTs (C a b) = containedASTs a ++ containedASTs b
    modifyContainedASTs f (C a b) = C (modifyContainedASTs f a) (modifyContainedASTs f b)

instance (Named a, Named b) => Named (C a b) where
    names (C a b) = names a <> names b
    rename old new (C a b) = C (rename old new a) (rename old new b)
    renames hm (C a b) = C (renames hm a) (renames hm b)

-- | Allows executing multiple halters.
-- If the halters disagree, prioritizes the order:
-- Discard, Accept, Switch, Continue
(<~>) :: Monad m => Halter m hv1 r t -> Halter m hv2 r t -> Halter m (C hv1 hv2) r t
h1 <~> h2 =
    Halter {
              initHalt = \s ->
                let
                    hv1 = initHalt h1 s
                    hv2 = initHalt h2 s
                in
                C hv1 hv2

            , updatePerStateHalt = \(C hv1 hv2) proc s ->
                let
                    hv1' = updatePerStateHalt h1 hv1 proc s
                    hv2' = updatePerStateHalt h2 hv2 proc s
                in
                C hv1' hv2'

            , discardOnStart = \(C hv1 hv2) proc s ->
                let
                    b1 = discardOnStart h1 hv1 proc s
                    b2 = discardOnStart h2 hv2 proc s
                in
                b1 || b2

            , stopRed = \(C hv1 hv2) proc s -> do
                hc1 <- stopRed h1 hv1 proc s
                hc2 <- stopRed h2 hv2 proc s

                return $ min hc1 hc2

            , stepHalter = \(C hv1 hv2) proc xs s ->
                let
                    hv1' = stepHalter h1 hv1 proc xs s
                    hv2' = stepHalter h2 hv2 proc xs s
                in
                C hv1' hv2'

            , updateHalterWithAll = \shv ->
                let
                    shv1 = map (\(s, C hv1 _) -> (s, hv1)) shv
                    shv2 = map (\(s, C _ hv2) -> (s, hv2)) shv

                    shv1' = updateHalterWithAll h1 shv1
                    shv2' = updateHalterWithAll h2 shv2
                in
                map (uncurry C) $ zip shv1' shv2'
            }
{-# INLINE (<~>) #-}


(.<~>) :: Monad m => SomeHalter m r t -> SomeHalter m r t -> SomeHalter m r t
SomeHalter h1 .<~> SomeHalter h2 = SomeHalter (h1 <~> h2)

{-# INLINE (.<~>) #-}

{-# INLINE swhnfHalter #-}
swhnfHalter :: Monad m => Halter m () r t
swhnfHalter = mkStoppingHalter stop
    where
        stop _ _ s =
            case isExecValueForm s of
                True -> return Accept
                False -> return Continue

-- | Accepts a state when it is in SWHNF and true_assert is true
-- Discards it if in SWHNF and true_assert is false
acceptIfViolatedHalter :: Monad m => Halter m () r t
acceptIfViolatedHalter = mkStoppingHalter stop
    where
        stop _ _ s =
            case isExecValueForm s of
                True
                    | true_assert s -> return Accept
                    | otherwise -> return Discard
                False -> return Continue

-- | Allows execution to continue until the step counter hits 0, then discards the state
zeroHalter :: Monad m => Int -> Halter m Int r t
zeroHalter n = mkSimpleHalter
                    (const n)
                    (\h _ _ -> h)
                    (\h _ _ -> if h == 0 then return Discard else return Continue)
                    (\h _ _ _ -> h - 1)

maxOutputsHalter :: Monad m => Maybe Int -> Halter m (Maybe Int) r t
maxOutputsHalter m = mkSimpleHalter
                        (const m)
                        (\hv _ _ -> hv)
                        (\_ (Processed {accepted = acc}) _ ->
                            case m of
                                Just m' -> return $ if length acc >= m' then Discard else Continue
                                _ -> return Continue)
                        (\hv _ _ _ -> hv)

-- | Switch execution every n steps
{-# INLINE switchEveryNHalter #-}
switchEveryNHalter :: Monad m => Int -> Halter m Int r t
switchEveryNHalter sw = (mkSimpleHalter
                            (const sw)
                            (\_ _ _ -> sw)
                            (\i _ _ ->  (return $ if i <= 0 then Switch else Continue))
                            (\i _ _ _ -> i - 1))
                        { updateHalterWithAll = updateAll }
    where
        updateAll [] = []
        updateAll xs@((_, c):_) =
            let
                len = length xs
                c' = c `quot` len
            in
            replicate len c'

-- | If the Name, disregarding the Unique, matches a Tag in the Accepted State list,
-- and in the State being evaluated, discard the State.
discardIfAcceptedTagHalter :: Monad m =>
                              Bool -- ^ If True, consider only accepted states that are non-erroring
                           -> Name
                           -> Halter m (HS.HashSet Name) (ExecRes t) t
discardIfAcceptedTagHalter non_erroring (Name n m _ _) =
                            mkSimpleHalter
                                (const HS.empty)
                                ups
                                (\ns _ _ -> if not (HS.null ns) then return Discard else return Continue)
                                (\hv _ _ _ -> hv)
    where
        ups _
            (Processed {accepted = acc})
            (State {tags = ts}) =
                let
                    acc_states = case non_erroring of
                                    True -> filter (not . isError . getExpr . final_state) acc
                                    False -> acc
                    allAccTags = HS.unions $ map (tags . final_state) acc_states
                    matchCurrState = HS.intersection ts allAccTags
                in
                HS.filter (\(Name n' m' _ _) -> n == n' && m == m') matchCurrState
            
        isError (Prim Error _) = True
        isError (Prim Undefined _) = True
        isError _ = False

-- | Counts the number of variable lookups are made, and switches the state
-- whenever we've hit a threshold
varLookupLimitHalter :: Monad m => Int -> Halter m Int r t
varLookupLimitHalter lim = mkSimpleHalter
                        (const lim)
                        (\_ _ _ -> lim)
                        (\l _ _ -> return $ if l <= 0 then Switch else Continue)
                        step
    where
        step l _ _ (State { curr_expr = CurrExpr Evaluate (Var _) }) = l - 1
        step l _ _ _ = l

hpcApproximationHalter :: (Solver solver, SM.MonadState (ApproxPrevs t) m, MonadIO m) =>
                          solver
                       -> HS.HashSet Name -- ^ Names that should not be inlined (often: top level names from the original source code)
                       -> Halter m () (ExecRes  t) t
hpcApproximationHalter = approximationHalter' stop_cond
    where
        stop_cond pr s =
            let acc_seen_hpc = HS.unions (map (reached_hpc . final_state) $ accepted pr) in
            HS.null $ HS.difference (reached_hpc s) acc_seen_hpc

approximationHalter :: (Solver solver, SM.MonadState(ApproxPrevs t) m, MonadIO m) =>
                       solver
                    -> HS.HashSet Name -- ^ Names that should not be inlined (often: top level names from the original source code)
                    -> Halter m () r t
approximationHalter = approximationHalter' (\_ _ -> True)

approximationHalter' :: (Solver solver, SM.MonadState (ApproxPrevs t) m, MonadIO m) =>
                        (Processed r (State t) -> State t -> Bool) -- ^ Approximated states are discarded only if they match this condition
                     -> solver
                     -> HS.HashSet Name -- ^ Names that should not be inlined (often: top level names from the original source code)
                     -> Halter m () r t
approximationHalter' stop_cond solver no_inline = mkSimpleHalter
                                                        (const ())
                                                        (\hv _ _ -> hv)
                                                        stop
                                                        (\hv _ _ _ -> hv)
    where
        stop _ pr s
            | maybe True (allowed_frame . fst) (Stck.pop (exec_stack s))
            
            , s'@(State { curr_expr = CurrExpr Evaluate e}) <- stateAdjStack s
            -- , Stck.null (exec_stack s')
            , Var _:_:_ <- stripAllTicks $ unApp e 

            , not . isTyFun . typeOf $ e = do
                liftIO $ do
                    putStrLn $ "approx halter log_path s = " ++ show (log_path s) ++ " " ++ show (num_steps s)
                    putStrLn $ "curr_expr s = " ++ show (curr_expr s')
                    putStrLn $ "stack s = " ++ show (exec_stack s')
                xs <- SM.gets ap_halter_states
                let xs' = filter (\x -> num_steps x < num_steps s') xs
                approx <- liftIO $ findM (\prev -> moreRestrictiveIncludingPCAndNRPC
                                                        solver
                                                        mr_cont
                                                        gen_lemma
                                                        lookupConcOrSymState
                                                        no_inline
                                                        prev
                                                        s'
                                                ) xs'
                if isJust approx && stop_cond pr s
                    then do liftIO $ do
                                putStrLn $ "log_path s = " ++ show (log_path s) ++ " " ++ show (num_steps s)
                                putStrLn $ "log_path approx = " ++ show (log_path $ fromJust approx) ++ " " ++ show (num_steps $ fromJust approx)
                                return Discard
                    else do SM.modify ((\ap -> ap { ap_halter_states = s':xs })); return Continue
        -- stop _ _ s | log_path s == [1, 1, 1, 1]
        --            , num_steps s == 103
        --            , s'@(State { curr_expr = CurrExpr _ e}) <- stateAdjStack s = error $
        --                 "maybe True (allowed_frame . fst) (Stck.pop (exec_stack s)) = "
        --                     ++ show (maybe True (allowed_frame . fst) (Stck.pop (exec_stack s)))
        --                 ++ "e = " ++ show (curr_expr s')
        --                 ++ "not . isTyFun . typeOf $ e = " ++ show (not . isTyFun . typeOf $ e)
        stop _ _ _ = return Continue
        
        -- mr_cont _ _ _ _ _ _ _ _ _ = Left []
        mr_cont = mrContIgnoreNRPCTicks gen_lemma lookupConcOrSymState
        gen_lemma s1 s2 _ e1 e2 =
            trace ("log_path s1 = " ++ show (log_path s1) ++ " " ++ show (num_steps s1)
                ++ "\nlog_path s2 = " ++ show (log_path s2) ++ " " ++ show (num_steps s2)
                ++ "\ne1 = " ++ show e1 ++ "\ne2 = " ++ show e2)
            (e1, e2)

        allowed_frame (ApplyFrame _) = False
        allowed_frame (UpdateFrame _) = False
        allowed_frame _ = True

mrContIgnoreNRPCTicks :: GenerateLemma t l
                      -> Lookup t
                      -> State t
                      -> State t
                      -> HS.HashSet Name
                      -> (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
                      -> Bool -- ^ indicates whether this is part of the "active expression"
                      -> [(Name, Expr)] -- ^ variables inlined previously on the LHS
                      -> [(Name, Expr)] -- ^ variables inlined previously on the RHS
                      -> Expr
                      -> Expr
                      -> Either [l] (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
mrContIgnoreNRPCTicks genLemma lkp s1 s2 ns hm active n1 n2 e1 e2 =
    case (e1, e2) of
        (Tick t1 e1', Tick t2 e2') | t1 /= t2 ->
            moreRestrictive' (mrContIgnoreNRPCTicks genLemma lkp) genLemma lkp s1 s2 ns hm active n1 n2 e1' e2'
        _ -> Left []


type HPCMemoTable = HM.HashMap Name (HS.HashSet (Int, T.Text))

noNewHPCHalter :: SM.MonadState HPCMemoTable m => HS.HashSet (Maybe T.Text) -> Halter m Int (ExecRes t) t
noNewHPCHalter mod_name = mkSimpleHalter
                                (const 0)
                                (\hv _ _ -> hv)
                                stop
                                (\hv _ _ _ -> if hv < 100 then hv + 1 else 0)
    where
        stop hv pr s
            | hv == 100 = do
                let acc_seen_hpc = HS.unions (map (reached_hpc . final_state) $ accepted pr)

                    diff1 = HS.difference (reached_hpc s) acc_seen_hpc

                if HS.null diff1
                    then do
                        reachable_hpc <- reachesHPC (expr_env s) (curr_expr s, exec_stack s, non_red_path_conds s)
                        let diff2 = HS.difference reachable_hpc acc_seen_hpc
                        if HS.null diff2 then do return Discard else do return Continue
                    else return Continue
            | otherwise = return Continue
        
        reachesHPC :: (SM.MonadState HPCMemoTable m, ASTContainer c Expr) => ExprEnv -> c -> m (HS.HashSet (Int, T.Text))
        reachesHPC eenv es = mconcat <$> mapM (reaches eenv) (containedASTs es) 

        reaches :: SM.MonadState HPCMemoTable m => ExprEnv -> Expr -> m (HS.HashSet (Int, T.Text))
        reaches eenv (Var (Id n _)) = do
            seen <- SM.get
            case HM.lookup n seen of
                Just hpcs -> return hpcs
                Nothing -> do
                    SM.modify (HM.insert n HS.empty)
                    hpcs <- maybe (return HS.empty) (reaches eenv) (E.lookup n eenv)
                    SM.modify (HM.insert n hpcs)
                    return hpcs
        reaches eenv (Tick (HpcTick i t) e) | Just t `HS.member` mod_name = HS.insert (i, t) <$> reaches eenv e
        reaches eenv e = mconcat <$> mapM (reaches eenv) (children e)

acceptOnlyNewHPC :: (Monad m1, SM.MonadState HPCMemoTable (m2 m1), SM.MonadTrans m2) => Halter m1 r (ExecRes t) t -> Halter (m2 m1) r (ExecRes t) t
acceptOnlyNewHPC h = 
        Halter {
              initHalt = initHalt h
            , updatePerStateHalt = updatePerStateHalt h
            , discardOnStart = discardOnStart h
            , stopRed = stop
            , stepHalter = stepHalter h
            , updateHalterWithAll = updateHalterWithAll h
            }
    where
        stop hv pr s = do
            res <- SM.lift $ stopRed h hv pr s
            case res of
                Accept -> do
                    let acc_seen_hpc = HS.unions (map (reached_hpc . final_state) $ accepted pr)
                        diff1 = HS.difference (reached_hpc s) acc_seen_hpc
                    if HS.null diff1 then return Discard else return Accept
                r -> return r

-- liftHalter :: (Monad m1, SM.MonadTrans m2) => Halter m1 rv r t -> Halter (m2 m1) rv r t
-- liftHalter h = Halter { initHalt = initHalt h
--                       , updatePerStateHalt = updatePerStateHalt h
--                       , discardOnStart = discardOnStart h
--                       , stopRed = \hv pr s -> SM.lift ((stopRed h) hv pr s)
--                       , stepHalter = stepHalter h
--                       , updateHalterWithAll = updateHalterWithAll h }

{-# INLINE stdTimerHalter #-}
stdTimerHalter :: (MonadIO m, MonadIO m_run) => NominalDiffTime -> m (Halter m_run Int r t)
stdTimerHalter ms = timerHalter ms Discard 10

{-# INLINE timerHalter #-}
timerHalter :: (MonadIO m, MonadIO m_run) => NominalDiffTime -> HaltC -> Int -> m (Halter m_run Int r t)
timerHalter ms def ce = do
    curr <- liftIO $ getCurrentTime
    return $ mkSimpleHalter
                (const 0)
                (\_ _ _ -> 0)
                (stop curr)
                step
    where
        stop it v (Processed { accepted = acc }) _
            | v == 0 = do
                curr <- liftIO $ getCurrentTime
                let diff = diffUTCTime curr it

                if diff > ms
                    then return def
                    else return Continue
            | otherwise = return Continue

        step v _ _ _
            | v >= ce = 0
            | otherwise = v + 1

-- | Print a specified message if a specified HaltC is returned from the contained Halter
printOnHaltC :: MonadIO m =>
                HaltC -- ^ The HaltC to watch for
             -> String -- ^ The message to print
             -> Halter m hv r t -- ^ The contained Halter
             -> Halter m hv r t
printOnHaltC watch mes h =
    h { stopRed = \hv pr s -> do
                        halt_c <- stopRed h hv pr s
                        if halt_c == watch then liftIO $ putStrLn mes else return ()
                        return halt_c }

-- * Orderers
--
-- $orderers
--

(<->) :: Monad m => Orderer m sov1 b1 r t -> Orderer m sov2 b2 r t -> Orderer m (C sov1 sov2) (b1, b2) r t
or1 <-> or2 = Orderer {
      initPerStateOrder = \s ->
          let
              sov1 = initPerStateOrder or1 s
              sov2 = initPerStateOrder or2 s
          in
          C sov1 sov2

    , orderStates = \(C sov1 sov2) pr s -> do
          sov1' <- orderStates or1 sov1 pr s
          sov2' <- orderStates or2 sov2 pr s
          return (sov1', sov2')

    , updateSelected = \(C sov1 sov2) proc s ->
          let
              sov1' = updateSelected or1 sov1 proc s
              sov2' = updateSelected or2 sov2 proc s
          in
          C sov1' sov2'

    , stepOrderer = \(C sov1 sov2) proc xs s -> do
            sov1' <- stepOrderer or1 sov1 proc xs s
            sov2' <- stepOrderer or2 sov2 proc xs s
            
            return (C sov1' sov2')
    }

ordComb :: Monad m => (v1 -> v2 -> v3) -> Orderer m sov1 v1 r t  -> Orderer m sov2 v2 r t -> Orderer m (C sov1 sov2) v3 r t
ordComb f or1 or2 = Orderer {
      initPerStateOrder = \s ->
          let
              sov1 = initPerStateOrder or1 s
              sov2 = initPerStateOrder or2 s
          in
          C sov1 sov2

    , orderStates = \(C sov1 sov2) pr s -> do
          sov1' <- orderStates or1 sov1 pr s
          sov2' <- orderStates or2 sov2 pr s
          return (f sov1' sov2')

    , updateSelected = \(C sov1 sov2) proc s ->
          let
              sov1' = updateSelected or1 sov1 proc s
              sov2' = updateSelected or2 sov2 proc s
          in
          C sov1' sov2'

    , stepOrderer = \(C sov1 sov2) proc xs s -> do
          sov1' <- stepOrderer or1 sov1 proc xs s
          sov2' <- stepOrderer or2 sov2 proc xs s
          return (C sov1' sov2')
    }

nextOrderer :: Monad m => Orderer m () Int r t
nextOrderer = mkSimpleOrderer (const ()) (\_ _ _ -> return 0) (\v _ _ -> v)

-- | Continue execution on the state that has been picked the least in the past. 
pickLeastUsedOrderer :: Monad m => Orderer m Int Int r t
pickLeastUsedOrderer = mkSimpleOrderer (const 0) (\v _ _ -> return v) (\v _ _ -> v + 1)

-- | Floors and does bucket size
bucketSizeOrderer :: Monad m => Int -> Orderer m Int Int r t
bucketSizeOrderer b =
    mkSimpleOrderer (const 0)
                    (\v _ _ -> return $ floor (fromIntegral v / fromIntegral b :: Float))
                    (\v _ _ -> v + 1)

-- | Orders by the size (in terms of height) of (previously) symbolic ADT.
-- In particular, aims to first execute those states with a height closest to
-- the specified height.
adtHeightOrderer :: Monad m => Int -> Maybe Name -> Orderer m (HS.HashSet Name, Bool) Int r t
adtHeightOrderer pref_height mn =
    (mkSimpleOrderer initial
                    order
                    (\v _ _ -> v))
                    { stepOrderer = \sov pr st s -> return $ step sov pr st s }
    where
        -- Normally, each state tracks the names of currently symbolic variables,
        -- but here we want all variables that were ever symbolic.
        -- To track this, we use a HashSet.
        -- The tracked bool is to speed up adjusting this hashset- if it is set to false,
        -- we do not update the hashset.  If it is set to true,
        -- after the next step the hashset will be updated, and the bool will be set
        -- back to false.
        -- This avoids repeated operations on the hashset after rules that we know
        -- will not add symbolic variables.
        initial s = (HS.fromList . map idName . E.symbolicIds . expr_env $ s, False)
        order (v, _) _ s =
            let
                m = maximum $ (-1):(HS.toList $ HS.map (flip adtHeight s) v)
                h = abs (pref_height - m)
            in
            return h

        step (v, _) _ _
                      (State { curr_expr = CurrExpr _ (SymGen _ _) }) = (v, True)
        step(v, True) _ _ s =
            (v `HS.union` (HS.fromList . map idName . E.symbolicIds . expr_env $ s), False)
        step (v, _) _ _
                       (State { curr_expr = CurrExpr _ (Tick (NamedLoc n') (Var (Id vn _))) })
                | Just n <- mn, n == n' =
                    (HS.insert vn v, False)
        step  v _ _ _ = v

adtHeight :: Name -> State t -> Int
adtHeight n s@(State { expr_env = eenv })
    | Just (E.Sym _) <- v = 0
    | Just (E.Conc e) <- v =
        1 + adtHeight' e s
    | otherwise = 0
    where
        v = E.lookupConcOrSym n eenv

adtHeight' :: Expr -> State t -> Int
adtHeight' e s =
    let
        _:es = unApp e
    in
    maximum $ 0:map (\e' -> case e' of
                        Var (Id n _) -> adtHeight n s
                        _ -> 0) es

-- | Orders by the combined size of (previously) symbolic ADT.
-- In particular, aims to first execute those states with a combined ADT size closest to
-- the specified zize.
adtSizeOrderer :: Monad m => Int -> Maybe Name -> Orderer m (HS.HashSet Name, Bool) Int r t
adtSizeOrderer pref_height mn =
    (mkSimpleOrderer initial
                    order
                    (\v _ _ -> v))
                    { stepOrderer = \sov pr st s -> return $ step sov pr st s }
    where
        -- Normally, each state tracks the names of currently symbolic variables,
        -- but here we want all variables that were ever symbolic.
        -- To track this, we use a HashSet.
        -- The tracked bool is to speed up adjusting this hashset- if it is set to false,
        -- we do not update the hashset.  If it is set to true,
        -- after the next step the hashset will be updated, and the bool will be set
        -- back to false.
        -- This avoids repeated operations on the hashset after rules that we know
        -- will not add symbolic variables.
        initial s = (HS.fromList . map idName . E.symbolicIds . expr_env $ s, False)
        order (v, _) _ s =
            let
                m = sum (HS.toList $ HS.map (flip adtSize s) v)
                h = abs (pref_height - m)
            in
            return h

        step (v, _) _ _
                      (State { curr_expr = CurrExpr _ (SymGen _ _) }) = (v, True)
        step (v, True) _ _ s =
            (v `HS.union` (HS.fromList . map idName . E.symbolicIds . expr_env $ s), False)
        step (v, _) _ _
                       (State { curr_expr = CurrExpr _ (Tick (NamedLoc n') (Var (Id vn _))) })
                | Just n <- mn, n == n' = (HS.insert vn v, False)
        step v _ _ _ = v

adtSize :: Name -> State t -> Int
adtSize n s@(State { expr_env = eenv })
    | Just (E.Sym _) <- v = 0
    | Just (E.Conc e) <- v =
        1 + adtSize' e s
    | otherwise = 0
    where
        v = E.lookupConcOrSym n eenv

adtSize' :: Expr -> State t -> Int
adtSize' e s =
    let
        _:es = unApp e
    in
    sum $ 0:map (\e' -> case e' of
                        Var (Id n _) -> adtSize n s
                        _ -> 0) es

-- | Orders by the number of Path Constraints
pcSizeOrderer :: Monad m =>
                 Int  -- ^ What size should we prioritize?
              -> Orderer m () Int r t
pcSizeOrderer pref_height = mkSimpleOrderer (const ())
                                            order
                                            (\v _ _ -> v)
    where
        order _ _ s =
            let
                m = PC.number (path_conds s)
                h = abs (pref_height - m)
            in
            return h

data IncrAfterNTr sov = IncrAfterNTr { steps_since_change :: Int
                                     , incr_by :: Int
                                     , underlying :: sov }

-- | Wraps an existing Orderer, and increases it's value by 1, every time
-- it doesn't change after N steps 
incrAfterN :: (Eq sov, Enum b, Monad m) => Int -> Orderer m sov b r t -> Orderer m (IncrAfterNTr sov) b r t
incrAfterN n ord = (mkSimpleOrderer initial order update) { stepOrderer = step }
    where
        initial s =
            IncrAfterNTr { steps_since_change = 0
                         , incr_by = 0
                         , underlying = initPerStateOrder ord s }

        order sov pr s = do
            b <- orderStates ord (underlying sov) pr s
            return $ succNTimes (incr_by sov) b

        update sov pr s =
            sov { underlying = updateSelected ord (underlying sov) pr s }

        step sov pr xs s = do
            let under = underlying sov
            under' <- stepOrderer ord under pr xs s
            let sov' = sov { underlying = under' }

            if | steps_since_change sov >= n ->
                    return $ sov' { incr_by = incr_by sov' + 1
                                  , steps_since_change = 0 }
               | under /= under' ->
                    return $ sov' { steps_since_change = 0 }
               | otherwise ->
                    return $ sov' { steps_since_change = steps_since_change sov' + 1}

succNTimes :: Enum b => Int -> b -> b
succNTimes x b
    | x <= 0 = b
    | otherwise = succNTimes (x - 1) (succ b)

-- | Wraps an existing orderer, and divides its value by 2 if true_assert is true
quotTrueAssert :: (Monad m, Integral b) => Orderer m sov b r t -> Orderer m sov b r t
quotTrueAssert ord = (mkSimpleOrderer (initPerStateOrder ord)
                                      order
                                      (updateSelected ord))
                                      { stepOrderer = stepOrderer ord}
    where
        order sov pr s = do
            b <- orderStates ord sov pr s
            return (if true_assert s then b `quot` 2 else b)

-- * Analyzers
--
-- $analyzers
--

-- | An event that occurs during symbolic execution
data AnalysisEvent t = StateAccepted (State t) -- ^ The state that was accepted
                     | StateDiscarded (State t) -- ^ The state that was discarded
                     | StateReduced (State t) -- ^ The initial state, pre-reduction
                                    [State t] -- ^ The new states

-- | Output information about all states being symbolically executed.
-- To be run after each symbolic execution step. 
type AnalyzeStates m r t = AnalysisEvent t -- ^ Newly generated states. 
                        -> Processed r (State t) -- ^ Accepted/Rejected States
                        -> [State t] -- ^ All states are are waiting to run
                        -> m ()

noAnalysis :: [AnalyzeStates m r t]
noAnalysis = []

-- | Whenever the number of states grows, output the (new) number of states and the time.
logStatesAtTime :: MonadIO m => IO (AnalyzeStates m r t)
logStatesAtTime = do
    init_time <- getTime Realtime

    let prTime ns as = liftIO $ do
                        curr_time <- getTime Realtime
                        let diff = diffTimeSpec curr_time init_time
                            diff_secs = (fromInteger (toNanoSecs diff)) / (10 ^ (9 :: Int) :: Double)
                        putStr "Time: "
                        putStr (show diff_secs)
                        putStr " Num States: "
                        print (length ns + length as)

    return (\ae _ all_s ->
                case ae of
                    StateReduced _ new_s@(_:_:_) -> prTime new_s all_s
                    StateReduced _ new_s@[] -> prTime new_s all_s
                    StateAccepted _ -> prTime [] all_s
                    StateDiscarded _ -> prTime [] all_s
                    _ -> return ())        

newtype LogStatesAtStep = LSS (M.Map Int Int, Int)

logStatesAtStepTracker :: LogStatesAtStep
logStatesAtStepTracker = LSS (M.empty, 0)

-- | Whenever the number of states that have reached a particular step changes, outputs the number of states.
logStatesAtStep :: (MonadIO m, SM.MonadState LogStatesAtStep m) => AnalyzeStates m r t
logStatesAtStep (StateReduced _ new_s@(s:_)) _ waiting = do
    -- We track a Map of (unprinted step numbers) -> (count of states at that step number)
    -- We can print out the number of states at step N only once there are no live states that have taken < N steps.
    -- We remove step numbers from the map once they are printed.
    --
    -- We also track how many states there were at the last state that we printed- we print only if the number
    -- of states is different than this previous state count.
    LSS (m, last_count_printed) <- SM.get
    let m' = M.alter (Just . maybe (length new_s) (+ length new_s)) (num_steps s) m
    let min_rule_num = minimum $ map num_steps (new_s ++ waiting)

    -- While there is some step count in the map that is less than the current minimum step count
    -- of all live steps, check if it should be printed and delete it from the map.
    let go m_ curr_min = case M.lookupMin m_ of
                            Just (min_key, states_at_min) | min_rule_num >= min_key -> do
                                liftIO $ if states_at_min /= curr_min
                                            then do
                                                putStr "Steps: "
                                                putStr (show min_key)
                                                putStr " Num States: "
                                                print states_at_min
                                            else return ()
                                go (M.delete min_key m_) states_at_min
                            _ -> return (m_, curr_min)
    fm_lcp <- go m' last_count_printed
    SM.put $ LSS fm_lcp
logStatesAtStep (StateDiscarded _) _ [] = do
    LSS (m, last_count_printed) <- SM.get
    let go m_ curr_min = case M.lookupMin m_ of
                        Just (min_key, states_at_min) -> do
                            liftIO $ if states_at_min /= curr_min
                                        then do
                                            putStr "Steps: "
                                            putStr (show min_key)
                                            putStr " At Least Num States: "
                                            print states_at_min
                                        else return ()
                            go (M.delete min_key m_) states_at_min
                        _ -> return ()
    go m last_count_printed
logStatesAtStep _ _ _ = return ()

-- | Outputs the total number of reduction rules after reduction stops.
logRedRuleNum :: (MonadIO m, SM.MonadState Int m) => AnalyzeStates m r t
logRedRuleNum (StateReduced _ _) _ _ = SM.modify (+ 1)
logRedRuleNum (StateDiscarded _) _ [] = do
    n <- SM.get
    liftIO . putStrLn $ "# Red Rules: " ++ show n
logRedRuleNum _ _ _ = return ()

--------
--------

-- | Solve for concrete values in a fully executed state.
type SolveStates m r t = State t -> Bindings -> m (Maybe r)

{-# INLINABLE runReducer #-}
{-# SPECIALIZE runReducer :: Ord b =>
                             Reducer IO rv t
                          -> Halter IO hv r t
                          -> Orderer IO sov b r t
                          -> SolveStates IO r t
                          -> [AnalyzeStates IO r t]
                          -> State t
                          -> Bindings
                          -> IO (Processed r (State t), Bindings)
    #-}
{-# SPECIALIZE runReducer :: Ord b =>
                             Reducer (SM.StateT PrettyGuide IO) rv t
                          -> Halter (SM.StateT PrettyGuide IO) hv r t
                          -> Orderer (SM.StateT PrettyGuide IO) sov b r t
                          -> SolveStates (SM.StateT PrettyGuide IO) r t
                          -> [AnalyzeStates (SM.StateT PrettyGuide IO) r t]
                          -> State t
                          -> Bindings
                          -> SM.StateT PrettyGuide IO (Processed r (State t), Bindings)
    #-}
-- | Uses a passed Reducer, Halter and Orderer to execute the reduce on the State, and generated States
runReducer :: forall m b rv hv sov r t .
              (Monad m, Ord b) =>
              Reducer m rv t
           -> Halter m hv r t
           -> Orderer m sov b r t
           -> SolveStates m r t -- ^ Given a fully executed state, solve for concrete values
           -> [AnalyzeStates m r t] -- ^ Output information about all states being symbolically executed
           -> State t
           -> Bindings
           -> m (Processed r (State t), Bindings)
runReducer red hal ord solve_r analyze init_state init_bindings = do
    let pr = Processed {accepted = [], discarded = []}
    let s' = ExState { state = init_state
                     , reducer_val = initReducer red init_state
                     , halter_val = initHalt hal init_state
                     , order_val = initPerStateOrder ord init_state }

    (states, b') <- runReducer' pr s' init_bindings M.empty
    afterRed red
    return (states, b')
    where
        {-# INLINABLE runReducer' #-}
        runReducer' :: (Monad m, Ord b)
                    => Processed r (State t)
                    -> ExState rv hv sov t
                    -> Bindings
                    -> M.Map b [ExState rv hv sov t]
                    -> m (Processed r (State t), Bindings)
        runReducer' pr rs@(ExState { state = s, reducer_val = r_val, halter_val = h_val, order_val = o_val }) b xs = do
            hc <- stopRed hal h_val pr s
            case () of
                ()
                    | hc == Accept -> do
                        (s', b') <- onAccept red s b r_val
                        er <- solve_r s' b'
                        sequence_ $ analyze <*> pure (StateAccepted s') <*> pure pr <*> pure (map state . concat $ M.elems xs)
                        pr' <- case er of
                                    Just er' -> do
                                        onSolved red
                                        return $ pr {accepted = er':accepted pr}
                                    Nothing -> return pr
                        let jrs = minState pr' xs
                        case jrs of
                            Just (rs', xs') -> switchState pr' rs' b' xs'
                            Nothing -> return (pr', b')
                    | hc == Discard -> do
                        onDiscard red s r_val
                        sequence_ $ analyze <*> pure (StateDiscarded s) <*> pure pr <*> pure (map state . concat $ M.elems xs)
                        let pr' = pr {discarded = state rs:discarded pr}
                            jrs = minState pr' xs
                        case jrs of
                            Just (rs', xs') ->
                                switchState pr' rs' b xs'
                            Nothing -> return (pr', b)
                    | hc == Switch -> do
                        let rs' = rs { order_val = updateSelected ord (order_val rs) pr (state rs) }
                        k <- orderStates ord (order_val rs') pr (state rs)
                        let Just (rs'', xs') = minState pr (M.insertWith (++) k [rs'] xs)
                        switchState pr rs'' b xs'
                    | otherwise -> do
                        (_, reduceds, b') <- redRules red r_val s b
                        let reduceds' = map (\(r, _) -> r {num_steps = num_steps r + 1 }) reduceds
                            reduceds'' = if length reduceds' > 1
                                            then updateWithAll red reduceds' ++ error ("List returned by updateWithAll is too short." ++ show (length (updateWithAll red reduceds')) ++ " " ++ show (length reduceds'))
                                            else reduceds'
                            new_states = take (length reduceds') reduceds''

                            r_vals = map snd reduceds

                            reduceds_h_vals = map (, h_val) new_states
                            h_vals = if length new_states > 1
                                        then updateHalterWithAll hal reduceds_h_vals ++ error "List returned by updateHalterWithAll is too short."
                                        else repeat h_val

                        
                        sequence_ $ analyze <*> pure (StateReduced s new_states) <*> pure pr <*> pure (map state . concat $ M.elems xs)

                        mod_info <- mapM (\(s', r_val', h_val') -> do
                                                or_v <- stepOrderer ord o_val pr new_states s'
                                                return $ rs { state = s'
                                                            , reducer_val = r_val'
                                                            , halter_val = stepHalter hal h_val' pr new_states s'
                                                            , order_val = or_v}) $ zip3 new_states r_vals h_vals




                        case mod_info of
                            (s_h:ss_tail) -> do
                                b_ss_tail <- mapM (\s' -> do
                                                            n_b <- orderStates ord (order_val s') pr (state s')
                                                            return (n_b, s')) ss_tail

                                let xs' = foldr (\(or_b, s') -> M.insertWith (++) or_b [s']) xs b_ss_tail

                                runReducer' pr s_h b' xs'
                            [] -> runReducerList pr xs b'

        {-# INLINABLE switchState #-}
        switchState :: (Monad m, Ord b)
                    => Processed r (State t)
                    -> ExState rv hv sov t
                    -> Bindings
                    -> M.Map b [ExState rv hv sov t]
                    -> m (Processed r (State t), Bindings)
        switchState pr rs b xs
            | not $ discardOnStart hal (halter_val rs') pr (state rs') =
                runReducer' pr rs' b xs
            | otherwise =
                runReducerListSwitching (pr {discarded = state rs':discarded pr}) xs b
            where
                rs' = rs { halter_val = updatePerStateHalt hal (halter_val rs) pr (state rs) }

        {-# INLINABLE runReducerList #-}
        -- To be used when we we need to select a state without switching 
        runReducerList :: (Monad m, Ord b)
                    => Processed r (State t)
                    -> M.Map b [ExState rv hv sov t]
                    -> Bindings
                    -> m (Processed r (State t), Bindings)
        runReducerList pr m binds =
            case minState pr m of
                Just (rs, m') ->
                    let
                        rs' = rs { halter_val = updatePerStateHalt hal (halter_val rs) pr (state rs) }
                    in
                    runReducer' pr rs' binds m'
                Nothing -> return (pr, binds)

        {-# INLINABLE runReducerListSwitching #-}
        -- To be used when we are possibly switching states 
        runReducerListSwitching :: (Monad m, Ord b)
                                => Processed r (State t)
                                -> M.Map b [ExState rv hv sov t]
                                -> Bindings
                                -> m (Processed r (State t), Bindings)
        runReducerListSwitching pr m binds =
            case minState pr m of
                Just (x, m') -> switchState pr x binds m'
                Nothing -> return (pr, binds)

        {-# INLINABLE minState #-}
        -- Uses the Orderer to determine which state to continue execution on.
        -- Returns that State, and a list of the rest of the states 
        minState :: Ord b
                => Processed r (State t)
                -> M.Map b [ExState rv hv sov t]
                -> Maybe (ExState rv hv sov t, M.Map b [ExState rv hv sov t])
        minState pr m =
            case getState m of
            Just (k, x:[]) -> Just (x, M.delete k m)
            Just (k, x:xs) -> Just (x, M.insert k xs m)
            Just (k, []) -> minState pr $ M.delete k m
            Nothing -> Nothing