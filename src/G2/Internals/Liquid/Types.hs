{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Internals.Liquid.Types ( LHOutput (..)
                                 , Measures
                                 , LHState (..)
                                 , LHStateM (..)
                                 , ExState (..)
                                 , consLHState
                                 , deconsLHState
                                 , measuresM
                                 , runLHStateM
                                 , evalLHStateM
                                 , execLHStateM
                                 , lookupMeasure
                                 , lookupMeasureM
                                 , insertMeasureM
                                 , andM
                                 , orM
                                 , notM
                                 , lhTCM
                                 , lhOrdTCM
                                 , lhEqM
                                 , lhNeM
                                 , lhLtM
                                 , lhLeM
                                 , lhGtM
                                 , lhGeM

                                 , lhPlusM
                                 , lhMinusM
                                 , lhTimesM
                                 , lhDivM
                                 , lhNegateM
                                 , lhModM
                                 
                                 , lhPPM ) where

import qualified Control.Monad.State.Lazy as SM

import qualified G2.Internals.Language as L
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.Monad

import G2.Internals.Liquid.TCValues

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Constraint.Types
import Language.Fixpoint.Types.Constraints

data LHOutput = LHOutput { ghcI :: GhcInfo
                         , cgI :: CGInfo
                         , solution :: FixSolution }

type Measures = L.ExprEnv


-- [LHState]
-- measures is an extra expression environment, used to build Assertions.
-- This distinction between functions for code, and functions for asserts is important because
-- Assertions should not themselves contain assertions.  A measure function
-- may be used both in code and in an assertion, but should only have it's
-- refinement type added in the code
--  
-- Invariant: Internally, functions in the State ExprEnv need to have LH Dict arguments added,
-- (see addLHTCExprEnv) whereas functions in the measures should be created with the LH Dicts
-- already accounted for.


-- | LHState
-- Wraps a State, along with the other information needed to parse
-- LiquidHaskell ASTs
data LHState = LHState { state :: L.State [L.FuncCall]
                       , measures :: Measures
                       , tcvalues :: TCValues
} deriving (Eq, Show, Read)

consLHState :: L.State [L.FuncCall] -> Measures -> TCValues -> LHState
consLHState s meas tcv =
    LHState { state = s
            , measures = meas
            , tcvalues = tcv }

deconsLHState :: LHState -> L.State [L.FuncCall]
deconsLHState (LHState { state = s
                       , measures = meas }) =
    s { L.expr_env = E.union (L.expr_env s) meas }

measuresM :: LHStateM Measures
measuresM = do
    lh_s <- SM.get
    return $ measures lh_s

newtype LHStateM a = LHStateM { unSM :: (SM.State LHState a) } deriving (Applicative, Functor, Monad)

instance SM.MonadState LHState LHStateM where
    state f = LHStateM (SM.state f) 

instance ExState LHState LHStateM where
    exprEnv = return . expr_env =<< SM.get
    putExprEnv = rep_expr_envM

    typeEnv = return . type_env =<< SM.get
    putTypeEnv = rep_type_envM

    nameGen = return . name_gen =<< SM.get
    putNameGen = rep_name_genM

    knownValues = return . known_values =<< SM.get

instance FullState LHState LHStateM where
    typeClasses = return . type_classes =<< SM.get
    putTypeClasses = rep_type_classesM

runLHStateM :: LHStateM a -> LHState -> (a, LHState)
runLHStateM (LHStateM s) s' = SM.runState s s'

evalLHStateM :: LHStateM a -> LHState -> a
evalLHStateM s = fst . runLHStateM s

execLHStateM :: LHStateM a -> LHState -> LHState
execLHStateM s = snd . runLHStateM s

liftState :: (L.State [L.FuncCall] -> a) -> LHState -> a
liftState f = f . state

expr_env :: LHState -> L.ExprEnv
expr_env = liftState L.expr_env

rep_expr_envM :: L.ExprEnv -> LHStateM ()
rep_expr_envM eenv = do
    lh_s <- SM.get
    let s = state lh_s
    let s' = s {L.expr_env = eenv}
    SM.put $ lh_s {state = s'}

type_env :: LHState -> L.TypeEnv
type_env = liftState L.type_env

rep_type_envM :: L.TypeEnv -> LHStateM ()
rep_type_envM tenv = do
    lh_s <- SM.get
    let s = state lh_s
    let s' = s {L.type_env = tenv}
    SM.put $ lh_s {state = s'}

name_gen :: LHState -> L.NameGen
name_gen = liftState L.name_gen

rep_name_genM :: L.NameGen -> LHStateM ()
rep_name_genM ng = do
    lh_s <- SM.get
    let s = state lh_s
    let s' = s {L.name_gen = ng}
    SM.put $ lh_s {state = s'}

known_values :: LHState -> L.KnownValues
known_values = liftState L.known_values

type_classes :: LHState -> L.TypeClasses
type_classes = liftState L.type_classes

rep_type_classesM :: L.TypeClasses -> LHStateM ()
rep_type_classesM tc = do
    lh_s <- SM.get
    let s = state lh_s
    let s' = s {L.type_classes = tc}
    SM.put $ lh_s {state = s'}

liftLHState :: (LHState -> a) -> LHStateM a
liftLHState f = return . f =<< SM.get

lookupMeasure :: L.Name -> LHState -> Maybe L.Expr
lookupMeasure n = E.lookup n . measures

lookupMeasureM :: L.Name -> LHStateM (Maybe L.Expr)
lookupMeasureM n = liftLHState (lookupMeasure n)

insertMeasureM :: L.Name -> L.Expr -> LHStateM ()
insertMeasureM n e = do
    lh_s <- SM.get
    let meas = measures lh_s
    let meas' = E.insert n e meas
    SM.put $ lh_s {measures = meas'}

-- | andM
-- The version of 'and' in the measures
andM :: LHStateM L.Expr
andM = do
    m <- measuresM
    return (L.mkAnd m)

-- | orM
-- The version of 'or' in the measures
orM :: LHStateM L.Expr
orM = do
    m <- measuresM
    return (L.mkOr m)

-- | notM
-- The version of 'not' in the measures
notM :: LHStateM L.Expr
notM = do
    m <- measuresM
    return (L.mkNot m)

liftTCValues :: (TCValues -> a) -> LHStateM a
liftTCValues f = return . f . tcvalues =<< SM.get

lhTCM :: LHStateM L.Name
lhTCM = liftTCValues lhTC

lhOrdTCM :: LHStateM L.Name
lhOrdTCM = liftTCValues lhOrdTC 

lhEqM :: LHStateM L.Name
lhEqM = liftTCValues lhEq

lhNeM :: LHStateM L.Name
lhNeM = liftTCValues lhNe

lhLtM :: LHStateM L.Name
lhLtM = liftTCValues lhLt

lhLeM :: LHStateM L.Name
lhLeM = liftTCValues lhLe

lhGtM :: LHStateM L.Name
lhGtM = liftTCValues lhGt

lhGeM :: LHStateM L.Name
lhGeM = liftTCValues lhGe

lhPlusM :: LHStateM L.Name
lhPlusM = liftTCValues lhPlus

lhMinusM :: LHStateM L.Name
lhMinusM = liftTCValues lhMinus

lhTimesM :: LHStateM L.Name
lhTimesM = liftTCValues lhTimes

lhDivM :: LHStateM L.Name
lhDivM = liftTCValues lhDiv

lhNegateM :: LHStateM L.Name
lhNegateM = liftTCValues lhNegate

lhModM :: LHStateM L.Name
lhModM = liftTCValues lhMod

lhPPM :: LHStateM L.Name
lhPPM = liftTCValues lhPP
