{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Internals.Liquid.Types ( LHOutput (..)
                                 , Measures
                                 , LHState
                                 , LHStateM (..)
                                 , consLHState
                                 , deconsLHState
                                 , measures
                                 , tcvalues
                                 , lookupMeasure
                                 , lookupMeasureM
                                 , lhTCM
                                 , lhEqM
                                 , lhNeM
                                 , lhLtM
                                 , lhLeM
                                 , lhGtM
                                 , lhGeM
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

-- | LHState
-- Wraps a State, along with the other information needed to parse
-- LiquidHaskell ASTs
data LHState = LHState { state_ :: L.State [L.FuncCall]
                       , measures_ :: Measures
                       , tcvalues_ :: TCValues
} deriving (Eq, Show, Read)

consLHState :: L.State [L.FuncCall] -> Measures -> TCValues -> LHState
consLHState s meas tcv =
    LHState { state_ = s
            , measures_ = meas
            , tcvalues_ = tcv }

deconsLHState :: LHState -> L.State [L.FuncCall]
deconsLHState (LHState { state_ = s
                       , measures_ = meas }) =
    s { L.expr_env = E.union (L.expr_env s) meas }

state :: LHState -> L.State [L.FuncCall]
state = state_

measures :: LHState -> Measures
measures = measures_

tcvalues :: LHState -> TCValues
tcvalues = tcvalues_

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

liftState :: (L.State [L.FuncCall] -> a) -> LHState -> a
liftState f = f . state

expr_env :: LHState -> L.ExprEnv
expr_env = liftState L.expr_env

rep_expr_envM :: L.ExprEnv -> LHStateM ()
rep_expr_envM eenv = do
    lh_s <- SM.get
    let s = state lh_s
    let s' = s {L.expr_env = eenv}
    SM.put $ lh_s {state_ = s'}

type_env :: LHState -> L.TypeEnv
type_env = liftState L.type_env

rep_type_envM :: L.TypeEnv -> LHStateM ()
rep_type_envM tenv = do
    lh_s <- SM.get
    let s = state lh_s
    let s' = s {L.type_env = tenv}
    SM.put $ lh_s {state_ = s'}

name_gen :: LHState -> L.NameGen
name_gen = liftState L.name_gen

rep_name_genM :: L.NameGen -> LHStateM ()
rep_name_genM ng = do
    lh_s <- SM.get
    let s = state lh_s
    let s' = s {L.name_gen = ng}
    SM.put $ lh_s {state_ = s'}

known_values :: LHState -> L.KnownValues
known_values = liftState L.known_values

liftLHState :: (LHState -> a) -> LHStateM a
liftLHState f = return . f =<< SM.get

lookupMeasure :: L.Name -> LHState -> Maybe L.Expr
lookupMeasure n = E.lookup n . measures

lookupMeasureM :: L.Name -> LHStateM (Maybe L.Expr)
lookupMeasureM n = liftLHState (lookupMeasure n)

liftTCValues :: (TCValues -> a) -> LHStateM a
liftTCValues f = return . f . tcvalues =<< SM.get

lhTCM :: LHStateM L.Name
lhTCM = liftTCValues lhTC

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

lhPPM :: LHStateM L.Name
lhPPM = liftTCValues lhPP
