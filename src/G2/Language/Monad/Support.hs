{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Language.Monad.Support ( StateM
                                 , ExState (..)
                                 , FullState (..)
                                 , runStateM
                                 , readRecord
                                 , withNG
                                 , mapCurrExpr ) where

import qualified Control.Monad.State.Lazy as SM

import G2.Language.Naming
import G2.Language.Syntax
import G2.Language.Support
import G2.Language.TypeClasses

-- | A wrapper for `State`, allowing it to be used as a monadic context.
newtype StateM t a = StateM (SM.State (State t) a) deriving (Applicative, Functor, Monad)

instance SM.MonadState (State t) (StateM t) where
    state f = StateM (SM.state f)

-- We split the State Monad into two pieces, so we can use it in the
-- initialization stage of G2.  In this stage, we do not have an entire State.
-- See G2.Initialization.Types

-- | Allows access to certain basic components of a state.
class SM.MonadState s m => ExState s m | m -> s where
    exprEnv :: m ExprEnv
    putExprEnv :: ExprEnv -> m ()

    typeEnv :: m TypeEnv
    putTypeEnv :: TypeEnv -> m ()

    nameGen :: m NameGen
    putNameGen :: NameGen -> m ()

    knownValues :: m KnownValues
    putKnownValues :: KnownValues -> m ()

    typeClasses :: m TypeClasses
    putTypeClasses :: TypeClasses -> m ()

-- Extends `ExState`, allowing access to a more complete set of the
-- components in the `State`.
class ExState s m => FullState s m | m -> s where
    currExpr :: m CurrExpr
    putCurrExpr :: CurrExpr -> m ()

    inputIds :: m InputIds
    fixedInputs :: m [Expr]

instance ExState (State t) (StateM t) where
    exprEnv = readRecord expr_env
    putExprEnv = rep_expr_envM

    typeEnv = readRecord type_env
    putTypeEnv = rep_type_envM

    nameGen = readRecord name_gen
    putNameGen = rep_name_genM

    knownValues = readRecord known_values
    putKnownValues = rep_known_valuesM

    typeClasses = readRecord type_classes
    putTypeClasses = rep_type_classesM

instance FullState (State t) (StateM t) where
    currExpr = readRecord curr_expr
    putCurrExpr = rep_curr_exprM

    inputIds = readRecord input_ids
    fixedInputs = readRecord fixed_inputs

runStateM :: StateM t a -> State t -> (a, State t)
runStateM (StateM s) s' = SM.runState s s'

readRecord :: SM.MonadState s m => (s -> r) -> m r
readRecord f = return . f =<< SM.get

rep_expr_envM :: ExprEnv -> StateM t ()
rep_expr_envM eenv = do
    s <- SM.get
    SM.put $ s {expr_env = eenv}

rep_type_envM :: TypeEnv -> StateM t ()
rep_type_envM tenv = do
    s <- SM.get
    SM.put $ s {type_env = tenv}

withNG :: ExState s m => (NameGen -> (a, NameGen)) -> m a
withNG f = do
    ng <- nameGen
    let (a, ng') = f ng
    putNameGen ng'
    return a

rep_name_genM :: NameGen -> StateM t ()
rep_name_genM ng = do
    s <- SM.get
    SM.put $ s {name_gen = ng}

rep_known_valuesM :: KnownValues -> StateM t ()
rep_known_valuesM kv = do
    s <- SM.get
    SM.put $ s {known_values = kv}

rep_type_classesM :: TypeClasses -> StateM t ()
rep_type_classesM tc = do
    s <- SM.get
    SM.put $ s {type_classes = tc}

rep_curr_exprM :: CurrExpr -> StateM t ()
rep_curr_exprM ce = do
    s <- SM.get
    SM.put $ s {curr_expr = ce}

mapCurrExpr :: FullState s m => (Expr -> m Expr) -> m ()
mapCurrExpr f = do
    (CurrExpr er e) <- currExpr
    e' <- f e
    putCurrExpr (CurrExpr er e') 
