{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Internals.Language.Monad.Support ( StateM
                                           , ExState (..)
                                           , FullState (..)
                                           , runStateM
                                           , readRecord
                                           , withNG ) where

import qualified Control.Monad.State.Lazy as SM

import G2.Internals.Language.Naming
import G2.Internals.Language.Support
import G2.Internals.Language.TypeClasses

newtype StateM t a = StateM (SM.State (State t) a) deriving (Applicative, Functor, Monad)

instance SM.MonadState (State t) (StateM t) where
    state f = StateM (SM.state f)

class SM.MonadState s m => ExState s m | m -> s where
    exprEnv :: m ExprEnv
    putExprEnv :: ExprEnv -> m ()

    typeEnv :: m TypeEnv
    putTypeEnv :: TypeEnv -> m ()

    nameGen :: m NameGen
    putNameGen :: NameGen -> m ()

    knownValues :: m KnownValues

class ExState s m => FullState s m | m -> s where
    currExpr :: m CurrExpr
    putCurrExpr :: CurrExpr -> m ()

    typeClasses :: m TypeClasses
    putTypeClasses :: TypeClasses -> m ()

    inputIds :: m InputIds

instance ExState (State t) (StateM t) where
    exprEnv = readRecord expr_env
    putExprEnv = rep_expr_envM

    typeEnv = readRecord type_env
    putTypeEnv = rep_type_envM

    nameGen = readRecord name_gen
    putNameGen = rep_name_genM

    knownValues = readRecord known_values

instance FullState (State t) (StateM t) where
    currExpr = readRecord curr_expr
    putCurrExpr = rep_curr_exprM

    typeClasses = readRecord type_classes
    putTypeClasses = rep_type_classesM

    inputIds = readRecord input_ids

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

rep_type_classesM :: TypeClasses -> StateM t ()
rep_type_classesM tc = do
    s <- SM.get
    SM.put $ s {type_classes = tc}

rep_curr_exprM :: CurrExpr -> StateM t ()
rep_curr_exprM ce = do
    s <- SM.get
    SM.put $ s {curr_expr = ce}