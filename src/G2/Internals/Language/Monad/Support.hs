{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Internals.Language.Monad.Support ( StateM
                                           , ExState (..)
                                           , runStateM
                                           , readRecord
                                           , withNG ) where

import qualified Control.Monad.State.Lazy as SM
import Data.Functor.Identity

import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support

newtype StateM t a = StateM { unSM :: (SM.State (State t) a) } deriving (Applicative, Functor, Monad)

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

instance ExState (State t) (StateM t) where
    exprEnv = readRecord expr_env
    putExprEnv = rep_expr_envM

    typeEnv = readRecord type_env
    putTypeEnv = rep_type_envM

    nameGen = readRecord name_gen
    putNameGen = rep_name_genM

    knownValues = readRecord known_values

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