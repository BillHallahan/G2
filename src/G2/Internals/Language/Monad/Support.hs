{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Internals.Language.Monad.Support ( StateM
                                           , ExState (..)
                                           , runStateM
                                           , readRecord
                                           , expr_envM
                                           , rep_expr_envM
                                           , type_envM
                                           , withNG
                                           , known_valuesM ) where

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

    nameGen :: m NameGen
    putNameGen :: NameGen -> m ()

    knownValues :: m KnownValues


instance ExState (State t) (StateM t) where
    exprEnv = expr_envM
    putExprEnv = rep_expr_envM

    typeEnv = type_envM

    nameGen = name_genM
    putNameGen = rep_name_genM

    knownValues = known_valuesM

runStateM :: StateM t a -> State t -> (a, State t)
runStateM (StateM s) s' = SM.runState s s'

readRecord :: SM.MonadState s m => (s -> r) -> m r
readRecord f = return . f =<< SM.get

expr_envM :: StateM t ExprEnv
expr_envM = readRecord expr_env

rep_expr_envM :: ExprEnv -> StateM t ()
rep_expr_envM eenv = do
    s <- SM.get
    SM.put $ s {expr_env = eenv}

type_envM :: StateM t TypeEnv
type_envM = readRecord type_env

withNG :: ExState s m => (NameGen -> (a, NameGen)) -> m a
withNG f = do
    ng <- nameGen
    let (a, ng') = f ng
    putNameGen ng'
    return a

name_genM :: StateM t NameGen
name_genM = readRecord name_gen

rep_name_genM :: NameGen -> StateM t ()
rep_name_genM ng = do
    s <- SM.get
    SM.put $ s {name_gen = ng}

known_valuesM :: StateM t KnownValues
known_valuesM = readRecord known_values
