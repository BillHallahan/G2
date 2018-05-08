module G2.Internals.Language.Monad.Support ( StateM
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

type StateM t s = SM.State (State t) s

readRecord :: (State t -> r) -> StateM t r
readRecord f = return . f =<< SM.get

expr_envM :: StateM t ExprEnv
expr_envM = readRecord expr_env

rep_expr_envM :: ExprEnv -> StateM t ()
rep_expr_envM eenv = do
    s <- SM.get
    SM.put $ s {expr_env = eenv}

type_envM :: StateM t TypeEnv
type_envM = readRecord type_env

withNG :: (NameGen -> (a, NameGen)) -> StateM t a
withNG f = do
    ng <- name_genM
    let (a, ng') = f ng
    rep_name_genM ng'
    return a

name_genM :: StateM t NameGen
name_genM = readRecord name_gen

rep_name_genM :: NameGen -> StateM t ()
rep_name_genM ng = do
    s <- SM.get
    SM.put $ s {name_gen = ng}

known_valuesM :: StateM t KnownValues
known_valuesM = readRecord known_values
