{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Initialization.Types ( SimpleState (..)
                               , SimpleStateM (..)
                               , runSimpleStateM
                               , evalSimpleStateM
                               , execSimpleStateM
                               , putKnownValues ) where

import qualified Control.Monad.State.Lazy as SM

import qualified G2.Language as L
import G2.Language.AST
import G2.Language.Monad
import G2.Language.Syntax

data SimpleState = SimpleState { expr_env :: L.ExprEnv
                               , type_env :: L.TypeEnv
                               , name_gen :: L.NameGen
                               , known_values :: L.KnownValues
                               , type_classes :: L.TypeClasses
                               , rewrite_rules :: ![L.RewriteRule]
                               , exports :: [Name] } deriving (Eq, Show, Read)

newtype SimpleStateM a = SimpleStateM { unSM :: (SM.State SimpleState a) } deriving (Applicative, Functor, Monad)

instance SM.MonadState SimpleState SimpleStateM where
    state f = SimpleStateM (SM.state f)

instance NamingM SimpleState SimpleStateM where
    nameGen = return . name_gen =<< SM.get
    putNameGen = rep_name_genM

instance ExprEnvM SimpleState SimpleStateM where
    exprEnv = return . expr_env =<< SM.get
    putExprEnv = rep_expr_envM

instance ExState SimpleState SimpleStateM where
    typeEnv = return . type_env =<< SM.get
    putTypeEnv = rep_type_envM

    knownValues = return . known_values =<< SM.get
    putKnownValues = rep_known_valuesM

    typeClasses = return . type_classes =<< SM.get
    putTypeClasses = rep_type_classesM

runSimpleStateM :: SimpleStateM a -> SimpleState -> (a, SimpleState)
runSimpleStateM (SimpleStateM s) s' = SM.runState s s'

evalSimpleStateM :: SimpleStateM a -> SimpleState -> a
evalSimpleStateM s = fst . runSimpleStateM s

execSimpleStateM :: SimpleStateM a -> SimpleState -> SimpleState
execSimpleStateM s = snd . runSimpleStateM s

rep_expr_envM :: L.ExprEnv -> SimpleStateM ()
rep_expr_envM eenv = do
    s <- SM.get
    SM.put $ s {expr_env = eenv}

rep_type_envM :: L.TypeEnv -> SimpleStateM ()
rep_type_envM tenv = do
    s <- SM.get
    SM.put $ s {type_env = tenv}

rep_name_genM :: L.NameGen -> SimpleStateM ()
rep_name_genM ng = do
    s <- SM.get
    SM.put $ s {name_gen = ng}

rep_known_valuesM :: L.KnownValues -> SimpleStateM ()
rep_known_valuesM kv = do
    s <- SM.get
    SM.put $ s {known_values = kv}

rep_type_classesM :: L.TypeClasses -> SimpleStateM ()
rep_type_classesM tc = do
    s <- SM.get
    SM.put $ s {type_classes = tc}

instance ASTContainer SimpleState Expr where
    containedASTs s =  containedASTs (expr_env s)
    modifyContainedASTs f s = s { expr_env = modifyContainedASTs f (expr_env s) }

instance ASTContainer SimpleState Type where
    containedASTs s =  containedASTs (expr_env s) ++ containedASTs (type_env s)
    modifyContainedASTs f s = s { expr_env = modifyContainedASTs f (expr_env s)
                                , type_env = modifyContainedASTs f (type_env s) }
