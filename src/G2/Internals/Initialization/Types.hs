{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Internals.Initialization.Types (SimpleState (..)) where

import qualified Control.Monad.State.Lazy as SM

import qualified G2.Internals.Language as L
import G2.Internals.Language.AST
import G2.Internals.Language.Monad
import G2.Internals.Language.Syntax

data SimpleState = SimpleState { expr_env :: L.ExprEnv
                               , type_env :: L.TypeEnv
                               , name_gen :: L.NameGen
                               , known_values :: L.KnownValues } deriving (Eq, Show, Read)

newtype SimpleStateM a = SimpleStateM { unSM :: (SM.State SimpleState a) } deriving (Applicative, Functor, Monad)

instance SM.MonadState SimpleState SimpleStateM where
    state f = SimpleStateM (SM.state f)

instance ExState SimpleState SimpleStateM where
    exprEnv = return . expr_env =<< SM.get
    putExprEnv = rep_expr_envM

    typeEnv = return . type_env =<< SM.get

    nameGen = return . name_gen =<< SM.get
    putNameGen = rep_name_genM

    knownValues = return . known_values =<< SM.get

rep_expr_envM :: L.ExprEnv -> SimpleStateM ()
rep_expr_envM eenv = do
    s <- SM.get
    SM.put $ s {expr_env = eenv}

rep_name_genM :: L.NameGen -> SimpleStateM ()
rep_name_genM ng = do
    s <- SM.get
    SM.put $ s {name_gen = ng}

instance ASTContainer SimpleState Expr where
    containedASTs s =  containedASTs (expr_env s)
    modifyContainedASTs f s = s { expr_env = modifyContainedASTs f (expr_env s) }

instance ASTContainer SimpleState Type where
    containedASTs s =  containedASTs (expr_env s) ++ containedASTs (type_env s)
    modifyContainedASTs f s = s { expr_env = modifyContainedASTs f (expr_env s)
                                , type_env = modifyContainedASTs f (type_env s) }