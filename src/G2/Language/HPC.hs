{-# LANGUAGE FlexibleContexts #-}

module G2.Language.HPC ( HPCMemoTable
                       , reachesHPC
                       , reachesHPC' ) where

import G2.Language.AST
import qualified G2.Language.ExprEnv as E
import G2.Language.Syntax

import qualified Control.Monad.State.Lazy as SM
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T

type HPCMemoTable = HM.HashMap Name (HS.HashSet (Int, T.Text))

reachesHPC :: ASTContainer c Expr => HS.HashSet (Maybe T.Text) -> E.ExprEnv -> c -> (HS.HashSet (Int, T.Text))
reachesHPC mod_name eenv c = SM.evalState (reachesHPC' mod_name eenv c) HM.empty

reachesHPC' :: (SM.MonadState HPCMemoTable m, ASTContainer c Expr) => HS.HashSet (Maybe T.Text) -> E.ExprEnv -> c -> m (HS.HashSet (Int, T.Text))
reachesHPC' mod_name eenv es = mconcat <$> mapM (reaches mod_name eenv) (containedASTs es) 

reaches :: SM.MonadState HPCMemoTable m => HS.HashSet (Maybe T.Text) -> E.ExprEnv -> Expr -> m (HS.HashSet (Int, T.Text))
reaches mod_name eenv (Var (Id n _)) = do
    seen <- SM.get
    case HM.lookup n seen of
        Just hpcs -> return hpcs
        Nothing -> do
            SM.modify (HM.insert n HS.empty)
            hpcs <- maybe (return HS.empty) (reaches mod_name eenv) (E.lookup n eenv)
            SM.modify (HM.insert n hpcs)
            return hpcs
reaches mod_name eenv (Tick (HpcTick i t) e) | Just t `HS.member` mod_name = HS.insert (i, t) <$> reaches mod_name eenv e
reaches mod_name eenv e = mconcat <$> mapM (reaches mod_name eenv) (children e)
