{-# LANGUAGE OverloadedStrings #-}

module G2.Execution.MutVar where

import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import G2.Language.Naming
import G2.Language.MutVarEnv
import G2.Language.Support
import G2.Language.Syntax

import qualified Data.List as DL

mutVarTy :: KnownValues
         -> Type -- ^ The State type
         -> Type -- ^ The stored type
         -> Type
mutVarTy kv ts ta = TyApp (TyApp (TyCon (KV.tyMutVar kv) (TyFun TYPE (TyFun TYPE TYPE))) ts) ta

newMutVar :: State t
          -> NameGen
          -> MVOrigin
          -> Type -- ^ The State type
          -> Type -- ^ The stored type
          -> Expr
          -> (State t, NameGen)
newMutVar s ng org ts t e =
    let
        (mv_n, ng') = freshSeededName (Name "mv" Nothing 0 Nothing) ng
        (i, ng'') = freshId t ng'        
        s' = s { curr_expr = CurrExpr Evaluate (Prim (MutVar mv_n) $ mutVarTy (known_values s) ts t)
               , expr_env = E.insert (idName i) e (expr_env s)
               , mutvar_env = insertMvVal mv_n i org (mutvar_env s)}
    in
    (s', ng'')

newMutVars :: State t 
        -> NameGen 
        -> [(MVOrigin, Type, Type, Expr)] 
        -> (State t, NameGen)
newMutVars state ng items = DL.foldl' go (state, ng) items
  where
    go (s, ng') (origin, stateType, storedType, expr) =
      newMutVar s ng' origin stateType storedType expr
