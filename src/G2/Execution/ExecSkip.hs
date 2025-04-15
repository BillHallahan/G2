{-# LANGUAGE FlexibleContexts #-}

module G2.Execution.ExecSkip 
    (
        ExecOrSkip (..),
        NRPCMemoTable,
        isExecOrSkip,
        checkDelayability,
        checklistOfExprs
    ) where

import qualified Control.Monad.State as SM
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import qualified G2.Language.ExprEnv as E
import G2.Language
import G2.Execution.NormalForms ( normalForm )


data ExecOrSkip = Exec
                | Skip
                deriving (Eq, Show)


isExecOrSkip :: ExecOrSkip -> ExecOrSkip -> ExecOrSkip
isExecOrSkip Skip Skip = Skip
isExecOrSkip Exec _ = Exec
isExecOrSkip _ Exec = Exec

data IsSWHNF = IsSWHNF | NotIsSWHNF deriving (Show)
type NRPCMemoTable = HM.HashMap Name (ExecOrSkip, IsSWHNF)

checkDelayability :: ExprEnv -> Expr -> NameGen -> HS.HashSet Name -> NRPCMemoTable -> (ExecOrSkip, NRPCMemoTable)
checkDelayability eenv e ng exec_names table = 
    let 
        ((res, _), var_table) = SM.runState (checkDelayability' eenv e ng exec_names ) table 
    in (res, var_table)

checkDelayability' :: SM.MonadState NRPCMemoTable m => ExprEnv -> Expr -> NameGen -> HS.HashSet Name -> m (ExecOrSkip, NameGen)
checkDelayability' eenv e ng exec_names
    | Var (Id n _) <- e =
        do
            currMemoTable <- SM.get
            case HM.lookup n currMemoTable of
                Just value -> isSkippable e value ng eenv
                -- Rule-VAR-EXEC
                Nothing | True <- HS.member n exec_names -> return (Exec, ng)
                -- Rule-VAR
                Nothing | Just e' <- E.lookup n eenv -> do 
                    let var_table_update = HM.insert n (Skip, NotIsSWHNF) currMemoTable
                    SM.put var_table_update
                    (res, ng') <- checkDelayability' eenv e' ng exec_names
                    let var_table_update' = HM.insert n (res, getSWHNFStatus eenv e') currMemoTable
                    SM.put var_table_update'
                    return (res, ng')
                -- Rule-SYM-VAR, that decides for any variable that's not in heap, be it let bindings or symbolic variable
                Nothing -> return (Skip, ng)
    -- Rule-DC
    | Data _  <- e = return (Skip, ng)
    -- Rule-LIT
    | Lit _ <- e = return (Skip, ng)
    -- Rule-Let
    | Let b e' <- e  = 
        let 
            (binds_lhs, binds_rhs) = unzip b

            olds = map idName binds_lhs
            (news, ng') = freshSeededNames olds ng

            e'' = renameExprs (zip olds news) e'
            binds_rhs' = renameExprs (zip olds news) binds_rhs

            eenv' = E.insertExprs (zip news binds_rhs') eenv

        in checkDelayability' eenv' e'' ng' exec_names
    -- Rule-LAM
    | Lam _ i e1 <- e = 
        let
            old = idName i
            (x', ng') = freshSeededName old ng
            e1' = renameExpr old x' e1
        in
            checkDelayability' eenv e1' ng' exec_names
    -- Rule-APP-LAM
    | App (Lam _ i e1) e2 <- e = 
        let
            old = idName i
            (x', ng') = freshSeededName old ng
            e1' = renameExpr old x' e1
            eenv' = E.insert x' e2 eenv
        in 
            checkDelayability' eenv' e1' ng' exec_names
    -- Rule-APP
    | App e1 e2 <- e = 
        do -- Question: Come back here and decide if we need to return name gen too?
            (del_e1, ng') <- checkDelayability' eenv e1 ng exec_names
            (del_e2, ng'') <- checkDelayability' eenv e2 ng' exec_names
            return (isExecOrSkip del_e1 del_e2, ng'')
    -- Rule-PRIM
    | (Prim _ _):es <- unApp e = checklistOfExprs eenv es ng exec_names
    -- Rule for determining case statements
    | Case e' _ _ alts <- e = 
        let altsExpr = e' : map (\(Alt _ e) -> e) alts
        in checklistOfExprs eenv altsExpr ng exec_names

    | Type _ <- e = return (Skip, ng)
    | Cast e' _ <- e = checkDelayability' eenv e' ng exec_names
    | Tick _ e' <- e = checkDelayability' eenv e' ng exec_names
    | NonDet es <- e = checklistOfExprs eenv es ng exec_names
    | SymGen _ _ <- e = return (Skip, ng)
    | Assume _ e1 e2 <- e = 
        do
            (del_e1, ng') <- checkDelayability' eenv e1 ng exec_names
            (del_e2, ng'') <- checkDelayability' eenv e2 ng' exec_names
            return (isExecOrSkip del_e1 del_e2, ng'')
    | Assert _ e1 e2 <- e = 
        do
            (del_e1, ng') <- checkDelayability' eenv e1 ng exec_names
            (del_e2, ng'') <- checkDelayability' eenv e2 ng' exec_names
            return (isExecOrSkip del_e1 del_e2, ng'')
    | otherwise = return (Skip, ng)

    where
        isSkippable _ (Skip, _) ng' _ = return (Skip, ng')
        isSkippable _ (Exec, IsSWHNF) ng' _ = return (Exec, ng')
        isSkippable (Var (Id n _)) (Exec, NotIsSWHNF) ng' eenv'
            | Just expr' <- E.lookup n eenv'
            , normalForm eenv expr' =
                do
                    (res, ng'') <- checkDelayability' eenv' expr' ng' exec_names
                    curr_var_table <- SM.get
                    let var_table_update = HM.insert n (res, IsSWHNF) curr_var_table
                    SM.put var_table_update
                    return (res, ng'')
        isSkippable _ (Exec, NotIsSWHNF) ng' _ = return (Exec, ng')

        getSWHNFStatus eenv' e' = if normalForm eenv' e' then IsSWHNF else NotIsSWHNF


checklistOfExprs :: SM.MonadState NRPCMemoTable m => ExprEnv -> [Expr] -> NameGen -> HS.HashSet Name -> m (ExecOrSkip, NameGen)
checklistOfExprs _ [] ng _ = return (Skip, ng)
checklistOfExprs eenv (e : es) ng exec_names = 
    do
        (del_e, ng') <- checkDelayability' eenv e ng exec_names
        (del_es, ng'') <- checklistOfExprs eenv es ng' exec_names
        return (isExecOrSkip del_e del_es, ng'')