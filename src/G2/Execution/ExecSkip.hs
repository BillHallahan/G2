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


isExecOrSkip :: SM.MonadState NRPCMemoTable m => NameGen -> (NameGen -> m (ExecOrSkip, NameGen)) -> (NameGen -> m (ExecOrSkip, NameGen)) -> m (ExecOrSkip, NameGen)
isExecOrSkip ng f1 f2 =
    do
        (res1, ng') <- f1 ng
        case res1 of
            Exec -> return (Exec, ng')
            Skip -> f2 ng'


data IsSWHNF = IsSWHNF | NotIsSWHNF deriving (Show)
type NRPCMemoTable = HM.HashMap Name (ExecOrSkip, IsSWHNF)

checkDelayability :: ExprEnv -> Expr -> NameGen -> HS.HashSet Name -> NRPCMemoTable -> (ExecOrSkip, NRPCMemoTable)
checkDelayability eenv e ng exec_names table = 
    let 
        ((res, _), var_table) = SM.runState (checkDelayability' eenv e exec_names ng) table 
    in (res, var_table)

checkDelayability' :: SM.MonadState NRPCMemoTable m => ExprEnv -> Expr -> HS.HashSet Name -> NameGen -> m (ExecOrSkip, NameGen)
checkDelayability' eenv e exec_names ng
    -- Rule-VAR-EXEC
    | Var (Id n _) <- e
    , True <- HS.member n exec_names = return (Exec, ng)
    | Var (Id n _) <- e =
        do
            currMemoTable <- SM.get
            case HM.lookup n currMemoTable of
                Just value | Just ex_sk <- isSkippable n value ng eenv -> return ex_sk
                -- Rule-VAR
                _ | Just e' <- E.lookup n eenv -> do
                    -- If we have recursive let bindings then we keep variable as skip to avoid infinite loop
                    -- and check delayability of the mapped expression. Now, we can update variable's exact delayability.
                    SM.modify (HM.insert n (Skip, NotIsSWHNF))
                    (res, ng') <- checkDelayability' eenv e' exec_names ng
                    SM.modify (HM.insert n (res, getSWHNFStatus eenv e'))
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

        in checkDelayability' eenv' e'' exec_names ng'
    -- Rule-LAM
    | Lam _ i e1 <- e = 
        let
            old = idName i
            (x', ng') = freshSeededName old ng
            e1' = renameExpr old x' e1
        in
            checkDelayability' eenv e1' exec_names ng'
    -- Rule-APP-LAM
    | App (Lam _ i e1) e2 <- e = 
        let
            old = idName i
            (x', ng') = freshSeededName old ng
            e1' = renameExpr old x' e1
            eenv' = E.insert x' e2 eenv
        in 
            checkDelayability' eenv' e1' exec_names ng'
    -- Rule-APP
    | App e1 e2 <- e = isExecOrSkip ng (checkDelayability' eenv e1 exec_names) (checkDelayability' eenv e2 exec_names)
    -- Rule-PRIM
    | (Prim _ _):es <- unApp e = checklistOfExprs eenv es exec_names ng
    -- Rule for determining case statements 
    | Case e' _ _ alts <- e = 
        let altsExpr = e' : map (\(Alt _ e) -> e) alts
        in checklistOfExprs eenv altsExpr exec_names ng

    | Type _ <- e = return (Skip, ng)
    | Cast e' _ <- e = checkDelayability' eenv e' exec_names ng
    | Tick _ e' <- e = checkDelayability' eenv e' exec_names ng
    | NonDet es <- e = checklistOfExprs eenv es exec_names ng
    | SymGen _ _ <- e = return (Skip, ng)
    | Assume _ e1 e2 <- e = isExecOrSkip ng (checkDelayability' eenv e1 exec_names) (checkDelayability' eenv e2 exec_names)
    | Assert _ e1 e2 <- e = isExecOrSkip ng (checkDelayability' eenv e1 exec_names) (checkDelayability' eenv e2 exec_names)
    | otherwise = return (Skip, ng)

    where
        isSkippable :: Name -> (ExecOrSkip, IsSWHNF) -> NameGen -> ExprEnv -> Maybe (ExecOrSkip, NameGen)
        isSkippable _ (Skip, _) ng' _ = Just (Skip, ng')
        isSkippable _ (Exec, IsSWHNF) ng' _ = Just (Exec, ng')
        isSkippable var_name (Exec, NotIsSWHNF) _ eenv'
            | Just expr' <- E.lookup var_name eenv'
            , normalForm eenv expr' = Nothing
        isSkippable _ _ ng' _ =  Just (Exec, ng')

        getSWHNFStatus eenv' e' = if normalForm eenv' e' then IsSWHNF else NotIsSWHNF


checklistOfExprs :: SM.MonadState NRPCMemoTable m => ExprEnv -> [Expr] -> HS.HashSet Name -> NameGen -> m (ExecOrSkip, NameGen)
checklistOfExprs _ [] _ ng = return (Skip, ng)
checklistOfExprs eenv (e : es) exec_names ng = 
        isExecOrSkip ng (checkDelayability' eenv e exec_names) (checklistOfExprs eenv es exec_names)