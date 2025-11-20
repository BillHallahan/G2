{-# LANGUAGE FlexibleContexts, PatternSynonyms #-}

module G2.Execution.Internals.ExecSkip 
    (
        ExecOrSkip (..),
        pattern Exec,
        NRPCMemoTable,
        isExecOrSkip,
        checkDelayability,
        checklistOfExprs,

        ReachesSymMemoTable,
        ReachesSym (..),
        reachesSymbolicMemo
    ) where

import qualified Control.Monad.State as SM
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import qualified G2.Language.ExprEnv as E
import G2.Language
import G2.Language.ReachesSym
import G2.Execution.NormalForms ( normalForm )

data ExecOrSkip = ExecI -- ^ The expression must be executed
                    Name -- ^ Name of a "checkpoint function", see Note [Memoization and SWHNF] in G2.Language.ReachesSym
                | Skip -- ^ The expression may be skipped
                deriving (Eq, Show)

pattern Exec :: ExecOrSkip
pattern Exec <- ExecI _

{-# COMPLETE Exec, Skip #-}

isExecOrSkip :: SM.MonadState NRPCMemoTable m => NameGen -> (NameGen -> m (ExecOrSkip, NameGen)) -> (NameGen -> m (ExecOrSkip, NameGen)) -> m (ExecOrSkip, NameGen)
isExecOrSkip ng f1 f2 =
    do
        (res1, ng') <- f1 ng
        case res1 of
            Exec -> return (res1, ng')
            Skip -> f2 ng'


type NRPCMemoTable = HM.HashMap Name ExecOrSkip

checkDelayability :: ExprEnv -> Expr -> NameGen -> HS.HashSet Name -> NRPCMemoTable -> (ExecOrSkip, NRPCMemoTable)
checkDelayability eenv e ng exec_names table = 
    let 
        ((res, _), var_table) = SM.runState (checkDelayability' eenv e exec_names ng) table 
    in (res, var_table)

checkDelayability' :: SM.MonadState NRPCMemoTable m => ExprEnv -> Expr -> HS.HashSet Name -> NameGen -> m (ExecOrSkip, NameGen)
checkDelayability' eenv (Var (Id n _)) exec_names ng
    -- Rule-VAR-EXEC
    | True <- HS.member n exec_names = return (ExecI n, ng)
    | otherwise =
        do
            memo <- SM.get
            case HM.lookup n memo of
                Just Skip -> return (Skip, ng)
                Just (ExecI n') | checkNotNormalForm memo n -> return (ExecI n', ng)
                -- Rule-VAR
                _ | Just (E.Conc e') <- e -> do
                    -- If we have recursive let bindings then we keep variable as skip to avoid infinite loop
                    -- and check delayability of the mapped expression. Now, we can update variable's exact delayability.
                    SM.modify (HM.insert n Skip)
                    (res, ng') <- checkDelayability' eenv e' exec_names ng

                    SM.modify (HM.insert n res)
                    -- See Note [Memoization and SWHNF] in G2.Language.ReachesSym.  For memoization of an Exec result for a function f, we want a
                    -- checkpoint function g that is (a) reachable from f only through SWHNF definitions and (b) returns
                    -- the result Exec.  We thus ensure that we are returning Exec's that fit these two conditions
                    let res' = case res of
                                Skip -> res
                                Exec -> if normalForm eenv e' then res else ExecI n
                    return (res', ng')
                -- Rule-SYM-VAR, that says symbolic variables are skippable, or for any variable that's not in heap, such as a let bound variable
                  | otherwise -> return (Skip, ng)
    where
        e = E.lookupConcOrSym n eenv
        
        checkNotNormalForm memo n' | HS.member n' exec_names = True
                                   | Just e' <- E.lookup n' eenv
                                   , not (normalForm eenv e')
                                   , Just (ExecI n'') <- HM.lookup n' memo = checkNotNormalForm memo n''
                                   | otherwise = False
checkDelayability' eenv e exec_names ng
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
        let altsExpr = e' : map (\(Alt _ ae) -> ae) alts
        in checklistOfExprs eenv altsExpr exec_names ng

    | Type _ <- e = return (Skip, ng)
    | Cast e' _ <- e = checkDelayability' eenv e' exec_names ng
    | Tick _ e' <- e = checkDelayability' eenv e' exec_names ng
    | NonDet es <- e = checklistOfExprs eenv es exec_names ng
    | SymGen _ _ <- e = return (Skip, ng)
    | Assume _ e1 e2 <- e = isExecOrSkip ng (checkDelayability' eenv e1 exec_names) (checkDelayability' eenv e2 exec_names)
    | Assert _ e1 e2 <- e = isExecOrSkip ng (checkDelayability' eenv e1 exec_names) (checkDelayability' eenv e2 exec_names)
    | otherwise = return (Skip, ng)

checklistOfExprs :: SM.MonadState NRPCMemoTable m => ExprEnv -> [Expr] -> HS.HashSet Name -> NameGen -> m (ExecOrSkip, NameGen)
checklistOfExprs _ [] _ ng = return (Skip, ng)
checklistOfExprs eenv (e : es) exec_names ng = 
        isExecOrSkip ng (checkDelayability' eenv e exec_names) (checklistOfExprs eenv es exec_names)