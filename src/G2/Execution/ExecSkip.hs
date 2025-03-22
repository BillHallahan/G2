module G2.Execution.ExecSkip 
    (
        ExecOrSkip (..),
        isExecOrSkip,
        canAddToNRPC,
        checklistOfExprs
    ) where

import qualified Data.HashSet as HS
import qualified G2.Language.ExprEnv as E
import G2.Language
import G2.Execution.Rules

data ExecOrSkip = Exec
                | Skip
                deriving (Eq, Show)


isExecOrSkip :: ExecOrSkip -> ExecOrSkip -> ExecOrSkip
isExecOrSkip Skip Skip = Skip
isExecOrSkip Exec _ = Exec
isExecOrSkip _ Exec = Exec

canAddToNRPC :: ExprEnv -> Expr -> NameGen -> HS.HashSet Name -> HS.HashSet Name -> ExecOrSkip
canAddToNRPC eenv e ng names seen_vars
    -- If a variable is already seen, then it can be skipped. e.g recursive bindings
    | Var (Id n t)  <- e
    , True <- HS.member n seen_vars = Skip
    -- Rule-VAR-EXEC
    | Var (Id n t)  <- e
    , True <- HS.member n names = Exec 
    -- Rule-SYM-VAR for symbolic variables
    | Var (Id n t) <- e
    , E.isSymbolic n eenv = Skip
    -- Rule-VAR
    | Var (Id n t)  <- e
    , Just e' <- E.lookup n eenv = 
        let seen_vars' = HS.insert n seen_vars
        in canAddToNRPC eenv e' ng names seen_vars'
    -- Rule-SYM-VAR, that decides for any variable that's not in heap, be it let bindings or symbolic variable
    | Var (Id n t)  <- e = Skip
    -- Rule-DC
    | Data dcon  <- e = Skip
    -- Rule-LIT
    | Lit lit <- e = Skip
    -- Rule-Let
    | Let b e' <- e  = 
        let 
            (binds_lhs, binds_rhs) = unzip b

            olds = map idName binds_lhs
            (news, ng') = freshSeededNames olds ng

            e'' = renameExprs (zip olds news) e'
            binds_rhs' = renameExprs (zip olds news) binds_rhs

            eenv' = E.insertExprs (zip news binds_rhs') eenv

        in canAddToNRPC eenv' e'' ng' names seen_vars
    | Lam u i e1 <- e = 
        let
            old = idName i
            (x', ng') = freshSeededName old ng
            e1' = renameExpr old x' e1
        in
            canAddToNRPC eenv e1' ng names seen_vars
    -- Rule-LAM
    | App (Lam u i e1) e2 <- e = 
        let
            old = idName i
            (x', ng') = freshSeededName old ng
            e1' = renameExpr old x' e1
            eenv' = E.insert x' e2 eenv
        in 
            canAddToNRPC eenv' e1' ng names seen_vars
    -- Rule-PRIM
    | (Prim _ _):es <- unApp e = checklistOfExprs eenv es ng names seen_vars
    -- Rule-APP
    | App e1 e2 <- e = isExecOrSkip (canAddToNRPC eenv e1 ng names seen_vars) (canAddToNRPC eenv e2 ng names seen_vars)
    -- Rule for determining case statements
    | Case e' i t alts <- e = 
        let altsExpr = e' : map (\(Alt _ e) -> e) alts
        in checklistOfExprs eenv altsExpr ng names seen_vars
    
    | Type _ <- e = Skip
    | Cast e' _ <- e = canAddToNRPC eenv e' ng names seen_vars
    | Tick _ e' <- e = canAddToNRPC eenv e' ng names seen_vars
    | NonDet es <- e = checklistOfExprs eenv es ng names seen_vars
    | SymGen _ _ <- e = Skip
    | Assume _ e1 e2 <- e = isExecOrSkip (canAddToNRPC eenv e1 ng names seen_vars) (canAddToNRPC eenv e2 ng names seen_vars)
    | Assert _ e1 e2 <- e = isExecOrSkip (canAddToNRPC eenv e1 ng names seen_vars) (canAddToNRPC eenv e2 ng names seen_vars)
         
    | otherwise = Skip

checklistOfExprs :: ExprEnv -> [Expr] -> NameGen -> HS.HashSet Name -> HS.HashSet Name -> ExecOrSkip
checklistOfExprs eenv [] ng _ _ = Skip
checklistOfExprs eenv (e : es) ng names seen_vars = isExecOrSkip (canAddToNRPC eenv e ng names seen_vars) (checklistOfExprs eenv es ng names seen_vars)