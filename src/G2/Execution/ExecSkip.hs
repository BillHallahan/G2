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
import Debug.Trace

data ExecOrSkip = Exec
                | Skip
                deriving (Eq, Show)


isExecOrSkip :: ExecOrSkip -> ExecOrSkip -> ExecOrSkip
isExecOrSkip Skip Skip = Skip
isExecOrSkip Exec _ = Exec
isExecOrSkip _ Exec = Exec

canAddToNRPC :: ExprEnv -> Expr -> NameGen -> HS.HashSet Name -> ExecOrSkip
canAddToNRPC eenv e ng names
    | Var (Id n t)  <- e
    , True <- HS.member n names = trace("I am in first Var")Exec
    -- Come back here if a datacon has variables Rule-DC
    | Data dcon  <- e = trace("I am in  DataCon") Skip
    -- Rule-LIT
    | Lit lit <- e = trace("I am in Lit Var") Skip
    -- SYM-VAR for symbolic variables
    | Var (Id n t) <- e
    , E.isSymbolic n eenv = Skip
    -- Rule-VAR
    | Var (Id n t)  <- e
    , Just e' <- E.lookup n eenv = trace("I am in second Var: " ++ show e') canAddToNRPC eenv e' ng names
    -- Rule-SYM-VAR, that decides for any variable that's not in heap, be it let bindings or symbolic variable
    | Var (Id n t)  <- e = trace("I am in third Var") Skip
    -- Rule-Let
    | Let b e' <- e  = 
        let 
            (binds_lhs, binds_rhs) = trace("I am in Let") unzip b

            olds = map idName binds_lhs
            (news, ng') = freshSeededNames olds ng

            e'' = renameExprs (zip olds news) e
            binds_rhs' = renameExprs (zip olds news) binds_rhs

            eenv' = E.insertExprs (zip news binds_rhs') eenv

        in canAddToNRPC eenv' e'' ng' names
    | Lam u i e1 <- e = 
        let
            old = idName i
            (x', ng') = freshSeededName old ng
            e1' = renameExpr old x' e1
        in
            canAddToNRPC eenv e1' ng names
    -- Rule-LAM
    | App (Lam u i e1) e2 <- e = 
        let
            old = trace("  I am in App now. ") idName i
            (x', ng') = freshSeededName old ng
            e1' = renameExpr old x' e1
            eenv' = E.insert x' e2 eenv
        in 
            trace("e1 is: " ++ show e1) canAddToNRPC eenv' e1' ng names
    -- Rule-PRIM
    | (Prim _ _):es <- unApp e = trace("I am in Prim") checklistOfExprs eenv es ng names
    -- Rule-APP
    | App e1 e2 <- e = trace("I am in second App") isExecOrSkip (canAddToNRPC eenv e1 ng names) (canAddToNRPC eenv e2 ng names)
    -- Rule for determining case statements
    | Case e' i t alts <- e = 
        let altsExpr = trace("I am in case") e' : map (\(Alt _ e) -> e) alts
        in checklistOfExprs eenv altsExpr ng names
         
    | otherwise = trace("I am in otherwise ") Skip

checklistOfExprs :: ExprEnv -> [Expr] -> NameGen -> HS.HashSet Name -> ExecOrSkip
checklistOfExprs eenv [] ng names = Skip
checklistOfExprs eenv (e : es) ng names = trace("I am in checklistOfExprs") isExecOrSkip (canAddToNRPC eenv e ng names) (checklistOfExprs eenv es ng names)