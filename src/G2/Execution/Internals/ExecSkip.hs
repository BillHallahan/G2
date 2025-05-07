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
        reachesSymbolic
    ) where

import qualified Control.Monad.State as SM
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import qualified G2.Language.ExprEnv as E
import G2.Language
import G2.Execution.NormalForms ( normalForm )

data ExecOrSkip = ExecI -- ^ The expression must be executed
                    Name -- ^ Name of a "checkpoint function", see Note [Memoization and SWHNF]
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

-- Note [Memoization and SWHNF]
-- We memoize our delayability and reaches symbolic values checks.  However, laziness can make this tricky,
-- as a non-SWHNF thunk which includes a "must exec" function or a symbolic variable may be rewritten to a
-- SWHNF value which does not. It is thus possible for a definition for which we returned EXEC to become
-- a definition for which we should return SKIP (the opposite situation cannot occur.)
-- Similarly, an expression which includes a symbolic variable may be rewritten to an expression that does
-- not include a symbolic variable (but not vice versa.)
-- Below, we focus on delayability checks- but the handling for symbolic variables is analogous. 
--
-- Because we search through variable names, we may even have situations like the following:
--
--   x -> 1:ys
--   ys -> 2:zs
--   zs -> ws
--   ws -> f as
--
-- If f is "must exec", then x will be "must exec" as well.  We would like to memoize this result, so that we
-- avoid (potentially expensive) delayabilty checks in the future.  However, now suppose ws is evaluated to reach
-- an empty list, and we update the thunk for ws:
--
--   ws -> []
--
-- Now, x should be skippable.
--
-- To address this, when memoizing a delayability result for some function f, we also record a "checkpoint function" g.
-- A call to g must (1) be reachable from f following only SWHNF definitions, and (b) g's delayability result
-- must be EXEC (at the time the result is memoized.)  These checkpoint values essentially form a linked list from
-- a definition through each successive EXEC function, ending at a "must exec" function.
--
-- When we see a memoized value, we search down through the checkpoint values until we either
-- (1) reach a "must exec" value, in which case we return EXEC
-- or
-- (2) reach a SWHNF definition being used as a checkpoint, at which point we know we must discard the memoized value and recompute.

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
                    -- See Note [Memoization and SWHNF].  For memoization of an Exec result for a function f, we want a
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


data ReachesSym = ReachesSym -- ^ A symbolic variable can be reached from the variable definition
                    (Maybe Name) -- ^ Name of a "checkpoint function", see Note [Memoization and SWHNF]
                                 -- Can be Nothing when returned from a SymGen
                | NotReachesSym -- ^ A symbolic variable cannot be reached from the variable definition
type ReachesSymMemoTable = HM.HashMap Name ReachesSym

instance Semigroup ReachesSym where
    NotReachesSym <> NotReachesSym = NotReachesSym
    rs@(ReachesSym _) <> _ = rs
    _ <> rs@(ReachesSym _) = rs

instance Monoid ReachesSym where
    mempty = NotReachesSym

-- | Can evaluating the Expr branch? Or is it fully concrete (including looking through variables.)
reachesSymbolic :: ReachesSymMemoTable -> ExprEnv -> Expr -> (Bool, ReachesSymMemoTable)
reachesSymbolic rsmt eenv e = 
    let 
        (res, rsmt') = SM.runState (reachesSymbolic' eenv e) rsmt
        res' = case res of
                    ReachesSym _ -> True
                    NotReachesSym -> False 
    in (res', rsmt')

reachesSymbolic' :: SM.MonadState ReachesSymMemoTable m => ExprEnv -> Expr -> m ReachesSym
reachesSymbolic' eenv = go
    where
        go (SymGen _ _) = return (ReachesSym Nothing)
        go (Var (Id n _)) = do
            let e = E.lookupConcOrSym n eenv
            memo <- SM.get
            case HM.lookup n memo of
                Just NotReachesSym -> return $ NotReachesSym
                Just (ReachesSym n') | checkNotNormalForm memo (Just n) -> return (ReachesSym n')
                _ | Just (E.Conc e') <- e ->  do
                    SM.modify (HM.insert n NotReachesSym)
                    r <- go e'
                    SM.modify (HM.insert n r)
                    -- See Note [Memoization and SWHNF].  For memoization of a ReachesSymbolic result for a function f, we
                    -- want a checkpoint function g that is (a) reachable from f only through SWHNF definitions and (b) returns
                    -- the result ReachesSymbolic.  We thus ensure that we are returning ReachesSymbolic's that fit these
                    -- two conditions
                    let r' = case r of
                                NotReachesSym -> r
                                ReachesSym _ -> if normalForm eenv e' then r else ReachesSym (Just n)

                    return r'
                  | Just (E.Sym _) <- e -> return (ReachesSym (Just n))
                  | otherwise -> return NotReachesSym
        go e = return . mconcat =<< mapM go (children e)

        checkNotNormalForm memo (Just n) | E.isSymbolic n eenv = True
                                         | Just e <- E.lookup n eenv
                                         , not (normalForm eenv e) =
                                            case HM.lookup n memo of
                                                Just (ReachesSym Nothing) -> True
                                                Just (ReachesSym n') -> checkNotNormalForm memo n'
                                                Just NotReachesSym -> False
                                                Nothing -> False
                                         | otherwise = False
        checkNotNormalForm _ Nothing = True