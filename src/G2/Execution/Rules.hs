{-# LANGUAGE OverloadedStrings #-}

module G2.Execution.Rules ( module G2.Execution.RuleTypes
                          , Sharing (..)
                          , stdReduce
                          , evalVarSharing
                          , evalApp
                          , evalLam
                          , retLam
                          , evalLet
                          , evalCase
                          , evalCast
                          , evalTick
                          , evalNonDet
                          , evalSymGen
                          , evalAssume
                          , evalAssert
                          , isExecValueForm ) where

import G2.Config.Config
import G2.Execution.NormalForms
import G2.Execution.PrimitiveEval
import G2.Execution.RuleTypes
import qualified G2.Execution.MergingHelpers as SM
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as S
import G2.Solver hiding (Assert)

import Control.Monad.Extra
import Data.Maybe
import qualified Data.HashSet as HS
import qualified Data.List as L

stdReduce :: Solver solver => Sharing -> solver -> State t -> Bindings -> IO (Rule, [(State t, ())], Bindings)
stdReduce sharing solver s b@(Bindings {name_gen = ng}) = do
    (r, s', ng') <- stdReduce' sharing solver s ng
    let s'' = map (\ss -> ss { rules = r:rules ss }) s'
    return (r, zip s'' (repeat ()), b { name_gen = ng'})

stdReduce' :: Solver solver => Sharing -> solver -> State t -> NameGen -> IO (Rule, [State t], NameGen)
stdReduce' share solver s@(State { curr_expr = CurrExpr Evaluate ce }) ng
    | Var i  <- ce
    , share == Sharing = return $ evalVarSharing s ng i
    | Var i <- ce
    , share == NoSharing = return $ evalVarNoSharing s ng i
    | App e1 e2 <- ce = return $ evalApp s ng e1 e2
    | Let b e <- ce = return $ evalLet s ng b e
    | Case e i a <- ce = do
        (r, xs, ng') <- evalCaseSMNF solver s ng e i a
        -- let (r, xs, ng') = evalCase s ng e i a
        xs' <- mapMaybeM (reduceNewPC solver) xs
        return (r, xs', ng')
    | Cast e c <- ce = return $ evalCast s ng e c
    | Tick t e <- ce = return $ evalTick s ng t e
    | NonDet es <- ce = return $ evalNonDet s ng es
    | SymGen t <- ce = return $ evalSymGen s ng t
    | Assume fc e1 e2 <- ce = return $ evalAssume s ng fc e1 e2
    | Assert fc e1 e2 <- ce = return $ evalAssert s ng fc e1 e2
    | otherwise = return (RuleReturn, [s { curr_expr = CurrExpr Return ce }], ng)
stdReduce' _ solver s@(State { curr_expr = CurrExpr Return ce
                             , exec_stack = stck }) ng
    | Prim Error _ <- ce
    , Just (AssertFrame is _, stck') <- S.pop stck =
        return (RuleError, [s { exec_stack = stck'
                              , true_assert = True
                              , assert_ids = is }], ng)
    | Prim Error _ <- ce
    , Just (_, stck') <- S.pop stck = return (RuleError, [s { exec_stack = stck' }], ng)
    | Just (MergePtFrame, stck') <- frstck = return (RuleHitMergePt, [s {exec_stack = stck'}], ng)
    | Just (UpdateFrame n, stck') <- frstck = return $ retUpdateFrame s ng n stck'
    | Lam u i e <- ce = return $ retLam s ng u i e
    | Just (ApplyFrame e, stck') <- S.pop stck = return $ retApplyFrame s ng ce e stck'
    | Just rs <- retReplaceSymbFunc s ng ce = return rs
    | Just (CaseFrame i a, stck') <- frstck = return $ retCaseFrame s ng ce i a stck'
    | Just (CastFrame c, stck') <- frstck = return $ retCastFrame s ng ce c stck'
    | Just (AssumeFrame e, stck') <- frstck = do
        let (r, xs, ng') = retAssumeFrame s ng ce e stck'
        xs' <- mapMaybeM (reduceNewPC solver) xs
        return (r, xs', ng')
    | Just (AssertFrame ais e, stck') <- frstck = do
        let (r, xs, ng') = retAssertFrame s ng ce ais e stck'
        xs' <- mapMaybeM (reduceNewPC solver) xs
        return (r, xs', ng')
    | Just (CurrExprFrame e, stck') <- frstck = do
        let (r, xs) = retCurrExpr s ce e stck'
        xs' <- mapMaybeM (reduceNewPC solver) xs
        return (r, xs', ng)
    | Nothing <- frstck = return (RuleIdentity, [s], ng)
    | otherwise = error $ "stdReduce': Unknown Expr" ++ show ce ++ show (S.pop stck)
        where
            frstck = S.pop stck

data NewPC t = NewPC { state :: State t
                     , new_pcs :: [PathCond] }

newPCEmpty :: State t -> NewPC t
newPCEmpty s = NewPC { state = s, new_pcs = []}

reduceNewPC :: Solver solver => solver -> NewPC t -> IO (Maybe (State t))
reduceNewPC solver
            (NewPC { state = s@(State { path_conds = spc })
                   , new_pcs = pc })
    | not (null pc) = do
        -- In the case of newtypes, the PC exists we get may have the correct name
        -- but incorrect type.
        -- We do not want to add these to the State
        -- This is a bit ugly, but not a huge deal, since the State already has PCExists
        let pc' = filter (not . PC.isPCExists) pc

        -- Optimization
        -- We replace the path_conds with only those that are directly
        -- affected by the new path constraints
        -- This allows for more efficient solving, and in some cases may
        -- change an Unknown into a SAT or UNSAT
        let new_pc = foldr PC.insert spc $ pc'
            s' = s { path_conds = new_pc}

        let rel_pc = PC.filter (not . PC.isPCExists) $ PC.relevant pc new_pc

        res <- check solver s rel_pc

        if res == SAT then
            return $ Just s'
        else
            return Nothing
    | otherwise = return $ Just s

evalVarSharing :: State t -> NameGen -> Id -> (Rule, [State t], NameGen)
evalVarSharing s@(State { expr_env = eenv
                        , exec_stack = stck })
               ng i
    | E.isSymbolic (idName i) eenv =
        (RuleEvalVal, [s { curr_expr = CurrExpr Return (Var i)}], ng)
    -- If the target in our environment is already a value form, we do not
    -- need to push additional redirects for updating later on.
    -- If our variable is not in value form, we first push the
    -- current name of the variable onto the stack and evaluate the
    -- expression that it points to. After the evaluation,
    -- we pop the stack to add a redirection pointer into the heap.
    | Just e' <- e
    , isExprValueForm eenv e' =
      ( RuleEvalVarVal (idName i), [s { curr_expr = CurrExpr Evaluate e' }], ng)
    | Just e' <- e = -- e' is NOT in SWHNF
      ( RuleEvalVarNonVal (idName i)
      , [s { curr_expr = CurrExpr Evaluate e'
           , exec_stack = S.push (UpdateFrame (idName i)) stck }]
      , ng)
    | otherwise = error  $ "evalVar: bad input." ++ show i
    where
        e = E.lookup (idName i) eenv

evalVarNoSharing :: State t -> NameGen -> Id -> (Rule, [State t], NameGen)
evalVarNoSharing s@(State { expr_env = eenv })
                 ng i
    | E.isSymbolic (idName i) eenv =
        (RuleEvalVal, [s { curr_expr = CurrExpr Return (Var i)}], ng)
    | Just e <- E.lookup (idName i) eenv =
        (RuleEvalVarNonVal (idName i), [s { curr_expr = CurrExpr Evaluate e }], ng)
    | otherwise = error  $ "evalVar: bad input." ++ show i

-- | If we have a primitive operator, we are at a point where either:
--    (1) We can concretely evaluate the operator, or
--    (2) We have a symbolic value, and no evaluation is possible, so we return
-- If we do not have a primitive operator, we go into the center of the apps,
-- to evaluate the function call
evalApp :: State t -> NameGen -> Expr -> Expr -> (Rule, [State t], NameGen)
evalApp s@(State { expr_env = eenv
                 , known_values = kv
                 , exec_stack = stck })
        ng e1 e2
    | (App (Prim BindFunc _) v) <- e1
    , Var i1 <- findSym v
    , v2 <- e2 =
        ( RuleBind
        , [s { expr_env = E.insert (idName i1) v2 eenv
             , curr_expr = CurrExpr Return (mkTrue kv) }]
        , ng)
    | isExprValueForm eenv (App e1 e2) =
        ( RuleReturnAppSWHNF
        , [s { curr_expr = CurrExpr Return (App e1 e2) }]
        , ng)
    | (Prim prim ty):ar <- unApp (App e1 e2) = 
        let
            ar' = map (lookupForPrim eenv) ar
            appP = mkApp (Prim prim ty : ar')
            -- replace any Case Exprs in appP with a Symbolic variable to ensure the Expr is in Symbolic Weak Head Normal Form
            (s', ng', appP') = SM.replaceCaseWSym s ng appP
            exP = evalPrims kv appP'
        in
        ( RuleEvalPrimToNorm
        , [s' { curr_expr = CurrExpr Return exP }]
        , ng')
    | otherwise =
        let
            frame = ApplyFrame e2
            stck' = S.push frame stck
        in
        ( RuleEvalApp e2
        , [s { curr_expr = CurrExpr Evaluate e1
             , exec_stack = stck' }]
        , ng)
    where
        findSym v@(Var (Id n _))
          | E.isSymbolic n eenv = v
          | Just e <- E.lookup n eenv = findSym e
        findSym _ = error "findSym: No symbolic variable"

lookupForPrim :: ExprEnv -> Expr -> Expr
lookupForPrim eenv v@(Var (Id _ _)) = repeatedLookup eenv v
lookupForPrim eenv (App e e') = App (lookupForPrim eenv e) (lookupForPrim eenv e')
lookupForPrim _ e = e

repeatedLookup :: ExprEnv -> Expr -> Expr
repeatedLookup eenv v@(Var (Id n _))
    | E.isSymbolic n eenv = v
    | otherwise = 
        case E.lookup n eenv of
          Just v'@(Var _) -> repeatedLookup eenv v'
          Just e -> e
          Nothing -> v
repeatedLookup _ e = e

evalLam :: State t -> LamUse -> Id -> Expr -> (Rule, [State t])
evalLam = undefined

retLam :: State t -> NameGen -> LamUse -> Id -> Expr -> (Rule, [State t], NameGen)
retLam s@(State { expr_env = eenv
                , exec_stack = stck })
       ng u i e
    | TypeL <- u
    , Just (ApplyFrame tf, stck') <- S.pop stck =
        case traceType eenv tf of
        Just t ->
            let
                e' = retype i t e

                binds = [(i, Type t)]
                (eenv', e'', ng', news) = liftBinds binds eenv e' ng
            in
            ( RuleReturnEApplyLamType news
            , [s { expr_env = eenv'
                 , curr_expr = CurrExpr Evaluate e''
                 , exec_stack = stck' }]
            , ng')
        Nothing -> error "retLam: Bad type"
    | TermL <- u
    , Just (ApplyFrame ae, stck') <- S.pop stck =
        let
            binds = [(i, ae)]
            (eenv', e', ng', news) = liftBinds binds eenv e ng
        in
        ( RuleReturnEApplyLamExpr news
        , [s { expr_env = eenv'
             , curr_expr = CurrExpr Evaluate e'
             , exec_stack = stck' }]
        ,ng')
    | otherwise = error "retLam: Bad type"

traceType :: E.ExprEnv -> Expr -> Maybe Type
traceType _ (Type t) = Just t
traceType eenv (Var (Id n _)) = traceType eenv =<< E.lookup n eenv
traceType _ _ = Nothing

evalLet :: State t -> NameGen -> Binds -> Expr -> (Rule, [State t], NameGen)
evalLet s@(State { expr_env = eenv }) 
        ng binds e =
    let
        (binds_lhs, binds_rhs) = unzip binds

        olds = map idName binds_lhs
        (news, ng') = freshSeededNames olds ng

        e' = renameExprs (zip olds news) e
        binds_rhs' = renameExprs (zip olds news) binds_rhs

        eenv' = E.insertExprs (zip news binds_rhs') eenv
    in
    (RuleEvalLet news, [s { expr_env = eenv'
                          , curr_expr = CurrExpr Evaluate e'}]
                     , ng')

-------------------------------------------------------------
--  evalCase that makes use of Symbolic Merged Normal Form --
-------------------------------------------------------------
type Cond = (Id, Integer)
type Assumption = Expr

data Matches = Matches { symbolic_vars :: [(Expr, [Assumption])]
                       , lits :: [(Expr, [Assumption])]
                       , constructors :: [(Expr, [Assumption])]
                       , prims :: [(Expr, [Assumption])]
                       , defaults :: [(Expr, [Assumption])]} deriving (Show)

emptyMatch :: Matches
emptyMatch = Matches { symbolic_vars = [], lits = [], constructors = [], prims = [], defaults = []}

isEmptyMatch :: Matches -> Bool
isEmptyMatch (Matches { symbolic_vars = s
                      , lits = l
                      , constructors = c
                      , prims = p
                      , defaults = d}) =
    (null s) && (null l) && (null c) && (null p) && (null d)

assumes :: Matches -> [[Assumption]]
assumes (Matches { symbolic_vars = s
                 , lits = l
                 , constructors = c
                 , prims = p
                 , defaults = d}) = map snd m
    where
        m = filter (not . null . snd) $ s ++ l ++ c ++ p ++ d

-- | Handle the Case forms of Evaluate.
evalCaseSMNF :: Solver solver => solver -> State t -> NameGen -> Expr -> Id -> [Alt] -> IO (Rule, [NewPC t], NameGen)
evalCaseSMNF solver s@(State { expr_env = eenv
                         , exec_stack = stck })
         ng mexpr bind alts
    -- Case evaluation also uses the stack in graph reduction based evaluation
    -- semantics. The case's binding variable and alts are pushed onto the stack
    -- as a `CaseFrame` along with their appropriate `ExecExprEnv`. However this
    -- is only done when the matching expression is NOT in value form. Value
    -- forms should be handled by other RuleEvalCase* rules.
    | not (isSMNF eenv mexpr) = do -- TODO: inline vars if necessary to get it into SMNF
        let frame = CaseFrame bind alts
        return ( RuleEvalCaseNonVal
               , [newPCEmpty $ s { expr_env = eenv
                                 , curr_expr = CurrExpr Evaluate mexpr
                                 , exec_stack = S.push frame stck }], ng)
    | otherwise = do
        choices <- getChoices solver s mexpr
        return $ evalCaseSMNF' s ng choices bind alts

-- | Given a `Case` expr in SMNF, returns a list of pairs of the nested Exprs and their associated Assume-d Exprs
-- e.g. getChoices Case (Var x) of 1 -> A, 2 -> (Case y of 1-> C, 2-> D) =
-- [(A, [(x == 1)]), (C, [(x == 2), (y == 1)]), (D, [(x == 2), (y == 1)])
getChoices :: Solver solver => solver -> State t -> Expr -> IO ([(Expr, [Assumption])])
getChoices solver s@(State {known_values = kv}) e@(Case _ _ _) = do
    let choices = getTopLevelExprs e -- [(Expr, Cond)]
    -- filter choices based on `Cond`
    choices' <- mapMaybeM (\(expr, (i, num)) ->
        let assum = mkEqIntExpr kv (Var i) num
        in checkNewPC solver s (ExtCond assum True) expr assum) choices
    concatMapM (\(expr, assum, s') ->
        -- extract Exprs and Assumptions in any nested NonDets
        getChoices solver s' expr
        -- add top level assumed expr to each of these. Order of Assumptions matters if we want to wrap them in AssumePCs later
        >>= mapM (\(exp', assums) -> return (exp', assum:assums))) choices'
getChoices _ _ e = return [(e, [])]

getTopLevelExprs :: Expr -> [(Expr, Cond)]
getTopLevelExprs (Case (Var i) b (a:as))
    | (Alt (LitAlt (LitInt num)) e) <- a = (e, (i, num)):getTopLevelExprs (Case (Var i) b as)
    | otherwise = error "getTopLevelExprs called with Expr not from result of merging states. "
getTopLevelExprs (Case _ _ []) = []
getTopLevelExprs _ = []

checkNewPC :: Solver solver => solver -> State t -> PathCond -> Expr -> Assumption -> IO (Maybe (Expr, Assumption, State t))
checkNewPC solver s@(State { path_conds = spc }) pc e assum
    -- In the case of newtypes, the PC exists we get may have the correct name but incorrect type.
    -- We do not want to add these to the State
    -- This is a bit ugly, but not a huge deal, since the State already has PCExists
    | (not . PC.isPCExists) pc = do
        -- Replace the path_conds with only those that are directly
        -- affected by the new path constraints
        -- This allows for more efficient solving, and in some cases may
        -- change an Unknown into a SAT or UNSAT
        let new_pc = PC.insert pc spc
            s' = s { path_conds = new_pc}
            rel_pc = PC.filter (not . PC.isPCExists) $ PC.relevant [pc] new_pc

        res <- check solver s rel_pc

        if res == SAT then
            return $ Just (e, assum, s')
        else
            return Nothing
    | otherwise = return $ Just (e, assum, s)

-- | Handle the Case forms of Evaluate.
evalCaseSMNF' :: State t -> NameGen -> [(Expr, [Assumption])] -> Id -> [Alt] -> (Rule, [NewPC t], NameGen)
evalCaseSMNF' s@(State { expr_env = eenv }) ng choices bind alts =
    let
        dalts = dataAltsSMNF alts
        lalts = litAltsSMNF alts
        defs = defaultAltsSMNF alts
        -- for each (DataAlt dcon params) match all choices that are: (i) Symbolic Variables
        -- (ii) Apps with a (Data dcon') center where dcon` == dcon and number of Apps == length params
        -- (iii) Apps with Prim center
        (daltMatches, choices') = matchDataAltsSMNF eenv dalts choices
        -- for each (LitAlt lit), match all Symbolic Variables, and Exprs of the form (Lit i) where i == lit.
        -- Delete any (Lit _) that matches from choices
        (laltMatches, choices'') = matchLitAltsSMNF eenv lalts choices'
        -- Match all Symbolic Variables and unmatched Apps with a (Data _) center
        (defMatches, _) = matchDefaults defs choices''
        --TODO: ensure choices''' is empty

        -- split into multiple states on the various Alts appropriately
        (dsts_cs, ng') = handleDaltMatches s ng daltMatches bind
        lsts_cs = handleLaltMatches s laltMatches bind 
        def_sts = handleDefMatches s defMatches bind alts
        newPCs = def_sts ++ dsts_cs ++ lsts_cs
        newPCs' = map (\p@(NewPC {state = st}) -> p {state = st {exec_stack = S.push MergePtFrame (exec_stack st)} }) newPCs
    in (RuleEvalCaseSym, newPCs', ng') -- TODO: new rule

dataAltsSMNF :: [Alt] -> [Alt]
dataAltsSMNF alts = [a | a @ (Alt (DataAlt _ _) _) <- alts]

litAltsSMNF :: [Alt] -> [Alt]
litAltsSMNF alts = [a | a @ (Alt (LitAlt _) _) <- alts]

defaultAltsSMNF :: [Alt] -> [Alt]
defaultAltsSMNF alts = [a | a @ (Alt Default _) <- alts]

matchDataAltsSMNF :: E.ExprEnv -> [Alt] -> [(Expr, [Assumption])] -> ([(Alt, Matches)], [(Expr, [Assumption])])
matchDataAltsSMNF eenv (alt:alts) choices =
    let
        (x', choices') = matchDataAlt eenv alt choices
        (xs, choices'') = matchDataAltsSMNF eenv alts choices'
    in case isEmptyMatch . snd $ x' of --filter out alts without any matches
        True -> (xs, choices'')
        False -> (x':xs, choices'')
matchDataAltsSMNF _ [] choices = ([], choices)

-- | If a choice in `choices` matches with the given `alt`, add to `matches`. Delete the match from `choices` if appropriate
matchDataAlt :: E.ExprEnv -> Alt -> [(Expr, [Assumption])] -> ((Alt, Matches), [(Expr, [Assumption])])
matchDataAlt eenv alt (x@(mexpr, _):xs)
    | (Alt (DataAlt dcon params) _) <- alt
    , (DataCon n _) <- dcon
    , (Data dcon'):ar <- unApp $ exprInCasts mexpr
    , (DataCon n' _) <- dcon'
    , ar' <- removeTypes ar eenv
    , n == n'
    , length params == length ar' =
        let
           ((_, matches'@(Matches {constructors = dcons})), choices') = matchDataAlt eenv alt xs
        in ((alt, matches' {constructors = x:dcons}), choices') -- delete x from choices
    | (Var (Id n _)):_ <- unApp $ unsafeElimOuterCast mexpr
    , E.isSymbolic n eenv =
        let
            ((_, matches'@(Matches {symbolic_vars = syms})), choices') = matchDataAlt eenv alt xs
        in ((alt, matches' {symbolic_vars = x:syms}), x:choices') -- keep x in choices
    | (Prim _ _):_ <- unApp $ unsafeElimOuterCast mexpr =
        let
            ((_, matches'@(Matches {prims = pr})), choices') = matchDataAlt eenv alt xs
        in ((alt, matches' {prims = x:pr}), x:choices') -- keep x in choices
    | otherwise = 
        let 
            ((_, matches'), choices') = matchDataAlt eenv alt xs
        in ((alt, matches'), x:choices')
matchDataAlt _ alt [] = ((alt, emptyMatch), [])

matchLitAltsSMNF :: E.ExprEnv -> [Alt] -> [(Expr, [Assumption])] -> ([(Alt, Matches)], [(Expr, [Assumption])])
matchLitAltsSMNF eenv (alt:alts) choices =
    let
        (x', choices') = matchLitAlt eenv alt choices
        (xs, choices'') = matchLitAltsSMNF eenv alts choices'
    in case isEmptyMatch . snd $ x' of -- filter out Alts without any matches
        True -> (xs, choices'')
        False -> (x':xs, choices'')
matchLitAltsSMNF _ [] choices = ([], choices)

-- | If a choice in `choices` matches with the given `alt`, add to `matches`
matchLitAlt :: E.ExprEnv -> Alt -> [(Expr, [Assumption])] -> ((Alt, Matches), [(Expr, [Assumption])])
matchLitAlt eenv alt (x@(mexpr, _):xs)
    | (Lit lit) <- unsafeElimOuterCast mexpr
    , (Alt (LitAlt lit') _) <- alt
    , lit == lit' =
        let
            ((_, matches'@(Matches {lits = l})), choices') = matchLitAlt eenv alt xs
        in ((alt, matches' {lits = x:l}), choices') -- delete x from choices
    | (Var (Id n _)):_ <- unApp $ unsafeElimOuterCast mexpr
    , E.lookup n eenv == Nothing || E.isSymbolic n eenv =
        let
            ((_, matches'@(Matches {symbolic_vars = syms})), choices') = matchLitAlt eenv alt xs
        in ((alt, matches' {symbolic_vars = x:syms}), x:choices') -- keep x in choices
    | (Prim _ _):_ <- unApp $ unsafeElimOuterCast mexpr =
        let
            ((_, matches'@(Matches {prims = pr})), choices') = matchLitAlt eenv alt xs
        in ((alt, matches' {prims = x:pr}), x:choices') -- keep x in choices
    | otherwise = 
        let 
            ((_, matches'), choices') = matchLitAlt eenv alt xs
        in ((alt, matches'), x:choices')
matchLitAlt _ alt [] = ((alt, emptyMatch), [])

matchDefaults :: [Alt] -> [(Expr, [Assumption])] -> ([(Alt, Matches)], [(Expr, [Assumption])])
matchDefaults _ [] = ([], [])
matchDefaults [] choices = ([], choices)
matchDefaults (alt:_) choices =
    let
        x = (alt, emptyMatch)
        (x', choices') = matchDefault x choices -- only need to look at 1 Default choice
    in ([x'], choices')

-- | If a choice in `choices` hits a Default `alt`, add to `matches`
-- The distinctions between the `constructors`, `lits` etc. fields in `matches` matter less here because execution proceeds on the Default Alt
-- in the same manner anyway
matchDefault :: (Alt, Matches) -> [(Expr, [Assumption])] -> ((Alt, Matches), [(Expr, [Assumption])])
matchDefault (alt, matches@(Matches {defaults = d})) choices = ((alt, matches {defaults = choices ++ d}), [])

handleLaltMatches :: State t -> [(Alt, Matches)] -> Id -> [NewPC t]
handleLaltMatches s@(State {known_values = kv}) ((alt, matches):alts) bind
    | (Alt (LitAlt lit) aexpr) <- alt 
    , (not $ null (symbolic_vars matches)) || (not $ null (lits matches)) || (not $ null (prims matches)) =
        let 
            -- for all SymbolicVars @(Var i), add the PathCond: `AssumePC _ _ (.... (AltCond lit (Var i))..)` True
            conds = map (makePCEqLit lit) $ (symbolic_vars matches ++ prims matches)
            assums = assumes matches
            conds' = case assums of
                [] -> conds
                _ -> let
                        assumsE = (mkAssumExpr kv) <$> assums
                        cond = ExtCond (dnf kv assumsE) True
                    in cond:conds
            binds = [(bind, Lit lit)]
            aexpr' = liftCaseBinds binds aexpr
            s' = s {curr_expr = CurrExpr Evaluate aexpr'}
            newPC = NewPC {state = s', new_pcs = conds'}

            newPCs = handleLaltMatches s alts bind
        in newPC:newPCs
    | otherwise = handleLaltMatches s alts bind
handleLaltMatches _ [] _ = []

makePCEqLit :: Lit -> (Expr, [Assumption]) -> PathCond
makePCEqLit l (e, xs) = wrapPC xs pc
    where pc = AltCond l e True

handleDaltMatches :: State t -> NameGen -> [(Alt, Matches)] -> Id -> ([NewPC t], NameGen)
handleDaltMatches s@(State {known_values = kv}) ng ((alt, matches):alts) bind
    | (Alt (DataAlt dcon params) aexpr) <- alt =
        let
            -- TODO: refactor & combine all 3 into one
            (apps, tyApps, newPC, ng', cast) = L.foldr (\(mexpr, assum) (asL, tyAsL, _newPC, ngen, _) ->
                let st = state _newPC
                    -- TODO deal with cast
                    (cast_', expr) = case mexpr of
                        (Cast e c) -> (Just c, e)
                        _ -> (Nothing, mexpr)

                    expr_id = case unApp $ unsafeElimOuterCast expr of
                        (Var i@(Id _ _)):_ -> i
                        _ -> error $ "Non Var expr:" ++ show expr

                    (as, tyAs, _newPC', ngen') = handleDaltSymMatch st ngen (dcon, params) (expr_id, assum) cast_'
                    -- Take a list of arguments `as`, and an Expr equiv. to AND-ing together `assum`, wraps each argument in
                    -- the Assum-ed expr
                    as' = case assum of
                        [] -> as
                        _ -> let
                            assumE = mkAssumExpr kv assum
                            wrapAssum = (\a -> Assume Nothing assumE a)
                            in wrapAssum <$> as

                    _oldPCs = new_pcs _newPC
                    _newPC'' = _newPC' {new_pcs = _oldPCs ++ (new_pcs _newPC')}
                in (as':asL, tyAs:tyAsL, _newPC'', ngen', cast_')) ([], [], newPCEmpty s, ng, Nothing) (symbolic_vars matches)

            (apps', newPC', ng'', cast') = L.foldr (\(mexpr, assum) (asL, _newPC, ngen, _) ->
                let st = state _newPC
                    (cast_, expr) = case mexpr of
                        (Cast e c) -> (Just c, e)
                        _ -> (Nothing, mexpr)

                    (as, _newPC', ngen') = handleDaltPrimMatch st ngen (dcon, params) (expr, assum)
                    as' = case assum of
                        [] -> as
                        _ -> let
                            assumE = mkAssumExpr kv assum
                            wrapAssum = (\a -> Assume Nothing assumE a)
                            in wrapAssum <$> as

                    _oldPCs = new_pcs _newPC
                    _newPC'' = _newPC' {new_pcs = _oldPCs ++ (new_pcs _newPC')}
                in (as':asL, _newPC'', ngen', cast_)) (apps, newPC, ng', cast) (prims matches)

            (apps'', tyApps', newPC'', ng''') = L.foldr (\(mexpr, assum) (asL, tyAsL, _newPC, ngen) -> 
                let st = state _newPC
                    (as, tyAs, _newPC', ngen') = handleDaltDconMatch st ngen (dcon, params) (mexpr, assum)
                    as' = case assum of
                        [] -> as
                        _ -> let
                            assumE = mkAssumExpr kv assum
                            wrapAssum = (\a -> Assume Nothing assumE a)
                            in wrapAssum <$> as

                    _oldPCs = new_pcs _newPC
                    _newPC'' = _newPC' {new_pcs = _oldPCs ++ (new_pcs _newPC')}
                in (as':asL, tyAs:tyAsL, _newPC'', ngen')) (apps', tyApps, newPC', ng'') (constructors matches)

            -- combine corresponding arguments from different matches into a NonDet Expr
            -- e.g. given [[a, b], [c,d]], results in [NonDet [a,c], NonDet [b,d]]
            apps''' = map (\a -> case a of
                [] -> error $ "Empty list "
                [e] -> e
                _ -> NonDet a) . L.transpose $ apps''
            -- TODO: merge types into one instead of wrapping in NonDet
            -- TODO: wrap tyApps in assums as well
            -- Do the same for Apps representing types
            tyApps'' = map (\a -> case a of
                [] -> error $ "Empty list "
                [e] -> e
                _ -> NonDet a) . L.transpose $ tyApps'

            -- Replace any occurrences of bind with the matched expr
            -- need to apply cast to dcon first
            binds = case cast' of
                Nothing -> [(bind, mkApp $ (Data dcon):(tyApps''++apps'''))]
                (Just (t1 :~ t2)) -> [(bind, Cast (mkApp $ (Data dcon):(tyApps''++apps''')) (t2 :~ t1))]
            aexpr' = liftCaseBinds binds aexpr

            -- Replace all occurrences of the `params` in aexpr with the corresponding app
            pBinds = zip params apps'''
            s'@(State {expr_env = eenv}) = state newPC''
            (eenv', aexpr'', ng'''', _) = liftBinds pBinds eenv aexpr' ng'''
            s'' = s' {expr_env = eenv'}

            -- Add PathConds representing constraints from Assume-d Exprs for each possible match
            newPCs = new_pcs newPC''
            assums = assumes matches
            newPCs' = case assums of
                [] -> newPCs
                _ -> let
                        assumsE = (mkAssumExpr kv) <$> assums
                        cond = ExtCond (dnf kv assumsE) True
                    in cond:newPCs

            newPC''' = newPC'' {state = s'' { curr_expr = CurrExpr Evaluate aexpr'' }, new_pcs = newPCs' }
            (pcs, ng''''') = handleDaltMatches s ng'''' alts bind
        in (newPC''':pcs, ng''''')
    | otherwise = error $ "Alt is not a DataAlt"
handleDaltMatches _ ng [] _ = ([], ng)

handleDaltSymMatch :: State t -> NameGen -> (DataCon, [Id]) -> (Id, [Assumption]) -> Maybe Coercion -> ([Expr],[Expr],NewPC t, NameGen)
handleDaltSymMatch s@(State {expr_env = eenv, type_env = tenv, symbolic_ids = syms, known_values = kv}) ngen (dcon, params) (mexprId, assum) maybeC =
    let
        -- rename the params and insert into expr_env
        olds = map idName params
        mexprN = idName mexprId
        (news, ngen') = childrenNames mexprN olds ngen
        newIds = map (\(Id _ t, n) -> (n, Id n t)) (zip params news)
        eenv' = foldr (uncurry E.insertSymbolic) eenv newIds

        newParams = map (uncurry Id) $ zip news (map typeOf params)
        apps = map (Var) newParams
        -- Get list of Types to concretize polymorphic data constructor
        mexprT = (\(Id _ t) -> t) mexprId
        tyApps = mexprTyToExpr mexprT tenv

        dConArgs = tyApps ++ apps
        mexpr' = mkApp (Data dcon:dConArgs)
        -- Apply cast, in opposite direction of unsafeElimOuterCast
        mexpr'' = case maybeC of
                (Just (t1 :~ t2)) -> Cast mexpr' (t2 :~ t1)
                Nothing -> mexpr'
        -- Concretize mexpr to dcon depending on the Assumption-s
        (eenv'', newParams', ngen'') = case assum of
            [] -> (E.insert mexprN mexpr'' eenv', newParams, ngen')
            _ -> let (newId, ngen_'') = freshId mexprT ngen'
                in (E.insert mexprN (NonDet [Assume Nothing (mkAssumExpr kv assum) mexpr''
                , Assume Nothing (mkNotExpr kv (mkAssumExpr kv assum)) (Var newId)]) eenv'
                , newId:newParams
                , ngen_'')
        -- Add new symbolic vars, and delete mexprId because it has been concretized
        syms' = HS.union (HS.fromList newParams') (HS.delete mexprId syms)

    in (apps, tyApps, newPCEmpty $ s {expr_env = eenv'', symbolic_ids = syms'}, ngen'')

handleDaltDconMatch :: State t -> NameGen -> (DataCon, [Id]) -> (Expr, [Assumption]) -> ([Expr], [Expr], NewPC t, NameGen)
handleDaltDconMatch s@(State {expr_env = eenv}) ngen (_, _) (mexpr, _) =
    let
        (Data _):ar = unApp $ exprInCasts mexpr
        ar' = removeTypes ar eenv
        tyApps = getTypes ar eenv
    in (ar', tyApps, newPCEmpty s, ngen)

-- The only Data Alts that match a `Prim` contain `Bool` DataCons
handleDaltPrimMatch :: State t -> NameGen -> (DataCon, [Id]) -> (Expr, [Assumption]) -> ([Expr], NewPC t, NameGen)
handleDaltPrimMatch s@(State {known_values = kv}) ng (dcon, params) (mexpr, assum) =
    let
        boolValue = getBoolFromDataCon kv (Data dcon)
        cond = ExtCond mexpr boolValue
        cond' = case assum of
            [] -> cond
            _ -> wrapPC assum cond
        apps = case (null params) of
            False -> error $ "Prim match should be of type Bool: " ++ show mexpr
            True -> [] -- Bool DataCon, so no params
    in (apps, (newPCEmpty s) { new_pcs = [cond'] }, ng)

handleDefMatches :: State t -> [(Alt, Matches)] -> Id -> [Alt] -> [NewPC t]
handleDefMatches s@(State {known_values = kv}) ((alt, matches):_) bind alts
    -- Only 1 match, no need to insert NonDet expr
    | (Alt Default aexpr) <- alt
    , (length (defaults matches) == 1)
    , mexpr <- fst . head . defaults $ matches =
        let
            binds = [(bind, mexpr)]
            aexpr' = liftCaseBinds binds aexpr
            s' = s {curr_expr = CurrExpr Evaluate aexpr'}
        in case unApp $ unsafeElimOuterCast mexpr of
            (Data _):_ -> [NewPC {state = s', new_pcs = []}]
            -- For all other matches: Add either ConsCond or AltCond False for each unmatched Alt
            _ -> let conds = mapMaybe (liftSymDefAltPCs mexpr) (map altMatch alts)
                 in [NewPC {state = s', new_pcs = conds}]
    | (Alt Default aexpr) <- alt = 
        let
            mexpr = mergeMatches kv matches -- combine all matches into 1 `NonDet` Expr
            binds = [(bind, mexpr)]
            aexpr' = liftCaseBinds binds aexpr
            s' = s {curr_expr = CurrExpr Evaluate aexpr'}
            conds = mapMaybe (liftSymDefAltPCs mexpr) (map altMatch alts)
            assums = assumes matches
            conds' = concatMap (\assum ->
                let wrappedConds = map (wrapPC assum) conds
                in wrappedConds) assums

            extConds = case assums of
                [] -> []
                _ -> let
                        assumsE = (mkAssumExpr kv) <$> assums
                        cond = ExtCond (dnf kv assumsE) True
                    in [cond]
        in [NewPC {state = s', new_pcs = conds' ++ extConds}]
    | otherwise = error $ "Alt is not a Default: " ++ show alt
handleDefMatches _ [] _ _ = []

-- When there are multiple Assumption-s in the list, order in which they are nested in the AssumePC matters.
-- `getChoices` ensures the original order is preserved
wrapPC :: [Assumption] -> PathCond -> PathCond
wrapPC (x:xs) pc = AssumePC n num pc'
    where (n, num) = SM.getAssumption x
          pc' = wrapPC xs pc
wrapPC [] pc = pc -- return pc sans AssumePC if there are no Assume-d Exprs

-- Replaces all Exprs that are not types with next element in `Params`. Assumes length `Params` == length of `Exprs` that are not types
getTypes :: [Expr] -> E.ExprEnv -> [Expr]
getTypes (ar@(Type _):es) eenv = ar:getTypes es eenv
getTypes (ar@(Var (Id n _)):es) eenv = case E.lookup n eenv of
    Just (Type _) -> ar:getTypes es eenv
    _ -> getTypes es eenv
getTypes (_:es) eenv = getTypes es eenv
getTypes [] _ = []

-- | For each (e@Expr, [Assumption]) pair in `Matches`, AND all `Assumptions` together to form new Assume-d Expr for e,
-- , and add it to a NonDet Expr.
-- e.g. given [(e1, [(Assume1, Assume2)]), (e2,[(Assume3)])]
-- return NonDet [Assume Nothing (App (App And Assume1) Assume2) e1, Assume Nothing Assume3 e2]
mergeMatches :: KnownValues -> Matches -> Expr
mergeMatches kv Matches { defaults = d } = NonDet $ mkNonDetOpts kv d

mkNonDetOpts :: KnownValues -> [(Expr, [Assumption])] -> [Expr]
mkNonDetOpts kv ((e, assum):xs) = (Assume Nothing (mkAssumExpr kv assum) e):(mkNonDetOpts kv xs)
mkNonDetOpts _ []               = []

mkAssumExpr :: KnownValues -> [Expr] -> Expr
mkAssumExpr kv (x:y:xs) = mkAssumExpr kv $ (mkAndExpr kv x y):xs
mkAssumExpr _ [x] = x

--------------------------------------------------------------------------------------


-- | Handle the Case forms of Evaluate.
evalCase :: State t -> NameGen -> Expr -> Id -> [Alt] -> (Rule, [NewPC t], NameGen)
evalCase s@(State { expr_env = eenv
                  , exec_stack = stck })
         ng mexpr bind alts
  -- Is the current expression able to match with a literal based `Alt`? If
  -- so, we do the cvar binding, and proceed with evaluation of the body.
  | (Lit lit) <- unsafeElimOuterCast mexpr
  , (Alt (LitAlt _) expr):_ <- matchLitAlts lit alts =
      let 
          binds = [(bind, Lit lit)]
          expr' = liftCaseBinds binds expr
      in ( RuleEvalCaseLit
         , [newPCEmpty $ s { expr_env = eenv
                           , curr_expr = CurrExpr Evaluate expr' }], ng)

  -- Is the current expression able to match a data consturctor based `Alt`?
  -- If so, then we bind all the parameters to the appropriate arguments and
  -- proceed with the evaluation of the `Alt`'s expression. We also make sure
  -- to perform the cvar binding.
  -- We unwrap the outermost cast from the mexpr.  It must be being cast
  -- to the DataCon type, so this is safe, and needed for our pattern matching.
  -- We do not want to remove casting from any of the arguments since this could
  -- mess up there types later
  | (Data dcon):ar <- unApp $ exprInCasts mexpr
  , (DataCon _ _) <- dcon
  , ar' <- removeTypes ar eenv
  , (Alt (DataAlt _ params) expr):_ <- matchDataAlts dcon alts
  , length params == length ar' =
      let
          dbind = [(bind, mexpr)]
          expr' = liftCaseBinds dbind expr
          pbinds = zip params ar'
          (eenv', expr'', ng', news) = liftBinds pbinds eenv expr' ng
      in 
         ( RuleEvalCaseData news
         , [newPCEmpty $ s { expr_env = eenv'
                           , curr_expr = CurrExpr Evaluate expr''}] 
         , ng')

  -- We are not able to match any constructor but don't have a symbolic variable?
  -- We hit a DEFAULT instead.
  -- We perform the cvar binding and proceed with the alt
  -- expression.
  | (Data _):_ <- unApp $ unsafeElimOuterCast mexpr
  , (Alt _ expr):_ <- matchDefaultAlts alts =
      let 
          binds = [(bind, mexpr)]
          expr' = liftCaseBinds binds expr
      in ( RuleEvalCaseDefault
         , [newPCEmpty $ s { expr_env = eenv
                           , curr_expr = CurrExpr Evaluate expr' }], ng)

  -- If we are pointing to something in expr value form, that is not addressed
  -- by some previous case, we handle it by branching on every `Alt`, and adding
  -- path constraints.
  | isExprValueForm eenv mexpr
  , dalts <- dataAlts alts
  , lalts <- litAlts alts
  , defs <- defaultAlts alts
  , (length dalts + length lalts + length defs) > 0 =
    let
        (cast, expr) = case mexpr of
            (Cast e c) -> (Just c, e)
            _ -> (Nothing, mexpr)

        (dsts_cs, ng') = case unApp $ unsafeElimOuterCast expr of
            (Var i@(Id _ _)):_ -> concretizeVarExpr s ng i bind dalts cast 
            (Prim _ _):_ -> createExtConds s ng expr bind dalts
            (Lit _):_ -> ([], ng)
            (Data _):_ -> ([], ng)
            _ -> error $ "unmatched expr" ++ show (unApp $ unsafeElimOuterCast mexpr)
            
        lsts_cs = liftSymLitAlt s mexpr bind lalts
        def_sts = liftSymDefAlt s mexpr bind alts
        newPCs = dsts_cs ++ lsts_cs ++ def_sts
        newPCs' = map (\p@(NewPC {state = st}) -> p{state = st{exec_stack = S.push MergePtFrame (exec_stack st)}}) newPCs
      in
      (RuleEvalCaseSym, newPCs', ng')

  -- Case evaluation also uses the stack in graph reduction based evaluation
  -- semantics. The case's binding variable and alts are pushed onto the stack
  -- as a `CaseFrame` along with their appropriate `ExecExprEnv`. However this
  -- is only done when the matching expression is NOT in value form. Value
  -- forms should be handled by other RuleEvalCase* rules.
  | not (isExprValueForm eenv mexpr) =
      let frame = CaseFrame bind alts
      in ( RuleEvalCaseNonVal
         , [newPCEmpty $ s { expr_env = eenv
                           , curr_expr = CurrExpr Evaluate mexpr
                           , exec_stack = S.push frame stck }], ng)

  | otherwise = error $ "reduceCase: bad case passed in\n" ++ show mexpr ++ "\n" ++ show alts

-- | Remove everything from an [Expr] that are actually Types.
removeTypes :: [Expr] -> E.ExprEnv -> [Expr]
removeTypes ((Type _):es) eenv = removeTypes es eenv
removeTypes ((Var (Id n ty)):es) eenv = case E.lookup n eenv of
    Just (Type _) -> removeTypes es eenv
    _ -> (Var (Id n ty)) : removeTypes es eenv
removeTypes (e:es) eenv = e : removeTypes es eenv
removeTypes [] _ = []

-- | DEFAULT `Alt`s.
matchDefaultAlts :: [Alt] -> [Alt]
matchDefaultAlts alts = [a | a @ (Alt Default _) <- alts]

-- | Match data constructor based `Alt`s.
matchDataAlts :: DataCon -> [Alt] -> [Alt]
matchDataAlts (DataCon n _) alts =
  [a | a @ (Alt (DataAlt (DataCon n' _) _) _) <- alts, n == n']

-- | Match literal constructor based `Alt`s.
matchLitAlts :: Lit -> [Alt] -> [Alt]
matchLitAlts lit alts = [a | a @ (Alt (LitAlt alit) _) <- alts, lit == alit]

liftCaseBinds :: [(Id, Expr)] -> Expr -> Expr
liftCaseBinds [] expr = expr
liftCaseBinds ((b, e):xs) expr = liftCaseBinds xs $ replaceASTs (Var b) e expr

-- | `DataCon` `Alt`s.
dataAlts :: [Alt] -> [(DataCon, [Id], Expr)]
dataAlts alts = [(dcon, ps, aexpr) | Alt (DataAlt dcon ps) aexpr <- alts]

-- | `Lit` `Alt`s.
litAlts :: [Alt] -> [(Lit, Expr)]
litAlts alts = [(lit, aexpr) | Alt (LitAlt lit) aexpr <- alts]

-- | DEFAULT `Alt`s.
defaultAlts :: [Alt] -> [Alt]
defaultAlts alts = [a | a @ (Alt Default _) <- alts]

-- | Lift positive datacon `State`s from symbolic alt matching. This in
-- part involves erasing all of the parameters from the environment by rename
-- their occurrence in the aexpr to something fresh.
concretizeVarExpr :: State t -> NameGen -> Id -> Id -> [(DataCon, [Id], Expr)] -> Maybe Coercion -> ([NewPC t], NameGen)
concretizeVarExpr _ ng _ _ [] _ = ([], ng)
concretizeVarExpr s ng mexpr_id cvar (x:xs) maybeC = 
        (x':newPCs, ng'') 
    where
        (x', ng') = concretizeVarExpr' s ng mexpr_id cvar x maybeC
        (newPCs, ng'') = concretizeVarExpr s ng' mexpr_id cvar xs maybeC

concretizeVarExpr' :: State t -> NameGen -> Id -> Id -> (DataCon, [Id], Expr) -> Maybe Coercion -> (NewPC t, NameGen)
concretizeVarExpr' s@(State {expr_env = eenv, type_env = tenv, symbolic_ids = syms})
                ngen mexpr_id cvar (dcon, params, aexpr) maybeC = 
          (NewPC { state =  s { expr_env = eenv''
                              , symbolic_ids = syms'
                              , curr_expr = CurrExpr Evaluate aexpr''}
                 -- It is VERY important that we insert a PCExists with the mexpr_id
                 -- This forces reduceNewPC to check that the concretized data constructor does
                 -- not violate any path constraints from default cases. 
                 ,  new_pcs = [PCExists mexpr_id]
                 }, ngen')
  where
    -- Make sure that the parameters do not conflict in their symbolic reps.
    olds = map idName params

    -- [ChildrenNames]
    -- Optimization
    -- We use the same names repeatedly for the children of the same ADT
    -- Haskell is purely functional, so this is OK!  The children can't change
    -- Then, in the constraint solver, we can consider fewer constraints at once
    -- (see note [AltCond] in Language/PathConds.hs) 
    mexpr_n = idName mexpr_id
    (news, ngen') = childrenNames mexpr_n olds ngen

    --Update the expr environment
    newIds = map (\(Id _ t, n) -> (n, Id n t)) (zip params news)
    eenv' = foldr (uncurry E.insertSymbolic) eenv newIds

    (dcon', aexpr') = renameExprs (zip olds news) (Data dcon, aexpr)

    newparams = map (uncurry Id) $ zip news (map typeOf params)
    dConArgs = (map (Var) newparams)
    -- Get list of Types to concretize polymorphic data constructor and concatenate with other arguments
    mexpr_t = (\(Id _ t) -> t) (mexpr_id)
    exprs = [dcon'] ++ (mexprTyToExpr mexpr_t tenv) ++ dConArgs

    -- Apply list of types (if present) and DataCon children to DataCon
    dcon'' = mkApp exprs

    -- Apply cast, in opposite direction of unsafeElimOuterCast
    dcon''' = case maybeC of 
                (Just (t1 :~ t2)) -> Cast dcon'' (t2 :~ t1)
                Nothing -> dcon''

    syms' = HS.union (HS.fromList newparams) (HS.delete mexpr_id syms)

    -- concretizes the mexpr to have same form as the DataCon specified
    eenv'' = E.insert mexpr_n dcon''' eenv' 

    -- Now do a round of rename for binding the cvar.
    binds = [(cvar, (Var mexpr_id))]
    aexpr'' = liftCaseBinds binds aexpr'

    
-- | Given the Type of the matched Expr, looks for Type in the TypeEnv, and returns Expr level representation of the Type
mexprTyToExpr :: Type -> TypeEnv -> [Expr]
mexprTyToExpr mexpr_t tenv 
    -- special case for NewTyCon, involves looking up tyVars and binding them to concrete types specified by mexpr_t
    | Just (algDataTy, bindings) <- getAlgDataTy mexpr_t tenv     
    , (isNewTyCon algDataTy) = dconTyToExpr (data_con algDataTy) bindings
    | otherwise = typeToExpr mexpr_t

-- | Given a DataCon, and an (Id, Type) mapping, returns list of Expression level Type Arguments to DataCon
dconTyToExpr :: DataCon -> [(Id, Type)] -> [Expr]
dconTyToExpr (DataCon _ t) bindings =
    case (getTyApps t) of
        (Just tApps) -> tyAppsToExpr tApps bindings
        Nothing -> []

createExtConds :: State t -> NameGen -> Expr -> Id -> [(DataCon, [Id], Expr)] -> ([NewPC t], NameGen)
createExtConds _ ng _ _ [] = ([], ng)
createExtConds s ng mexpr cvar (x:xs) = 
        (x':newPCs, ng'') 
    where
        (x', ng') = createExtCond s ng mexpr cvar x
        (newPCs, ng'') = createExtConds s ng' mexpr cvar xs

createExtCond :: State t -> NameGen -> Expr -> Id -> (DataCon, [Id], Expr) -> (NewPC t, NameGen)
createExtCond s ngen mexpr cvar (dcon, _, aexpr) =
        (NewPC { state = res, new_pcs = [cond] }, ngen)
  where
    -- Get the Bool value specified by the matching DataCon
    -- Throws an error if dcon is not a Bool Data Constructor
    boolValue = getBoolFromDataCon (known_values s) (Data dcon)
    cond = ExtCond mexpr boolValue

    -- Now do a round of rename for binding the cvar.
    binds = [(cvar, mexpr)]
    aexpr' = liftCaseBinds binds aexpr
    res = s {curr_expr = CurrExpr Evaluate aexpr'}

liftSymLitAlt :: State t -> Expr -> Id -> [(Lit, Expr)] -> [NewPC t]
liftSymLitAlt s mexpr cvar = map (liftSymLitAlt' s mexpr cvar)

-- | Lift literal alts found in symbolic case matching.
liftSymLitAlt' :: State t -> Expr -> Id -> (Lit, Expr) -> NewPC t
liftSymLitAlt' s mexpr cvar (lit, aexpr) =
    NewPC { state = res, new_pcs = [cond] }
  where
    -- Condition that was matched.
    cond = AltCond lit mexpr True
    -- Bind the cvar.
    binds = [(cvar, Lit lit)]
    aexpr' = liftCaseBinds binds aexpr
    res = s { curr_expr = CurrExpr Evaluate aexpr' }

liftSymDefAlt :: State t -> Expr ->  Id -> [Alt] -> [NewPC t]
liftSymDefAlt s mexpr cvar as =
    let
        aexpr = defAltExpr as
    in
    case aexpr of
        Just aexpr' -> liftSymDefAlt' s mexpr aexpr' cvar as
        _ -> []

liftSymDefAlt' :: State t -> Expr -> Expr -> Id -> [Alt] -> [NewPC t]
liftSymDefAlt' s mexpr aexpr cvar as =
    let
        conds = mapMaybe (liftSymDefAltPCs mexpr) (map altMatch as)

        binds = [(cvar, mexpr)]
        aexpr' = liftCaseBinds binds aexpr
    in
    [NewPC { state = s { curr_expr = CurrExpr Evaluate aexpr' }
           , new_pcs = conds }]

defAltExpr :: [Alt] -> Maybe Expr
defAltExpr [] = Nothing
defAltExpr (Alt Default e:_) = Just e
defAltExpr (_:xs) = defAltExpr xs

liftSymDefAltPCs :: Expr -> AltMatch -> Maybe PathCond
liftSymDefAltPCs mexpr (DataAlt dc _) = Just $ ConsCond dc mexpr False
liftSymDefAltPCs mexpr (LitAlt lit) = Just $ AltCond lit mexpr False
liftSymDefAltPCs _ Default = Nothing

evalCast :: State t -> NameGen -> Expr -> Coercion -> (Rule, [State t], NameGen)
evalCast s@(State { exec_stack = stck }) 
         ng e c
    | cast /= cast' =
        ( RuleEvalCastSplit
        , [ s { curr_expr = CurrExpr Evaluate $ simplifyCasts cast' }]
        , ng')
    | otherwise =
        ( RuleEvalCast
        , [s { curr_expr = CurrExpr Evaluate $ simplifyCasts e
             , exec_stack = S.push frame stck}]
        , ng)
    where
        cast = Cast e c
        (cast', ng') = splitCast ng cast
        frame = CastFrame c

evalTick :: State t -> NameGen -> Tickish -> Expr -> (Rule, [State t], NameGen)
evalTick s ng _ e = (RuleTick, [ s { curr_expr = CurrExpr Evaluate e }], ng)

evalNonDet :: State t -> NameGen -> [Expr] -> (Rule, [State t], NameGen)
evalNonDet s ng es =
    let
        s' = map (\e -> s { curr_expr = CurrExpr Evaluate e }) es
    in
    (RuleNonDet, s', ng)

evalSymGen :: State t -> NameGen -> Type -> (Rule, [State t], NameGen)
evalSymGen s@( State { expr_env = eenv }) 
           ng t =
    let
          (n, ng') = freshSeededString "symG" ng
          i = Id n t

          eenv' = E.insertSymbolic n i eenv
    in
    (RuleSymGen, [s { expr_env = eenv'
                    , curr_expr = CurrExpr Evaluate (Var i)
                    , symbolic_ids = HS.insert i $ symbolic_ids s }]
                , ng')

evalAssume :: State t -> NameGen -> Maybe FuncCall -> Expr -> Expr -> (Rule, [State t], NameGen)
evalAssume s@(State { exec_stack = stck }) ng _ e1 e2 =
    let
        fr = AssumeFrame e2
        stck' = S.push fr stck
    in
    ( RuleEvalAssume
    , [ s { curr_expr = CurrExpr Evaluate e1
          , exec_stack = stck' }]
    , ng)

evalAssert :: State t -> NameGen -> Maybe FuncCall -> Expr -> Expr -> (Rule, [State t], NameGen)
evalAssert s@(State { exec_stack = stck }) ng is e1 e2 =
    let
        fr = AssertFrame is e2
        stck' = S.push fr stck
    in
    ( RuleEvalAssert
    , [ s { curr_expr = CurrExpr Evaluate e1
          , exec_stack = stck' }]
    , ng)

retUpdateFrame :: State t -> NameGen -> Name -> S.Stack Frame -> (Rule, [State t], NameGen)
retUpdateFrame s@(State { expr_env = eenv
                        , curr_expr = CurrExpr _ e}) ng un stck
    | Var i@(Id vn _) <- e =
       ( RuleReturnEUpdateVar un
       , [s { expr_env = E.redirect un vn eenv
            , curr_expr = CurrExpr Return (Var i)
            , exec_stack = stck }]
       , ng)
    | otherwise =
        ( RuleReturnEUpdateNonVar un
        , [s { expr_env = E.insert un e eenv
             , exec_stack = stck }]
        , ng)

retApplyFrame :: State t -> NameGen -> Expr -> Expr -> S.Stack Frame -> (Rule, [State t], NameGen)
retApplyFrame s@(State { expr_env = eenv }) ng e1 e2 stck'
    | Var (Id n _):_ <- unApp e1
    , E.isSymbolic n eenv = 
        ( RuleReturnEApplySym
        , [s { curr_expr = CurrExpr Return (App e1 e2)
             , exec_stack = stck' }], ng)
    | otherwise =
        ( RuleReturnEApplySym
        , [s { curr_expr = CurrExpr Evaluate (App e1 e2)
             , exec_stack = stck' }], ng)

retCaseFrame :: State t -> NameGen -> Expr -> Id -> [Alt] -> S.Stack Frame -> (Rule, [State t], NameGen)
retCaseFrame s b e i a stck =
    ( RuleReturnECase
    , [s { curr_expr = CurrExpr Evaluate (Case e i a)
         , exec_stack = stck }]
    , b)

retCastFrame :: State t -> NameGen -> Expr -> Coercion -> S.Stack Frame -> (Rule, [State t], NameGen)
retCastFrame s ng e c stck =
    ( RuleReturnCast
    , [s { curr_expr = CurrExpr Return $ simplifyCasts $ Cast e c
         , exec_stack = stck}]
    , ng)

retCurrExpr :: State t -> Expr -> CurrExpr -> S.Stack Frame -> (Rule, [NewPC t])
retCurrExpr s e1 e2 stck = 
    ( RuleReturnCurrExprFr
    , [NewPC { state = s { curr_expr = e2
                         , exec_stack = stck}
             , new_pcs = [ExtCond e1 True]}] )

retAssumeFrame :: State t -> NameGen -> Expr -> Expr -> S.Stack Frame -> (Rule, [NewPC t], NameGen)
retAssumeFrame s@(State {known_values = kv
                        , type_env = tenv}) 
               ng e1 e2 stck =
    let
        -- Create a True Bool DataCon
        dalt = case (getDataCon tenv (KV.tyBool kv) (KV.dcTrue kv)) of
            Just dc -> [dc]
            _ -> []
        -- If Assume is just a Var, concretize the Expr to a True Bool DataCon. Else add an ExtCond
        (newPCs, ng') = case unApp $ unsafeElimOuterCast e1 of
            (Var i@(Id _ _)):_ -> concretizeExprToBool s ng i dalt e2 stck
            _ -> addExtCond s ng e1 e2 True stck
    in
    (RuleReturnCAssume, newPCs, ng')

retAssertFrame :: State t -> NameGen -> Expr -> Maybe (FuncCall) -> Expr -> S.Stack Frame -> (Rule, [NewPC t], NameGen)
retAssertFrame s@(State {known_values = kv
                        , type_env = tenv}) 
               ng e1 ais e2 stck =
    let
        -- Create True and False Bool DataCons
        dalts = case getDataCons (KV.tyBool kv) tenv of
            Just dcs -> dcs
            _ -> []
        -- If Assert is just a Var, concretize the Expr to a True or False Bool DataCon, else add an ExtCond
        (newPCs, ng') = case unApp $ unsafeElimOuterCast e1 of
            (Var i@(Id _ _)):_ -> concretizeExprToBool s ng i dalts e2 stck
            _ -> addExtConds s ng e1 ais e2 stck
            
      in
      (RuleReturnCAssert, newPCs, ng')

concretizeExprToBool :: State t -> NameGen -> Id -> [DataCon] -> Expr -> S.Stack Frame -> ([NewPC t], NameGen)
concretizeExprToBool _ ng _ [] _ _ = ([], ng)
concretizeExprToBool s ng mexpr_id (x:xs) e2 stck = 
        (x':newPCs, ng'') 
    where
        (x', ng') = concretizeExprToBool' s ng mexpr_id x e2 stck
        (newPCs, ng'') = concretizeExprToBool s ng' mexpr_id xs e2 stck

concretizeExprToBool' :: State t -> NameGen -> Id -> DataCon -> Expr -> S.Stack Frame -> (NewPC t, NameGen)
concretizeExprToBool' s@(State {expr_env = eenv
                        , symbolic_ids = syms
                        , known_values = kv})
                ngen mexpr_id dcon@(DataCon dconName _) e2 stck = 
        (newPCEmpty $ s { expr_env = eenv'
                        , symbolic_ids = syms'
                        , exec_stack = stck
                        , curr_expr = CurrExpr Evaluate e2
                        , true_assert = assertVal}
                        , ngen)
    where
        mexpr_n = idName mexpr_id

        -- concretize the mexpr to the DataCon specified
        eenv' = E.insert mexpr_n (Data dcon) eenv
        syms' = HS.delete mexpr_id syms

        assertVal = if (dconName == (KV.dcTrue kv))
                        then False
                        else True

addExtCond :: State t -> NameGen -> Expr -> Expr -> Bool -> S.Stack Frame -> ([NewPC t], NameGen)
addExtCond s ng e1 e2 boolVal stck = 
    ([NewPC { state = s { curr_expr = CurrExpr Evaluate e2
                         , exec_stack = stck}
             , new_pcs = [ExtCond e1 boolVal]}], ng)

addExtConds :: State t -> NameGen -> Expr -> Maybe (FuncCall) -> Expr -> S.Stack Frame -> ([NewPC t], NameGen)
addExtConds s ng e1 ais e2 stck =
    let
        s' = s { curr_expr = CurrExpr Evaluate e2
               , exec_stack = stck}

        condt = [ExtCond e1 True]
        condf = [ExtCond e1 False]

        strue = NewPC { state = s'
                      , new_pcs = condt }

        sfalse = NewPC { state = s' { true_assert = True
                                    , assert_ids = ais }
                       , new_pcs = condf }
    in
    ([strue, sfalse], ng)

-- | Inject binds into the eenv. The LHS of the [(Id, Expr)] are treated as
-- seed values for the names.
liftBinds :: [(Id, Expr)] -> E.ExprEnv -> Expr -> NameGen ->
             (E.ExprEnv, Expr, NameGen, [Name])
liftBinds binds eenv expr ngen = (eenv', expr', ngen', news)
  where
    (bindsLHS, bindsRHS) = unzip binds

    olds = map (idName) bindsLHS
    (news, ngen') = freshSeededNames olds ngen
    expr' = renameExprs (zip olds news) expr
    bindsLHS' = renameExprs (zip olds news) bindsLHS

    binds' = zip bindsLHS' bindsRHS

    eenv' = E.insertExprs (zip news (map snd binds')) eenv

-- If the expression is a symbolic higher order function application, replaces
-- it with a symbolic variable of the correct type.
-- A non reduced path constraint is added, to force solving for the symbolic
-- function later.
retReplaceSymbFunc :: State t -> NameGen -> Expr -> Maybe (Rule, [State t], NameGen)
retReplaceSymbFunc s@(State { expr_env = eenv
                            , known_values = kv
                            , type_classes = tc
                            , exec_stack = stck })
                   ng ce
    | Just (frm, _) <- S.pop stck
    , not (isApplyFrame frm)
    , (Var (Id f idt):_) <- unApp ce
    , E.isSymbolic f eenv
    , isTyFun idt
    , t <- typeOf ce
    , not (isTyFun t)
    , Just eq_tc <- concreteSatStructEq kv tc t =
        let
            (new_sym, ng') = freshSeededString "sym" ng
            new_sym_id = Id new_sym t

            s_eq_f = KV.structEqFunc kv

            nrpc_e = mkApp $ 
                           [ Var (Id s_eq_f TyUnknown)
                           , Type t
                           , eq_tc
                           , Var new_sym_id
                           , ce ]
        in
        Just (RuleReturnReplaceSymbFunc, 
            [s { expr_env = E.insertSymbolic new_sym new_sym_id eenv
               , curr_expr = CurrExpr Return (Var new_sym_id)
               , symbolic_ids = HS.insert new_sym_id $ symbolic_ids s
               , non_red_path_conds = non_red_path_conds s ++ [nrpc_e] }]
            , ng')
    | otherwise = Nothing

isApplyFrame :: Frame -> Bool
isApplyFrame (ApplyFrame _) = True
isApplyFrame _ = False


