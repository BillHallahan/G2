-- | Reduction Rules for Stack Execution Semantics
module G2.Internals.Execution.Rules
  ( Rule (..)
  , isExecValueForm
  , stackReduce
  ) where

import G2.Internals.Language
import G2.Internals.Language.Stack
import qualified G2.Internals.Language.ExprEnv as E

import Data.List

data Rule = RuleEvalVal
          | RuleEvalVarNonVal | RuleEvalVarVal
          | RuleEvalUnInt
          | RuleEvalApp
          | RuleEvalLet
          | RuleEvalCaseData | RuleEvalCaseLit | RuleEvalCaseDefault
                             | RuleCaseSym | RuleEvalCaseNonVal

          | RuleReturnUpdateVar | RuleReturnUpdateNonVar
          | RuleReturnCase
          | RuleReturnApplyLam | RuleReturnApplyData
                                  | RuleReturnApplySym

          | RuleIdentity

          | RuleError
           deriving (Show, Eq, Read)

-- | Check whether or not a value is the result of symbolic application. This
-- would require us to go through a chain of things to make sure that the LHS
-- of the sequence of Apps is mapped to a Nothing -- effectively a normal form.
isSymbolic :: Id -> E.ExprEnv -> Bool
isSymbolic var eenv = case E.lookup (idName var) eenv of
    Just (App (Var fvar) _) -> isSymbolic fvar eenv
    Just _ -> False
    Nothing -> True

-- | Unravels the application spine.
unApp :: Expr -> [Expr]
unApp (App f a) = unApp f ++ [a]
unApp expr = [expr]

-- | If something is in "value form", then it is essentially ready to be
-- returned and popped off the heap. This will be the SSTG equivalent of having
-- Return vs Evaluate for the ExecCode of the `State`.
--
-- So in this context, the following are considered NOT-value forms:
--   `Var`, only if a lookup still available in the expression environment.
--   `App`, which involves pushing the RHS onto the `Stack`.
--   `Let`, which involves binding the binds into the eenv
--   `Case`, which involves pattern decomposition and stuff.
isExprValueForm :: Expr -> E.ExprEnv -> Bool
isExprValueForm (Var var) eenv =
    E.lookup (idName var) eenv == Nothing || isSymbolic var eenv
isExprValueForm (App f a) _ = case unApp (App f a) of
    (Data _:_) -> True
    _ -> False
isExprValueForm (Let _ _) _ = False
isExprValueForm (Case _ _ _) _ = False
isExprValueForm _ _ = True

-- | Is the execution state in a value form of some sort? This would entail:
-- * The `Stack` is empty.
-- * The `ExecCode` is in a `Return` form.
isExecValueForm :: State -> Bool
isExecValueForm state | Nothing <- pop (stack state)
                      , CurrExpr Return _ <- curr_expr state = True

                      | otherwise = False

-- | Rename multiple things at once with [(olds, news)] on a `Renameable`.
renamings :: Renamable a => [(Name, Name)] -> a -> a
renamings names a = foldr (\(old, new) -> renaming old new) a names

-- | Inject binds into the eenv. The LHS of the [(Id, Expr)] are treated as
-- seed values for the names.
liftBinds :: [(Id, Expr)] -> E.ExprEnv -> Expr -> NameGen ->
           (E.ExprEnv, Expr, NameGen)
liftBinds kvs eenv expr ngen = (eenv', expr', ngen')
  where
    olds = map (idName . fst) kvs
    (news, ngen') = freshSeededNames olds ngen
    eenv' = E.insertExprs (zip news (map snd kvs)) eenv
    expr' = renamings (zip olds news) expr

-- | `DataCon` `Alt`s.
dataAlts :: [Alt] -> [(DataCon, [Id], Expr)]
dataAlts alts = [(dcon, ps, aexpr) | Alt (DataAlt dcon ps) aexpr <- alts]

-- | `Lit` `Alt`s.
litAlts :: [Alt] -> [(Lit, Expr)]
litAlts alts = [(lit, aexpr) | Alt (LitAlt lit) aexpr <- alts]

-- | DEFAULT `Alt`s.
defaultAlts :: [Alt] -> [Alt]
defaultAlts alts = [a | a @ (Alt Default _) <- alts]

-- | Match data constructor based `Alt`s.
matchDataAlts :: DataCon -> [Alt] -> [Alt]
matchDataAlts dc alts = [a | a @ (Alt (DataAlt adc _) _) <- alts , dc == adc]

-- | Match literal constructor based `Alt`s.
matchLitAlts :: Lit -> [Alt] -> [Alt]
matchLitAlts lit alts = [a | a @ (Alt (LitAlt alit) _) <- alts, lit == alit]

-- | Negate an `PathCond`.
negatePathCond :: PathCond -> PathCond
negatePathCond (AltCond a e b) = AltCond a e (not b)
negatePathCond (ExtCond e b) = ExtCond e (not b)

-- | Lift positive datacon `State`s from symbolic alt matching. This in
-- part involves erasing all of the parameters from the environment by renaming
-- their occurrence in the aexpr to something fresh.
liftSymDataAlt :: E.ExprEnv -> Expr -> NameGen -> (DataCon, [Id], Expr) -> Id ->
                  (E.ExprEnv, CurrExpr, [PathCond], NameGen, Maybe Frame)
liftSymDataAlt eenv mexpr ng (dcon, params, aexpr) cvar = ret
  where
    -- Condition that was matched.
    cond = AltCond (DataAlt dcon params) mexpr True
    -- Make sure that the parameters do not conflict in their symbolic reps.
    olds = map idName params
    (aexpr', ng') = rename' olds ng aexpr
    -- Now do a round of renaming for binding the cvar.
    binds = [(cvar, mexpr)]
    (eenv', aexpr'', ngen'') = liftBinds binds eenv aexpr' ng'
    ret = ( eenv'
          , CurrExpr Evaluate aexpr''
          , [cond]
          , ngen''
          , Nothing)

-- | Lift literal alts found in symbolic case matching.
liftSymLitAlt :: E.ExprEnv -> Expr -> NameGen -> (Lit, Expr) -> Id ->
                 (E.ExprEnv, CurrExpr, [PathCond], NameGen, Maybe Frame)
liftSymLitAlt eenv mexpr ng (lit, aexpr) cvar = ret
  where
    -- Condition that was matched.
    cond = AltCond (LitAlt lit) mexpr True
    -- Bind the cvar.
    binds = [(cvar, Lit lit)]
    (eenv', aexpr', ng') = liftBinds binds eenv aexpr ng
    ret = ( eenv'
          , CurrExpr Evaluate aexpr'
          , [cond]
          , ng'
          , Nothing)

-- | Lift default alts found in symbolic case matching.
liftSymDefAlt :: E.ExprEnv -> Expr -> NameGen -> [PathCond] -> Expr -> Id ->
                 (E.ExprEnv, CurrExpr, [PathCond], NameGen, Maybe Frame)
liftSymDefAlt eenv mexpr ng negatives aexpr cvar = ret
  where
    -- Bind the cvar.
    binds = [(cvar, mexpr)]
    (eenv', aexpr', ng') = liftBinds binds eenv aexpr ng
    ret = (eenv
          , CurrExpr Evaluate aexpr'
          , negatives
          , ng'
          , Nothing)

-- | Funciton for performing rule reductions based on stack based evaluation
-- semantics with heap memoization.

-- The semantics differ a bit from SSTG a bit, namely in what is and is not
-- returned from the heap. In SSTG, you return either literals or pointers.
-- The distinction is less clear here. For now :)

stackReduce :: State -> (Rule, [State])
stackReduce s @ State { stack = stack
                      , expr_env = eenv
                      , curr_expr = cexpr
                      , name_gen = ng
                      , path_conds = paths }
    | isExecValueForm s =
        (RuleIdentity, [s])
    
    | CurrExpr Evaluate expr <- cexpr 
    , isExprValueForm expr eenv =
        -- Our current thing is a value form, which means we can return it.
        (RuleEvalVal, [s { curr_expr = CurrExpr Return expr }])
    
    | CurrExpr Evaluate expr <- cexpr =
        let
            (r, new) = srEvaluate eenv expr ng
        in
        (r, map (\(eenv', cexpr', paths', ng', f) ->
                    s { expr_env = eenv'
                      , curr_expr = cexpr'
                      , path_conds = paths' ++ paths
                      , name_gen = ng'
                      , stack = maybe stack (\f' -> push f' stack) f}) new)
    | CurrExpr Return expr <- cexpr
    , Just (f, stack') <- pop stack =
        let
            (r, eenv', cexpr', ng') = srReturn eenv expr ng f
        in
        (r, [s {
                 expr_env = eenv'
               , curr_expr = cexpr'
               , name_gen = ng'
               , stack = stack'
               }])
    
    | otherwise = (RuleError, [s])

-- The semantics differ a bit from SSTG a bit, namely in what is and is not
-- returned from the heap. In SSTG, you return either literals or pointers.
-- The distinction is less clear here. For now :)
srEvaluate :: E.ExprEnv -> Expr -> NameGen -> (Rule, [(E.ExprEnv, CurrExpr, [PathCond], NameGen, Maybe Frame)])
srEvaluate eenv (Var var) ng =
    case E.lookup (idName var) eenv of
        Just expr ->
            if isExprValueForm expr eenv then
                -- If the target in our environment is already a value form, we do not
                -- need to push additional redirects for updating later on.
                (RuleEvalVarVal
                , [(eenv
                , CurrExpr Evaluate expr
                , []
                , ng
                , Nothing)])
            else
                -- If our variable points to something on the heap, we first push the
                -- current name of the variable onto the stack and evaluate the expression
                -- that it points to only if it is not a value. After the latter is done
                -- evaluating, we pop the stack to add a redirection pointer into the heap.
                let
                    frame = UpdateFrame (idName var)
                in
                ( RuleEvalVarNonVal
                , [(eenv
                , CurrExpr Evaluate expr
                , []
                , ng
                , Just frame)])
        Nothing -> error "Lookup was Nothing"
srEvaluate eenv (App fexpr aexpr) ng =
    -- Push application RHS onto the stack. This is essentially the same as the
    -- original STG rules, but we pretend that every function is (appropriately)
    -- single argument. However one problem is that eenv sharing has a redundant
    -- representation because long `App` chains will all share the same eenv.
    -- However given actual lazy evaluations within Haskell, all the
    -- `ExecExprEnv`s at each frame would really be stored in a single
    -- location on the actual Haskell heap during execution.
    let
        frame = ApplyFrame aexpr
    in 
    ( RuleEvalApp
    , [(eenv
    , CurrExpr Evaluate fexpr
    , []
    , ng
    , Just frame)])
srEvaluate eenv (Let binds expr) ng =
    -- Lift all the let bindings into the environment and continue with eenv
    -- and continue with evaluation of the let expression.
    let
        (eenv', expr', ng') = liftBinds binds eenv expr ng
    in
    ( RuleEvalLet
    , [(eenv'
    , CurrExpr Evaluate expr'
    , []
    , ng'
    , Nothing)])
srEvaluate eenv (Case mexpr cvar alts) ng =
    srEvaluateCase eenv mexpr cvar alts ng
srEvaluate eenv c ng =
    (RuleError, [(eenv, CurrExpr Evaluate c, [], ng, Nothing)])

srEvaluateCase ::
    E.ExprEnv -> Expr -> Id -> [Alt] -> NameGen
            -> (Rule, [(E.ExprEnv, CurrExpr, [PathCond], NameGen, Maybe Frame)])
srEvaluateCase eenv mexpr bind alts ng
    | (Lit lit) <- mexpr
    , (Alt (LitAlt _) expr):_ <- matchLitAlts lit alts =
        -- | Is the current expression able to match with a literal based `Alt`? If
        -- so, we do the cvar binding, and proceed with evaluation of the body.
        let
            binds = [(bind, Lit lit)]
            (eenv', expr', ng') = liftBinds binds eenv expr ng
        in 
        ( RuleEvalCaseLit
        , [(eenv'
        , CurrExpr Evaluate expr'
        , []
        , ng'
        , Nothing)])

    | (Data dcon):args <- unApp mexpr
    , (Alt (DataAlt _ params) expr):_ <- matchDataAlts dcon alts
    , length params == length args =
        -- Is the current expression able to match a data consturctor based `Alt`?
        -- If so, then we bind all the parameters to the appropriate arguments and
        -- proceed with the evaluation of the `Alt`'s expression. We also make sure
        -- to perform the cvar binding.
        let
            binds = (bind, mexpr) : zip params args
            (eenv', expr', ng') = liftBinds binds eenv expr ng
        in
        ( RuleEvalCaseData
        , [(eenv'
        , CurrExpr Evaluate expr'
        , []
        , ng'
        , Nothing)] )

    | (Alt _ expr):_ <- defaultAlts alts =
        -- | We are not able to match any of the stuff, and hit a DEFAULT instead?
        -- If so, we just perform the cvar binding and proceed with the alt
        -- expression.
        let
            binds = [(bind, mexpr)]
            (eenv', expr', ng') = liftBinds binds eenv expr ng
        in
        ( RuleEvalCaseDefault
        , [(eenv'
        , CurrExpr Evaluate expr'
        , []
        , ng'
        , Nothing)])

    | (Var var) <- mexpr
    , isSymbolic var eenv
    , (dalts, lalts, defs) <- (dataAlts alts, litAlts alts, defaultAlts alts)
    , (length dalts + length lalts + length defs) > 0 =
        -- | If we are pointing to a symbolic value in the environment, handle it
        -- appropriately by branching on every `Alt`.
        let 
            dsts_cs = map (\d -> liftSymDataAlt eenv (Var var) ng d bind) dalts
            lsts_cs = map (\l -> liftSymLitAlt eenv (Var var) ng l bind) lalts
            (_, _, dconds, _, _) = unzip5 dsts_cs
            (_, _, lconds, _, _) = unzip5 lsts_cs
            negs = map (negatePathCond) $ concat (dconds ++ lconds)
            def_sts = map (\(Alt _ aexpr) ->
                           liftSymDefAlt eenv (Var var) ng negs aexpr bind) defs
        in
        (RuleCaseSym, dsts_cs ++ lsts_cs ++ def_sts)

    | not (isExprValueForm mexpr eenv) =
        -- Case evaluation also uses the stack in graph reduction based evaluation
        -- semantics. The case's binding variable and alts are pushed onto the stack
        -- as a `CaseFrame` along with their appropriate `ExecExprEnv`. However this
        -- is only done when the matching expression is NOT in value form. Value
        -- forms should be handled by other RuleEvalCase* rules.
        let
            frame = CaseFrame bind alts
        in
        ( RuleEvalCaseNonVal
        , [(eenv
        , CurrExpr Evaluate mexpr
        , []
        , ng
        , Just frame)])

srReturn :: E.ExprEnv -> Expr -> NameGen -> Frame -> (Rule, E.ExprEnv, CurrExpr, NameGen)
srReturn eenv (Var (Id name ty)) ng (UpdateFrame frm_name) =
    -- We are returning something and the first thing that we have on the stack
    -- is an `UpdateFrame`, this means that we add a redirection pointer to the
    -- `ExecExprEnv`, and continue with execution. This is the equivalent of
    -- performing memoization on values that we have seen.
    ( RuleReturnUpdateVar
    , E.redirect frm_name name eenv
    , CurrExpr Return (Var $ Id name ty)
    , ng)

srReturn eenv expr ng (UpdateFrame frm_name) =
    -- If the variable we are returning does not have a `Var` in it at the
    -- immediate top level, then we have to insert it into the `ExecExprEnv`
    -- directly.
        ( RuleReturnUpdateNonVar
        , E.insert frm_name expr eenv
        , CurrExpr Return expr
        , ng)
srReturn eenv expr ng (CaseFrame cvar alts) =
    -- In the event that we are returning and we have a `CaseFrame` waiting for
    -- us at the top of the stack, we would simply inject it into the case
    -- expression. We do some assumptions here about the form of expressions!
    ( RuleReturnCase
    , eenv
    , CurrExpr Evaluate (Case expr cvar alts)
    , ng)
srReturn eenv (Lam b lexpr) ng (ApplyFrame aexpr) =
    -- When we have an `ApplyFrame` on the top of the stack, things might get a
    -- bit tricky, since we need to make sure that the thing we end up returning
    -- is appropriately a value. In the case of `Lam`, we need to perform
    -- application, and then go into the expression body.
    let binds = [(b, aexpr)]
        (eenv', lexpr', ng') = liftBinds binds eenv lexpr ng
    in 
    ( RuleReturnApplyLam
    , eenv'
    , CurrExpr Evaluate lexpr'
    , ng')
srReturn eenv dexpr@(App (Data _) _) ng (ApplyFrame aexpr) =
    -- When we have an `DataCon` application chain, we need to tack on the
    -- expression in the `ApplyFrame` at the end.
    ( RuleReturnApplyData
    , eenv
    , CurrExpr Return (App dexpr aexpr)
    , ng)
srReturn eenv c@(Var var) ng (ApplyFrame aexpr)=
    -- When we return symbolic values on an `ApplyFrame`, introduce new name
    -- mappings in the eenv to form this long symbolic normal form chain.
    if isSymbolic var eenv then
        let 
            (sname, ngen') = freshSeededName (idName var) ng
            sym_app = App (Var var) aexpr
            svar = Id sname (TyApp (typeOf var) (typeOf aexpr))
        in 
        ( RuleReturnApplySym
        , E.insert sname sym_app eenv
        , CurrExpr Return (Var svar)
        , ngen') 
    else
        (RuleError, eenv, CurrExpr Return c, ng)
srReturn eenv c ng f = (RuleError, eenv, CurrExpr Return c, ng)