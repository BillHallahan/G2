{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}

module G2.Equiv.G2Calls ( StateET
                        , EquivTracker (..)
                        , BlockInfo (..)
                        , emptyEquivTracker
                        , runG2ForNebula
                        , totalExpr
                        , argCount
                        , concretizable

                        , isLabeledErrorName
                        , labeledErrorName
                        , isLabeledError

                        , lookupBoth
                        , isSymbolicBoth ) where

import G2.Config
import G2.Execution
import G2.Interface
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Stack as S
import qualified G2.Language.Typing as TY
import G2.Solver
import G2.Equiv.Config

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS

import qualified Data.Text as T

import Data.Hashable
import qualified Data.List as L

import GHC.Generics (Generic)

-- get names from symbolic ids in the state
runG2ForNebula :: Solver solver =>
                    solver ->
                    StateET ->
                    E.ExprEnv ->
                    EquivTracker ->
                    Config ->
                    NebulaConfig ->
                    Bindings ->
                    IO ([ExecRes EquivTracker], Bindings)
runG2ForNebula solver state h_opp track_opp config nc bindings = do
    --SomeSolver solver <- initSolver config
    let simplifier = IdSimplifier
        sym_config = PreserveAllMC
        {-
        sym_config = addSearchNames (namesList $ track state)
                   $ addSearchNames (input_names bindings)
                   $ addSearchNames (M.keys $ deepseq_walkers bindings) emptyMemConfig
        -}

        state' = state { track = (track state) { saw_tick = Nothing } }

    (in_out, bindings') <- case rewriteRedHaltOrd solver simplifier h_opp track_opp config nc of
                (red, hal, ord) ->
                    runG2WithSomes red hal ord solver simplifier sym_config state' bindings

    --close solver

    return (in_out, bindings')

rewriteRedHaltOrd :: (Solver solver, Simplifier simplifier) =>
                     solver ->
                     simplifier ->
                     E.ExprEnv ->
                     EquivTracker ->
                     Config ->
                     NebulaConfig ->
                     (SomeReducer EquivTracker, SomeHalter EquivTracker, SomeOrderer EquivTracker)
rewriteRedHaltOrd solver simplifier h_opp track_opp config (NC { use_labeled_errors = use_labels }) =
    let
        share = sharing config
        state_name = Name "state" Nothing 0 Nothing

        m_logger = getLogger config
    in
    (case m_logger of
            Just logger -> SomeReducer (
                                (StdRed share solver simplifier :<~?
                                        EnforceProgressR) :<~? LabeledErrorsR :<~ ConcSymReducer use_labels :<~ SymbolicSwapper h_opp track_opp) <~?
                                        (logger <~ SomeReducer EquivReducer)
            Nothing -> SomeReducer (
                                ((StdRed share solver simplifier :<~?
                                    EnforceProgressR) :<~? LabeledErrorsR :<~ ConcSymReducer use_labels :<~ SymbolicSwapper h_opp track_opp) :<~?
                                    EquivReducer)
     , SomeHalter
         (DiscardIfAcceptedTag state_name
         :<~> EnforceProgressH
         :<~> SWHNFHalter
         :<~> LabeledErrorsH)
     , SomeOrderer $ PickLeastUsedOrderer)

type StateET = State EquivTracker

data ConcSymReducer = ConcSymReducer UseLabeledErrors

data BlockInfo = BlockDC DataCon Int Int
               | BlockLam Id
               deriving (Show, Eq, Generic)

instance Hashable BlockInfo

-- Maps higher order function calls to symbolic replacements.
-- This allows the same call to be replaced by the same Id consistently.
-- relocated from Equiv.G2Calls
-- TODO dormant is 0 if execution can happen now
-- at what point do dormant values get assigned?
-- EquivTracker probably the wrong level for handling this
data EquivTracker = EquivTracker { higher_order :: HM.HashMap Expr Id
                                 , saw_tick :: Maybe Int
                                 , total_vars :: HS.HashSet Name
                                 , finite_vars :: HS.HashSet Name
                                 , dc_path :: [BlockInfo]
                                 , opp_env :: ExprEnv
                                 , folder_name :: String } deriving (Show, Eq, Generic)

instance Hashable EquivTracker

-- Forces a lone symbolic variable with a type corresponding to an ADT
-- to evaluate to some value of that ADT
instance Reducer ConcSymReducer () EquivTracker where
    initReducer _ _ = ()

    redRules red@(ConcSymReducer use_labels) _
                   s@(State { curr_expr = CurrExpr _ (Var (Id n t))
                            , expr_env = eenv
                            , type_env = tenv
                            , track = EquivTracker et m total finite dcp opp fname })
                   b@(Bindings { name_gen = ng })
        | E.isSymbolic n eenv
        , Just (dc_symbs, ng') <- arbDC use_labels tenv ng t n total = do
            let new_names = map idName $ concat $ map snd dc_symbs
                total' = if n `elem` total
                         then foldr HS.insert total new_names
                         else total
                -- finiteness carries over to sub-expressions too
                finite' = if n `elem` finite
                          then foldr HS.insert finite new_names
                          else finite
                xs = map (\(e, symbs') ->
                                s   { curr_expr = CurrExpr Evaluate e
                                    , expr_env =
                                        foldr E.insertSymbolic
                                              (E.insert n e eenv)
                                              symbs'
                                    , track = EquivTracker et m total' finite' dcp opp fname
                                    }) dc_symbs
                b' =  b { name_gen = ng' }
                -- only add to total if n was total
                -- not all of these will be used on each branch
                -- they're all fresh, though, so overlap is not a problem
            return (InProgress, zip xs (repeat ()) , b', red)
    redRules red _ s b = return (NoProgress, [(s, ())], b, red)

-- | Build a case expression with one alt for each data constructor of the given type
-- and symbolic arguments.  Thus, the case expression could evaluate to any value of the
-- given type.
arbDC :: UseLabeledErrors
      -> TypeEnv
      -> NameGen
      -> Type
      -> Name
      -> HS.HashSet Name
      -> Maybe ([(Expr, [Id])], NameGen)
arbDC use_labels tenv ng t n total
    | TyCon tn _:ts <- unTyApp t
    , Just adt <- HM.lookup tn tenv =
        let
            dcs = dataCon adt

            bound = boundIds adt
            bound_ts = zip bound ts

            (err_lab, ng') = freshLabeledError ng
            err = if use_labels == UseLabeledErrors
                      then Tick (NamedLoc err_lab) (Prim Error TyBottom)
                      else Prim Error TyBottom

            ty_apped_dcs = map (\dc -> mkApp $ Data dc:map Type ts) dcs
            ty_apped_dcs' = err:ty_apped_dcs
            (ng'', dc_symbs) = 
                L.mapAccumL
                    (\ng_ dc ->
                        let
                            anon_ts = anonArgumentTypes dc
                            re_anon = foldr (\(i, ty) -> retype i ty) anon_ts bound_ts
                            (ars, ng_') = freshIds re_anon ng_
                        in
                        (ng_', (mkApp $ dc:map Var ars, ars))
                    )
                    ng'
                    (if n `elem` total then ty_apped_dcs else ty_apped_dcs')
        in
        Just (dc_symbs, ng'')
    | otherwise = Nothing

data SymbolicSwapper = SymbolicSwapper E.ExprEnv EquivTracker

instance Reducer SymbolicSwapper () EquivTracker where
    initReducer _ _ = ()
    redRules r@(SymbolicSwapper h_opp track_opp) rv
                  s@(State { curr_expr = CurrExpr _ e
                           , expr_env = h
                           , track = EquivTracker et m tot fin dcp opp fname })
                  b =
        case e of
            Var (Id n _) | E.isSymbolic n h ->
                case E.lookupConcOrSym n h_opp of
                    Just (E.Conc e') ->
                        let vi = varIds e'
                            vi_hs = HS.fromList $ map idName vi
                            h' = foldr (\j -> E.insertSymbolic j) (E.insert n e' h) (L.nub vi)
                            total' = HS.union (HS.intersection (total_vars track_opp) vi_hs) tot
                            finite' = HS.union (HS.intersection (finite_vars track_opp) vi_hs) fin
                            track' = EquivTracker et m total' finite' dcp opp fname
                            s' = s {
                              expr_env = h'
                            , track = track'
                            }
                        in return (InProgress, [(s', rv)], b, r)
                    _ -> return (NoProgress, [(s, rv)], b, r)
            _ -> return (NoProgress, [(s, rv)], b, r)

data EnforceProgressR = EnforceProgressR

data EnforceProgressH = EnforceProgressH

instance Reducer EnforceProgressR () EquivTracker where
    initReducer _ _ = ()
    redRules r rv s@(State { curr_expr = CurrExpr _ e
                           , num_steps = n
                           , track = EquivTracker et m total finite dcp opp fname })
                  b =
        let s' = s { track = EquivTracker et (Just n) total finite dcp opp fname }
        in
        case (e, m) of
            (Tick (NamedLoc (Name p _ _ _)) _, Nothing) ->
                if p == T.pack "STACK"
                then return (InProgress, [(s', ())], b, r)
                else return (NoProgress, [(s, ())], b, r)
            -- TODO condense these into one case?
            -- then again, it might not matter at all here
            (Tick (NamedLoc (Name p _ _ _)) _, Just n0) ->
                if p == T.pack "STACK" && n > n0 + 1
                then return (InProgress, [(s', ())], b, r)
                else return (NoProgress, [(s, ())], b, r)
            _ -> return (NoProgress, [(s, rv)], b, r)

labeledErrorStringSeed :: T.Text
labeledErrorStringSeed = "__ERROR_LABEL__"

labeledErrorNameSeed :: Name
labeledErrorNameSeed = Name "__ERROR_LABEL__" Nothing 0 Nothing

isLabeledErrorName :: Name -> Bool
isLabeledErrorName (Name n _ _ _) = n == labeledErrorStringSeed

labeledErrorName :: Tickish -> Maybe Name
labeledErrorName (NamedLoc n) | isLabeledErrorName n = Just n
labeledErrorName _ = Nothing

freshLabeledError :: NameGen -> (Name, NameGen)
freshLabeledError = freshSeededName labeledErrorNameSeed

isLabeledError :: Expr -> Bool
isLabeledError (Tick (NamedLoc n) (Prim Error _)) = isLabeledErrorName n
isLabeledError (Tick (NamedLoc n) (Prim Undefined _)) = isLabeledErrorName n
isLabeledError _ = False

data LabeledErrorsR = LabeledErrorsR

instance Reducer LabeledErrorsR () t where
    initReducer _ _ = ()
    redRules r rv s@(State { curr_expr = CurrExpr _ ce }) b
        | isLabeledError ce = return (Finished, [(s { exec_stack = S.empty }, rv)], b, r)
        | otherwise = return (NoProgress, [(s, rv)], b, r)

data LabeledErrorsH = LabeledErrorsH

instance Halter LabeledErrorsH () t where
    initHalt _ _ = ()
    updatePerStateHalt _ hv _ _ = hv
    stopRed _ _ _ (State { curr_expr = CurrExpr _ ce, exec_stack = stck })
        | isLabeledError ce, S.null stck = return Accept
        | otherwise = return Continue
    stepHalter _ hv _ _ _ = hv

-- this does not account for type arguments
argCount :: Type -> Int
argCount (TyApp _ t) = 1 + argCount t
argCount _ = 0

exprFullApp :: ExprEnv -> Expr -> Bool
exprFullApp h e | (Tick (NamedLoc (Name p _ _ _)) f):as <- unApp e
                , p == T.pack "REC" = exprFullApp h (mkApp $ f:as)
exprFullApp h e | (Var (Id n t)):_ <- unApp e
                -- We require that the variable be the center of a function
                -- application, have at least one argument, and not map to a variable for two reasons:
                -- (1) We do not want to count symbolic function applications as in FAF form
                -- (2) We need to ensure we make sufficient progress to avoid
                -- moreRestrictive matching states spuriously.
                -- Consider an expression environment with a mapping of `x :: Int` to `f y`.
                -- We want to avoid storing a previous state using x,
                -- having the symbolic execution inline `f y`, and then deciding that 
                -- the two states match and are sufficient for verification to succeed,
                -- when, in isMoreRestrictive, x is inlined.
                , Just e' <- E.lookup n h
                , not (isVar e')
                , c_unapp <- length (unApp e)
                , c_unapp >= 2 = c_unapp == 1 + argCount t
exprFullApp _ _ = False

isVar :: Expr -> Bool
isVar (Tick _ e) = isVar e
isVar (Var _) = True
isVar _ = False

-- induction only works if both states in a pair satisfy this
-- there's no harm in stopping here for just one, though
-- TODO removing the Case requirement doesn't fix forceIdempotent
recursionInCase :: State t -> Bool
recursionInCase (State { curr_expr = CurrExpr _ e }) =
    case e of
        Tick (NamedLoc (Name p _ _ _)) _ ->
            p == T.pack "REC" -- && containsCase sk
        _ -> False

-- used by EquivADT and Tactics
concretizable :: Type -> Bool
concretizable (TyVar _) = False
concretizable (TyForAll _ _) = False
concretizable (TyFun _ _) = False
concretizable t@(TyApp _ _) =
  typeFullApp t && (concretizable $ last $ TY.unTyApp t)
concretizable TYPE = False
concretizable TyUnknown = False
concretizable _ = True

typeFullApp :: Type -> Bool
typeFullApp t@(TyApp _ _) =
    let c_unapp = length $ TY.unTyApp t
    in c_unapp >= 2 && 1 + argCount t == c_unapp
typeFullApp _ = False

instance Halter EnforceProgressH () EquivTracker where
    initHalt _ _ = ()
    updatePerStateHalt _ _ _ _ = ()
    stopRed _ _ _ s =
        let CurrExpr _ e = curr_expr s
            n' = num_steps s
            EquivTracker _ m _ _ _ _ _ = track s
            h = expr_env s
        in
        case m of
            Nothing -> return Continue
            -- Execution needs to take strictly more than one step beyond the
            -- point when it reaches the Tick because the act of unwrapping the
            -- expression inside the Tick counts as one step.
            Just n0 -> do
                if (isExecValueForm s) || (exprFullApp h e) || (recursionInCase s)
                       then return (if n' > n0 + 1 then Accept else Continue)
                       else return Continue
    stepHalter _ _ _ _ _ = ()

emptyEquivTracker :: EquivTracker
emptyEquivTracker = EquivTracker HM.empty Nothing HS.empty HS.empty [] E.empty ""

data EquivReducer = EquivReducer

instance Reducer EquivReducer () EquivTracker where
    initReducer _ _ = ()
    redRules r _
                 s@(State { expr_env = eenv
                          , curr_expr = CurrExpr Evaluate e
                          , track = EquivTracker et m total finite dcp opp fname })
                 b@(Bindings { name_gen = ng })
        | isSymFuncApp eenv (removeAllTicks e) =
            let
                -- We inline variables to have a higher chance of hitting in the Equiv Tracker
                e' = removeAllTicks $ inlineApp eenv e
            in
            case HM.lookup e' et of
                Just v ->
                    let eenv' = case E.lookup (idName v) eenv of
                            Just _ -> eenv
                            Nothing -> E.insertSymbolic v eenv
                        s' = s {
                            curr_expr = CurrExpr Evaluate (Var v)
                          , expr_env = eenv'
                        }
                    in
                    return (InProgress, [(s', ())], b, r)
                Nothing ->
                    let
                        (v, ng') = freshId (typeOf e) ng
                        et' = HM.insert e' v et
                        -- carry over totality if function and all args are total
                        -- unApp, make sure every arg is a total symbolic var
                        -- these are exprs originally
                        {-
                        es = map exprVarName $ unApp e'
                        all_vars = all isJust es
                        es' = map (\(Just n) -> n) $ filter isJust es
                        all_sym = all (\x -> E.isSymbolic x eenv) es'
                        -}
                        -- TODO I could use totalExpr here
                        -- TODO do I have access to ns here?
                        -- TODO do I still want all_sym?
                        all_total = all (totalExpr s HS.empty []) $ unApp e'
                        total' = if all_total
                                 then HS.insert (idName v) total
                                 else total
                        s' = s { curr_expr = CurrExpr Evaluate (Var v)
                               , track = EquivTracker et' m total' finite dcp opp fname
                               , expr_env = E.insertSymbolic v eenv }
                        b' = b { name_gen = ng' }
                    in-- trace ("SYM FUNC " ++ show v ++ "\n" ++ show e) $
                    return (InProgress, [(s', ())], b', r)
    redRules r rv s b = return (NoProgress, [(s, rv)], b, r)

-- TODO not exhaustive
-- cyclic expressions do not count as total for now
-- if a cycle never goes through a Data constructor, it's not total
-- TODO reject Error and Undefined primitives
totalExpr :: StateET ->
             HS.HashSet Name ->
             [Name] -> -- variables inlined previously
             Expr ->
             Bool
totalExpr s@(State { expr_env = h, track = EquivTracker _ _ total _ _ h' _ }) ns n e =
  case e of
    Tick _ e' -> totalExpr s ns n e'
    Var i | m <- idName i
          , isSymbolicBoth m h h' -> m `elem` total
          | m <- idName i
          , not $ HS.member m ns
          , not $ m `elem` n
          , Just e' <- lookupBoth m h h' -> totalExpr s ns (m:n) e'
          | (idName i) `elem` n -> False
          | HS.member (idName i) ns -> False
          | otherwise -> error $ "unmapped variable " ++ show i ++ " " ++ (folder_name $ track s)
    App f a -> totalExpr s ns n f && totalExpr s ns n a
    Data _ -> True
    Prim p _ -> not (p == Error || p == Undefined)
    Lit _ -> True
    Lam _ _ _ -> False
    Type _ -> True
    Let _ _ -> False
    Case _ _ _ -> False
    _ -> False

-- helper function to circumvent syncSymbolic
-- for symbolic things, lookup returns the variable
lookupBoth :: Name -> ExprEnv -> ExprEnv -> Maybe Expr
lookupBoth n h1 h2 = case E.lookupConcOrSym n h1 of
  Just (E.Conc e) -> Just e
  Just (E.Sym i) -> case E.lookup n h2 of
                      Nothing -> Just $ Var i
                      m -> m
  Nothing -> E.lookup n h2

-- doesn't count as symbolic if it's unmapped
-- condition we need:  n is symbolic in every env where it's mapped
isSymbolicBoth :: Name -> ExprEnv -> ExprEnv -> Bool
isSymbolicBoth n h1 h2 =
  case E.lookupConcOrSym n h1 of
    Just (E.Sym _) -> case E.lookupConcOrSym n h2 of
                        Just (E.Conc _) -> False
                        _ -> True
    Just (E.Conc _) -> False
    Nothing -> E.isSymbolic n h2

isSymFuncApp :: ExprEnv -> Expr -> Bool
isSymFuncApp eenv e
    | v@(Var _):(_:_) <- unApp e
    , (Var (Id f t)) <- inlineVars eenv v =
       E.isSymbolic f eenv && hasFuncType (PresType t)
    | otherwise = False

removeTicks :: Expr -> Expr
removeTicks (Tick _ e) = removeTicks e
removeTicks e = e

removeAllTicks :: Expr -> Expr
removeAllTicks = modifyASTs removeTicks

inlineApp :: ExprEnv -> Expr -> Expr
inlineApp eenv = mkApp . map (inlineVars eenv) . unApp

inlineVars :: ExprEnv -> Expr -> Expr
inlineVars = inlineVars' HS.empty

inlineVars' :: HS.HashSet Name -> ExprEnv -> Expr -> Expr
inlineVars' seen eenv (Var (Id n _))
    | not (n `HS.member` seen)
    , Just e <- E.lookup n eenv = inlineVars' (HS.insert n seen) eenv e
inlineVars' seen eenv (App e1 e2) = App (inlineVars' seen eenv e1) (inlineVars' seen eenv e2)
inlineVars' _ _ e = e

instance ASTContainer EquivTracker Expr where
    containedASTs (EquivTracker hm _ _ _ _ _ _) = HM.keys hm
    modifyContainedASTs f (EquivTracker hm m total finite dcp opp fname) =
        (EquivTracker . HM.fromList . map (\(k, v) -> (f k, v)) $ HM.toList hm)
        m total finite dcp opp fname

instance ASTContainer EquivTracker Type where
    containedASTs (EquivTracker hm _ _ _ _ _ _) = containedASTs $ HM.keys hm
    modifyContainedASTs f (EquivTracker hm m total finite dcp opp fname) =
        ( EquivTracker
        . HM.fromList
        . map (\(k, v) -> (modifyContainedASTs f k, modifyContainedASTs f v))
        $ HM.toList hm )
        m total finite dcp opp fname

-- TODO should names change in total and finite?
-- TODO change names for dc path?
instance Named EquivTracker where
    names (EquivTracker hm _ _ _ _ _ _) = names hm
    rename old new (EquivTracker hm m total finite dcp opp fname) =
        EquivTracker (rename old new hm) m (rename old new total) (rename old new finite) dcp (rename old new opp) fname
