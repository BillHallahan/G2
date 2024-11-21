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
                        , lookupConcOrSymBoth
                        , isSymbolicBoth ) where

import G2.Config
import G2.Execution
import G2.Execution.NormalForms
import G2.Interface
import G2.Language
import G2.Lib.Printers
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Stack as S
import G2.Solver
import G2.Equiv.Config

import Control.Monad.IO.Class
import qualified Control.Monad.State as SM
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

        state' = state { track = (track state) { saw_tick = Nothing } }

    (in_out, bindings') <- case rewriteRedHaltOrd solver simplifier h_opp track_opp config nc of
                (red, hal, ord) ->
                    SM.evalStateT (runG2WithSomes red hal ord solver simplifier sym_config state' bindings) (mkPrettyGuide ())


    return (in_out, bindings')

rewriteRedHaltOrd :: (MonadIO m, Solver solver, Simplifier simplifier) =>
                     solver ->
                     simplifier ->
                     E.ExprEnv ->
                     EquivTracker ->
                     Config ->
                     NebulaConfig ->
                     ( SomeReducer (SM.StateT PrettyGuide m) EquivTracker
                     , SomeHalter (SM.StateT PrettyGuide m) EquivTracker
                     , SomeOrderer (SM.StateT PrettyGuide m) EquivTracker)
rewriteRedHaltOrd solver simplifier h_opp track_opp config (NC { use_labeled_errors = use_labels }) =
    let
        share = sharing config
        state_name = Name "state" Nothing 0 Nothing

        m_logger = fmap SomeReducer $ getLogger config
        some_std_red = enforceProgressRed :== NoProgress --> stdRed share retReplaceSymbFuncVar solver simplifier
        extra_red = symbolicSwapperRed h_opp track_opp ~> concSymReducer use_labels ~> labeledErrorsRed
        red = equivReducer :== NoProgress .--> extra_red :== NoProgress .--> some_std_red
    in
    (case m_logger of
        Just logger -> logger .~> red             
        Nothing -> red                            
     , SomeHalter
         (discardIfAcceptedTagHalter state_name
         <~> enforceProgressHalter
         <~> swhnfHalter
         <~> labeledErrorsHalter)
     , SomeOrderer $ pickLeastUsedOrderer)

type StateET = State EquivTracker

data BlockInfo = BlockDC DataCon Int Int
               | BlockLam Id
               deriving (Show, Eq, Generic)

instance Hashable BlockInfo

instance Named BlockInfo where
    names (BlockDC dc _ _) = names dc
    names (BlockLam i) = names i
    rename old new (BlockDC dc n1 n2) = BlockDC (rename old new dc) n1 n2
    rename old new (BlockLam i) = BlockLam (rename old new i)

-- Maps higher order function calls to symbolic replacements.
-- This allows the same call to be replaced by the same Id consistently.
data EquivTracker = EquivTracker { higher_order :: HM.HashMap Expr Id
                                 , saw_tick :: Maybe Int
                                 , total_vars :: HS.HashSet Name
                                 , dc_path :: [BlockInfo]
                                 , opp_env :: ExprEnv
                                 , folder_name :: String } deriving (Show, Eq, Generic)

instance Hashable EquivTracker

-- | Forces a lone symbolic variable with a type corresponding to an ADT
-- to evaluate to some value of that ADT
concSymReducer :: Monad m => UseLabeledErrors -> Reducer m () EquivTracker
concSymReducer use_labels = mkSimpleReducer
                    (const ())
                    rr
    where
        rr _
                 s@(State { curr_expr = CurrExpr _ (Var (Id n t))
                          , expr_env = eenv
                          , type_env = tenv
                          , track = EquivTracker et m total dcp opp fname })
                 b@(Bindings { name_gen = ng })
            | E.isSymbolic n eenv
            , Just (dc_symbs, ng') <- arbDC use_labels tenv ng t n total = do
                let new_names = map idName $ concat $ map snd dc_symbs
                    total' = if n `elem` total
                            then foldr HS.insert total new_names
                            else total
                    xs = map (\(e, symbs') ->
                                    s   { curr_expr = CurrExpr Evaluate e
                                        , expr_env =
                                            foldr E.insertSymbolic
                                                (E.insert n e eenv)
                                                symbs'
                                        , track = EquivTracker et m total' dcp opp fname
                                        }) dc_symbs
                    b' =  b { name_gen = ng' }
                    -- only add to total if n was total
                    -- not all of these will be used on each branch
                    -- they're all fresh, though, so overlap is not a problem
                return (InProgress, zip xs (repeat ()) , b')
        rr _ s b = return (NoProgress, [(s, ())], b)

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

            bound = bound_ids adt
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

symbolicSwapperRed :: Monad m => E.ExprEnv -> EquivTracker -> Reducer m () EquivTracker
symbolicSwapperRed h_opp track_opp = mkSimpleReducer
                        (const ())
                        rr
    where
        rr rv
           s@(State { curr_expr = CurrExpr _ e
                    , expr_env = h
                    , track = EquivTracker et m tot dcp opp fname })
           b =
            case e of
                Var (Id n _) | E.isSymbolic n h ->
                    case E.lookupConcOrSym n h_opp of
                        Just (E.Conc e') ->
                            let vi = varIds e'
                                vi_hs = HS.fromList $ map idName vi
                                h' = foldr (\j -> E.insertSymbolic j) (E.insert n e' h) (L.nub vi)
                                total' = HS.union (HS.intersection (total_vars track_opp) vi_hs) tot
                                track' = EquivTracker et m total' dcp opp fname
                                s' = s {
                                  expr_env = h'
                                , track = track'
                                }
                            in return (InProgress, [(s', rv)], b)
                        _ -> return (NoProgress, [(s, rv)], b)
                _ -> return (NoProgress, [(s, rv)], b)

enforceProgressRed :: Monad m => Reducer m () EquivTracker
enforceProgressRed = mkSimpleReducer
                        (const ())
                        rr
    where
        rr rv s@(State { curr_expr = CurrExpr _ e
                               , num_steps = n
                               , track = EquivTracker et m total dcp opp fname })
                      b =
            let s' = s { track = EquivTracker et (Just n) total dcp opp fname }
                need_more = case m of
                                Nothing -> True
                                Just n0 -> n > n0 + 1
            in
            case e of
                Tick (NamedLoc (Name p _ _ _)) _ ->
                    if p == T.pack "STACK" && need_more
                    then return (InProgress, [(s', ())], b)
                    else return (NoProgress, [(s, ())], b)
                _ -> return (NoProgress, [(s, rv)], b)

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

labeledErrorsRed :: Monad m => Reducer m () t
labeledErrorsRed = mkSimpleReducer
                        (const ())
                        rr
    where
        rr rv s@(State { curr_expr = CurrExpr _ ce }) b
            | isLabeledError ce = return (Finished, [(s { exec_stack = S.empty }, rv)], b)
            | otherwise = return (NoProgress, [(s, rv)], b)

labeledErrorsHalter :: Monad m => Halter m () t
labeledErrorsHalter = mkSimpleHalter (const ())
                                     (\hv _ _ -> hv)
                                     stop
                                     (\hv _ _ _ -> hv)
    where
        stop _ _ (State { curr_expr = CurrExpr _ ce, exec_stack = stck })
            | isLabeledError ce, S.null stck = return Accept
            | otherwise = return Continue


-- this does not account for type arguments
argCount :: Type -> Int
argCount = length . spArgumentTypes . PresType

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

enforceProgressHalter :: Monad m => Halter m () EquivTracker
enforceProgressHalter = mkSimpleHalter
                            (const ())
                            (\_ _ _ -> ())
                            stop
                            (\_ _ _ _ -> ())
    where
        stop _ _ s =
            let CurrExpr _ e = curr_expr s
                n' = num_steps s
                EquivTracker _ m _ _ _ _ = track s
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

emptyEquivTracker :: EquivTracker
emptyEquivTracker = EquivTracker HM.empty Nothing HS.empty [] E.empty ""

equivReducer :: Monad m => Reducer m () EquivTracker
equivReducer = mkSimpleReducer
                (const ())
                rr
    where
        rr _
           s@(State { expr_env = eenv
                    , curr_expr = CurrExpr Evaluate e
                    , track = EquivTracker et m total dcp opp fname })
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
                        return (InProgress, [(s', ())], b)
                    Nothing ->
                        let
                            (v, ng') = freshId (typeOf e) ng
                            et' = HM.insert e' v et
                            -- carry over totality if function and all args are total
                            all_total = all (totalExpr s HS.empty []) $ unApp e'
                            total' = if all_total
                                    then HS.insert (idName v) total
                                    else total
                            s' = s { curr_expr = CurrExpr Evaluate (Var v)
                                , track = EquivTracker et' m total' dcp opp fname
                                , expr_env = E.insertSymbolic v eenv }
                            b' = b { name_gen = ng' }
                        in
                        return (InProgress, [(s', ())], b')
        rr rv s b = return (NoProgress, [(s, rv)], b)

-- not exhaustive, but totality is undecidable in general
-- cyclic expressions do not count as total for now
-- if a cycle never goes through a Data constructor, it's not total
totalExpr :: StateET ->
             HS.HashSet Name ->
             [Name] -> -- variables inlined previously
             Expr ->
             Bool
totalExpr s@(State { expr_env = h, track = EquivTracker _ _ total _ h' _ }) ns n e =
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
    Case _ _ _ _ -> False
    _ -> False

-- helper function to circumvent syncSymbolic
-- for symbolic things, lookup returns the variable
lookupBoth :: Name -> ExprEnv -> ExprEnv -> Maybe Expr
lookupBoth n h1 = fmap E.concOrSymToExpr . lookupConcOrSymBoth n h1

lookupConcOrSymBoth :: Name -> ExprEnv -> ExprEnv -> Maybe E.ConcOrSym
lookupConcOrSymBoth n h1 h2 = case E.lookupConcOrSym n h1 of
  e@(Just (E.Conc _)) -> e
  sym@(Just (E.Sym _)) -> case E.lookupConcOrSym n h2 of
                      Nothing -> sym
                      m -> m
  Nothing -> E.lookupConcOrSym n h2

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
    containedASTs (EquivTracker hm _ _ _ _ _) = HM.keys hm
    modifyContainedASTs f (EquivTracker hm m total dcp opp fname) =
        (EquivTracker . HM.fromList . map (\(k, v) -> (f k, v)) $ HM.toList hm)
        m total dcp opp fname

instance ASTContainer EquivTracker Type where
    containedASTs (EquivTracker hm _ _ _ _ _) = containedASTs $ HM.keys hm
    modifyContainedASTs f (EquivTracker hm m total dcp opp fname) =
        ( EquivTracker
        . HM.fromList
        . map (\(k, v) -> (modifyContainedASTs f k, modifyContainedASTs f v))
        $ HM.toList hm )
        m total dcp opp fname

instance Named EquivTracker where
    names (EquivTracker hm _ _ _ _ _) = names hm
    rename old new (EquivTracker hm m total dcp opp fname) =
        EquivTracker (rename old new hm) m (rename old new total) (rename old new dcp) (rename old new opp) fname
