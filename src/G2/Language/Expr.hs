{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Language.Expr ( module G2.Language.Casts
                        , eqUpToTypes
                        , unApp
                        , mkApp
                        , mkDCTrue
                        , mkDCFalse
                        , mkTrue
                        , mkFalse
                        , mkBool
                        , mkDCInt
                        , mkDCInteger
                        , mkDCFloat
                        , mkDCDouble
                        , mkDCChar
                        , mkCons
                        , mkEmpty
                        , mkJust
                        , mkNothing
                        , mkUnit

                        , mkIdentity
                        , mkEqExpr
                        , mkGeIntExpr
                        , mkLeIntExpr
                        , mkAndExpr
                        , mkOrExpr
                        , mkNotExpr
                        , mkImpliesExpr
                        , mkToRatioExpr
                        , mkFromRationalExpr
                        , mkIntegralExtactReal
                        , mkRealExtractNum
                        , mkRealExtractOrd
                        , mkOrdExtractEq

                        , mkEqPrimExpr

                        , isData
                        , isLit
                        , isLam
                        , isADT

                        , replaceVar
                        , getFuncCalls
                        , getFuncCallsRHS
                        , modifyAppTop
                        , modifyAppedDatas
                        , modifyAppLHS
                        , modifyAppRHS
                        , modifyLamTop
                        , nonDataFunctionCalls
                        , appCenter
                        , mapArgs
                        , mkLams
                        , elimAsserts
                        , elimAssumes
                        , assertsToAssumes
                        , leadingLamUsesIds
                        , leadingLamIds
                        , insertInLams
                        , maybeInsertInLams
                        , inLams
                        , simplifyLams
                        , flattenLets
                        , replaceASTs
                        , args
                        , passedArgs
                        , vars
                        , varIds
                        , varNames
                        , varId
                        , symbVars
                        , freeVars
                        , alphaReduction
                        , varBetaReduction
                        , etaExpandTo
                        , mkStrict
                        , mkStrict_maybe) where

import G2.Language.AST
import G2.Language.Casts
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import G2.Language.Naming
import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Typing
import G2.Language.Primitives

import Data.Foldable
import qualified Data.Map as M
import Data.Maybe
import Data.Semigroup

eqUpToTypes :: Expr -> Expr -> Bool
eqUpToTypes (Var (Id n _)) (Var (Id n' _)) = n == n'
eqUpToTypes (Lit l) (Lit l') = l == l'
eqUpToTypes (Prim p _) (Prim p' _) = p == p'
eqUpToTypes (Data (DataCon n _ _)) (Data (DataCon n' _ _)) = n == n'
eqUpToTypes (App e1 e2) (App e1' e2') = e1 `eqUpToTypes` e1' && e2 `eqUpToTypes` e2'
eqUpToTypes (Lam lu (Id n _) e) (Lam lu' (Id n' _) e') = lu == lu' && n == n' && e `eqUpToTypes` e'
eqUpToTypes (Let b e) (Let b' e') =
    let
        be_eq = all (\((Id n _, be), (Id n' _, be')) -> n == n' && be `eqUpToTypes` be') $ zip b b'
    in
    be_eq && e `eqUpToTypes` e'
eqUpToTypes (Case _ _ _ _) (Case _ _ _ _) = error "Case not supported"
eqUpToTypes (Type _) (Type _) = True
eqUpToTypes (Cast e _) (Cast e' _) = e `eqUpToTypes` e'
eqUpToTypes (Coercion _) (Coercion _) = True
eqUpToTypes (Tick _ e) (Tick _ e') = e `eqUpToTypes` e'
eqUpToTypes (NonDet es) (NonDet es') = all (uncurry eqUpToTypes) $ zip es es'
eqUpToTypes (SymGen _) (SymGen _) = True
eqUpToTypes (Assume _ _ _) (Assume _ _ _) = True
eqUpToTypes (Assert _ _ _) (Assert _ _ _) = True
eqUpToTypes _ _ = False

-- | Unravels the application spine.
unApp :: Expr -> [Expr]
unApp = unApp' []

unApp' :: [Expr] -> Expr -> [Expr]
unApp' xs (App f a) = unApp' (a:xs) f
unApp' xs e = e:xs

-- | Turns the Expr list into an Application
--
-- @ mkApp [e1, e2, e3] == App (App e1 e2) e3@
mkApp :: [Expr] -> Expr
mkApp [] = error "mkApp: empty list"
mkApp (e:[]) = e
mkApp (e1:e2:es) = mkApp (App e1 e2 : es)

mkDCInt :: KnownValues -> TypeEnv -> Expr
mkDCInt kv tenv = Data . fromJust $ getDataCon tenv (KV.tyInt kv) (KV.dcInt kv)

mkDCInteger :: KnownValues -> TypeEnv -> Expr
mkDCInteger kv tenv = Data . fromJust $ getDataCon tenv (KV.tyInteger kv) (KV.dcInteger kv)

mkDCFloat :: KnownValues -> TypeEnv -> Expr
mkDCFloat kv tenv = Data . fromJust $ getDataCon tenv (KV.tyFloat kv) (KV.dcFloat kv)

mkDCDouble :: KnownValues -> TypeEnv -> Expr
mkDCDouble kv tenv = Data . fromJust $ getDataCon tenv (KV.tyDouble kv) (KV.dcDouble kv)

mkDCChar :: KnownValues -> TypeEnv -> Expr
mkDCChar kv tenv = Data . fromJust $ getDataCon tenv (KV.tyChar kv) (KV.dcChar kv)

mkDCTrue :: KnownValues -> TypeEnv -> DataCon
mkDCTrue kv tenv = fromJust $ getDataCon tenv (KV.tyBool kv) (KV.dcTrue kv)

mkDCFalse :: KnownValues -> TypeEnv -> DataCon
mkDCFalse kv tenv = fromJust $ getDataCon tenv (KV.tyBool kv) (KV.dcFalse kv)

mkTrue :: KnownValues -> Expr
mkTrue kv = Data $ DataCon (KV.dcTrue kv) (TyCon (KV.tyBool kv) TYPE) []

mkFalse :: KnownValues -> Expr
mkFalse kv = Data $ DataCon (KV.dcFalse kv) (TyCon (KV.tyBool kv) TYPE) []

mkBool :: KnownValues -> Bool -> Expr
mkBool kv b = if b then mkTrue kv else mkFalse kv

mkCons :: KnownValues -> TypeEnv -> Expr
mkCons kv tenv = Data . fromJust $ getDataCon tenv (KV.tyList kv) (KV.dcCons kv)

mkEmpty :: KnownValues -> TypeEnv -> Expr
mkEmpty kv tenv = Data . fromJust $ getDataCon tenv (KV.tyList kv) (KV.dcEmpty kv)

mkJust :: KnownValues -> TypeEnv -> Expr
mkJust kv tenv = Data . fromJust $ getDataCon tenv (KV.tyMaybe kv) (KV.dcJust kv)

mkNothing :: KnownValues -> TypeEnv -> Expr
mkNothing kv tenv = Data . fromJust $ getDataCon tenv (KV.tyMaybe kv) (KV.dcNothing kv)

mkUnit :: KnownValues -> TypeEnv -> Expr
mkUnit kv tenv = Data . fromJust $ getDataCon tenv (KV.tyUnit kv) (KV.dcUnit kv)

mkIdentity :: Type -> Expr
mkIdentity t =
    let
        x = Id (Name "x" Nothing 0 Nothing) t
    in
    Lam TermL x (Var x)

mkEqExpr :: KnownValues -> Expr -> Expr -> Expr
mkEqExpr kv e1 e2 = App (App eq e1) e2
    where eq = mkEqPrimType (typeOf e1) kv

mkEqPrimExpr :: KnownValues -> Expr -> Expr -> Expr
mkEqPrimExpr kv e1 e2 = App (App eq e1) e2
    where eq = mkEqPrimType (typeOf e1) kv

mkGeIntExpr :: KnownValues -> Expr -> Integer -> Expr
mkGeIntExpr kv e num = App (App ge e) (Lit (LitInt num))
    where ge = mkGePrimInt kv

mkLeIntExpr :: KnownValues -> Expr -> Integer -> Expr
mkLeIntExpr kv e num = App (App le e) (Lit (LitInt num))
    where le = mkLePrimInt kv

mkAndExpr :: KnownValues -> Expr -> Expr -> Expr
mkAndExpr kv e1 e2 = App (App andEx e1) e2
    where andEx = mkAndPrim kv

mkOrExpr :: KnownValues -> Expr -> Expr -> Expr
mkOrExpr kv e1 e2 = App (App orEx e1) e2
    where orEx = mkOrPrim kv

mkImpliesExpr :: KnownValues -> Expr -> Expr -> Expr
mkImpliesExpr kv e1 e2 = App (App impEx e1) e2
    where impEx = mkImpliesPrim kv

mkNotExpr :: KnownValues -> Expr -> Expr
mkNotExpr kv e = App notEx e
    where notEx = mkNotPrim kv

mkToRatioExpr :: KnownValues -> Expr
mkToRatioExpr kv = Var $ Id (KV.toRatioFunc kv) TyUnknown

mkFromRationalExpr :: KnownValues -> Expr
mkFromRationalExpr kv = Var $ Id (KV.fromRationalFunc kv) TyUnknown

mkIntegralExtactReal :: KnownValues -> Expr
mkIntegralExtactReal kv = Var $ Id (KV.integralExtactReal kv) TyUnknown

mkRealExtractNum :: KnownValues -> Expr
mkRealExtractNum kv = Var $ Id (KV.realExtractNum kv) TyUnknown

mkRealExtractOrd :: KnownValues -> Expr
mkRealExtractOrd kv = Var $ Id (KV.realExtractOrd kv) TyUnknown

mkOrdExtractEq :: KnownValues -> Expr
mkOrdExtractEq kv = Var $ Id (KV.ordExtractEq kv) TyUnknown

isData :: Expr -> Bool
isData (Data _) = True
isData _ = False

isLit :: Expr -> Bool
isLit (Lit _) = True
isLit _ = False

isLam :: Expr -> Bool
isLam (Lam _ _ _) = True
isLam _ = False

isADT :: Expr -> Bool
isADT e
    | Data _:_ <- unApp e = True
    | otherwise = False

replaceVar :: ASTContainer m Expr => Name -> Expr -> m -> m
replaceVar n e = modifyContainedASTs (replaceVar' n e)

replaceVar' :: Name -> Expr -> Expr -> Expr
replaceVar' n e v@(Var (Id n' _)) =
    if n == n' then e else v
replaceVar' n _ le@(Lam _ (Id n' _) _) | n == n' = le
replaceVar' n e (Case b i@(Id n' _) t as) | n == n' = Case (replaceVar n e b) i t as
replaceVar' n e (Case b i t as) = Case (replaceVar' n e b) i t (map repAlt as)
    where
        repAlt a@(Alt (DataAlt _ is) _)
            | n `elem` map idName is = a
        repAlt a = modifyContainedASTs (replaceVar' n e) a
replaceVar' n _ le@(Let b _) | n `elem` map (idName . fst) b = le
replaceVar' n e e' = modifyChildren (replaceVar' n e) e'

getFuncCalls :: ASTContainer m Expr => m -> [Expr]
getFuncCalls = evalContainedASTs getFuncCalls'

getFuncCalls' :: Expr -> [Expr]
getFuncCalls' a@(App e1 e2) = a:getFuncCallsRHS e1 ++ getFuncCalls' e2
getFuncCalls' v@(Var _) = [v]
getFuncCalls' e = evalChildren getFuncCalls' e

getFuncCallsRHS :: Expr -> [Expr]
getFuncCallsRHS (App e1 e2) = getFuncCallsRHS e1 ++ getFuncCalls' e2
getFuncCallsRHS (Var _) = []
getFuncCallsRHS e = getFuncCalls' e

-- | Calls the given function on the topmost @App@ in every function application
-- in the given `Expr`
modifyAppTop :: ASTContainer m Expr => (Expr -> Expr) -> m -> m
modifyAppTop f = modifyContainedASTs (modifyAppTop' f)

modifyAppTop' :: (Expr -> Expr) -> Expr -> Expr
modifyAppTop' f e@(App _ _) =
    let
        e' = f e
    in
    modifyAppCenter (modifyChildren (modifyAppTop' f)) $ modifyAppRHS (modifyAppTop' f) e' 
modifyAppTop' f e = modifyChildren (modifyAppTop' f) e

modifyAppedDatas :: ASTContainer m Expr => (DataCon -> [Expr] -> Expr) -> m -> m
modifyAppedDatas f = modifyContainedASTs (modifyAppedDatas' f)

modifyAppedDatas' :: (DataCon -> [Expr] -> Expr) -> Expr -> Expr
modifyAppedDatas' f e
    | (Data dc:es) <- unApp e =
    let
        e' = f dc es
    in
    modifyAppCenter (modifyChildren (modifyAppedDatas' f)) $ modifyAppRHS (modifyAppedDatas' f) e'
    | otherwise = modifyChildren (modifyAppedDatas' f) e

modifyAppRHS :: (Expr -> Expr) -> Expr -> Expr
modifyAppRHS f (App e e') = App (modifyAppRHS f e) (f e')
modifyAppRHS _ e = e

modifyAppLHS :: (Expr -> Expr) -> Expr -> Expr
modifyAppLHS f (App e e') = App (f e) (modifyAppLHS f e')
modifyAppLHS _ e = e

modifyAppCenter :: (Expr -> Expr) -> Expr -> Expr
modifyAppCenter f (App e e') = App (modifyAppCenter f e) e'
modifyAppCenter f e = f e

modifyLamTop :: ASTContainer m Expr => (Expr -> Expr) -> m -> m
modifyLamTop f = modifyContainedASTs (modifyLamTop' f)

modifyLamTop' :: (Expr -> Expr) -> Expr -> Expr
modifyLamTop' f e@(Lam _ _ _) =
    let
        e' = f e
    in
    modifyLamRHS (modifyLamTop' f) e'
modifyLamTop' f e = modifyChildren f e

modifyLamRHS :: (Expr -> Expr) -> Expr -> Expr
modifyLamRHS f (Lam u i e) = Lam u i $ modifyLamRHS f e
modifyLamRHS f e = f e

-- | Returns all function calls to Vars with all arguments
nonDataFunctionCalls :: ASTContainer m Expr => m -> [Expr]
nonDataFunctionCalls = filter (not . centerIsData) . getFuncCalls

centerIsData :: Expr -> Bool
centerIsData (App e _) = centerIsData e
centerIsData (Data _) = True
centerIsData _ = False

-- Gets the `Expr` at the center of several nested @App@s
appCenter :: Expr -> Expr
appCenter (App a _) = appCenter a
appCenter e = e

mapArgs :: (Expr -> Expr) -> Expr -> Expr
mapArgs f (App e e') = App (mapArgs f e) (f e')
mapArgs _ e = e

mkLams :: [(LamUse, Id)] ->  Expr -> Expr
mkLams =  flip (foldr (\(u, i) -> Lam u i))

-- | Remove all @Assert@s from the given `Expr`
elimAsserts :: ASTContainer m Expr => m -> m
elimAsserts = modifyASTs elimAsserts'

elimAsserts' :: Expr -> Expr
elimAsserts' (Assert _ _ e) = e
elimAsserts' e = e

-- | Remove all @Assume@s from the given `Expr`
elimAssumes :: ASTContainer m Expr => m -> m
elimAssumes = modifyASTs elimAssumes'

elimAssumes' :: Expr -> Expr
elimAssumes' (Assume _ _ e) = e
elimAssumes' e = e

assertsToAssumes :: ASTContainer m Expr => m -> m
assertsToAssumes = modifyASTs assertsToAssumes'

assertsToAssumes' :: Expr -> Expr
assertsToAssumes' (Assert fc e e') = Assume fc e e'
assertsToAssumes' e = e

-- Runs the given function f on the expression nested in the lambdas, and
-- rewraps the new expression with the Lambdas
insertInLams :: ([Id] -> Expr -> Expr) -> Expr -> Expr
insertInLams f = insertInLams' f []

insertInLams' :: ([Id] -> Expr -> Expr) -> [Id] -> Expr -> Expr
insertInLams' f xs (Lam u i e)  = Lam u i $ insertInLams' f (i:xs) e
insertInLams' f xs e = f (reverse xs) e

maybeInsertInLams :: ([Id] -> Expr -> Maybe Expr) -> Expr -> Maybe Expr
maybeInsertInLams f = maybeInsertInLams' f []

maybeInsertInLams' :: ([Id] -> Expr -> Maybe Expr) -> [Id] -> Expr -> Maybe Expr
maybeInsertInLams' f xs (Lam u i e)  = fmap (Lam u i) $ maybeInsertInLams' f (i:xs) e
maybeInsertInLams' f xs e = f (reverse xs) e

-- | Returns the Expr in nested Lams
inLams :: Expr -> Expr
inLams (Lam _ _ e) = inLams e
inLams e = e

simplifyLams :: ASTContainer c Expr => c -> c
simplifyLams = modifyASTs simplifyLams'

simplifyLams' :: Expr -> Expr
simplifyLams' (App (Lam _ i e1) e2) = replaceASTs (Var i) e2 e1
simplifyLams' e = e

leadingLamUsesIds :: Expr -> [(LamUse, Id)]
leadingLamUsesIds (Lam u i e) = (u, i):leadingLamUsesIds e
leadingLamUsesIds _ = []

leadingLamIds :: Expr -> [Id]
leadingLamIds (Lam _ i e) = i:leadingLamIds e
leadingLamIds _ = []

flattenLets :: ASTContainer m Expr => m -> m
flattenLets = modifyASTs flattenLet

flattenLet :: Expr -> Expr
flattenLet l@(Let be e) =
    case findElem (isLet . snd) be of
        Just ((bi, Let ibe ie), be') -> flattenLet $ Let (ibe ++ (bi, ie):be') e
        _ -> l
flattenLet e = e

isLet :: Expr -> Bool
isLet (Let _ _) = True
isLet _ = False

findElem :: (a -> Bool) -> [a] -> Maybe (a, [a])
findElem p = find' id
    where
      find' _ []         = Nothing
      find' pre (x : xs)
          | p x          = Just (x, pre xs)
          | otherwise    = find' (pre . (x:)) xs

-- | Returns all Ids from Lam's at the top of the Expr
args :: Expr -> [Id]
args (Lam _ i e) = i:args e
args _ = []

passedArgs :: Expr -> [Expr]
passedArgs = reverse . passedArgs'

passedArgs' :: Expr -> [Expr]
passedArgs' (App e e') = e':passedArgs' e
passedArgs' _ = []

--Returns all Vars in an ASTContainer
vars :: (ASTContainer m Expr) => m -> [Id]
vars = evalASTs vars'

vars' :: Expr -> [Id]
vars' (Var i) = [i]
vars' _ = []

varId :: Expr -> Maybe Id
varId (Var i) = Just i
varId _ = Nothing

symbVars :: (ASTContainer m Expr) => ExprEnv -> m -> [Id]
symbVars eenv = filter (symbVars' eenv) . vars

symbVars' :: ExprEnv -> Id -> Bool
symbVars' eenv (Id n _) = E.isSymbolic n eenv

-- | freeVars
-- Returns the free (unbound by a Lambda, Let, or the Expr Env) variables of an expr
freeVars :: ASTContainer m Expr => E.ExprEnv -> m -> [Id]
freeVars eenv = evalASTsMonoid (freeVars' eenv)

freeAltMatch :: AltMatch -> [Id]
freeAltMatch (DataAlt _ is) = is
freeAltMatch _ = []

freeVars' :: E.ExprEnv -> [Id] -> Expr -> ([Id], [Id])
freeVars' _ _ (Let b _) = (map fst b, [])
freeVars' _ _ (Lam _ b _) = ([b], [])
freeVars' _ _ (Case _ b _ alt) = (b:concatMap (freeAltMatch . altMatch) alt, [])
freeVars' eenv bound (Var i) =
    if E.member (idName i) eenv || i `elem` bound then
        ([], [])
    else
        ([], [i])
freeVars' _ _ _ = ([], [])

alphaReduction :: ASTContainer m Expr => m -> m
alphaReduction = modifyASTsMonoid alphaReduction'

alphaReduction' :: Max Int -> Expr -> (Expr, Max Int)
alphaReduction' mi l@(Lam u i@(Id (Name n m ii lo) t) e) =
    let
        mi' = mi + 1
        n' = Name n m (getMax mi') lo
        i' = Id n' t

        e' = replaceASTs (Var i) (Var i') e
    in
    if ii > getMax mi then (l, mi') else (Lam u i' e', mi')
alphaReduction' m e = (e, m)

-- |  Performs beta reduction, if a Var is being applied 
varBetaReduction :: ASTContainer m Expr => m -> m
varBetaReduction = modifyASTs varBetaReduction'

varBetaReduction' :: Expr -> Expr
varBetaReduction' a@(App (Lam _ i e) (Var v)) = 
    if not (isTYPE . typeOf $ i) then replaceLamIds i v e else a
varBetaReduction' e = e

replaceLamIds :: Id -> Id -> Expr -> Expr
replaceLamIds i i' v@(Var v') = if i == v' then Var i' else v
replaceLamIds i i' l@(Lam u l' e) = if i == l' then l else Lam u l' (replaceLamIds i i' e)
replaceLamIds i i' e = modifyChildren (replaceLamIds i i') e

-- | If doing so will not change evaluation, eta expands to the given arity.
-- This function is conservative, so it may sometimes fail to determine that
-- we can perform eta expansion, even when it can.
-- However, it should NEVER eta expand something that will change evaluation.
--
-- Eta expansion converts:
--           @ abs @
-- to
--     @ \x -> abs x @
-- and
--           @ \x -> (+) x @
-- to
--     @ \x -> \y -> (+) x y @
-- That is, it looks directly inside the outermost lambdas
--
-- If the arity is greater than the given number, does nothing.
-- If the given number is greater than the maximal number of arguments,
-- tries to expand to the maximal number of arguments.
--
-- This function is careful to not change 
-- That is, we cannot convert:
--      @ undefined `seq` 1 @
-- to
--      @ (\x -> undefined x) `seq` 1 @
-- because the first will call undefined, and error, whereas the second will
-- evaluate to 1.
etaExpandTo :: ExprEnv -> NameGen -> Int -> Expr -> (Expr, NameGen)
etaExpandTo eenv ng n (Lam u i e) =
    let
        (e', ng') = etaExpandTo eenv ng n e
    in
    (Lam u i e', ng')
etaExpandTo eenv ng n e = etaExpandTo' eenv ng n e

etaExpandTo' :: ExprEnv -> NameGen -> Int -> Expr -> (Expr, NameGen)
etaExpandTo' eenv ng n e = (addLamApps fn (typeOf e) e, ng')
    where
        n' = n `min` numArgs e
        n'' = validN eenv M.empty n' e

        (fn, ng') = freshNames n'' ng

        -- Determines if we can eta expand the Expr, without changing semantics
        -- This requires looking in variables, possibly recursively.
        -- We use the map to track if recursive lookups are actually decreasing arity,
        -- and prevent an infinite loop
        validN :: ExprEnv -> M.Map Name Int -> Int -> Expr -> Int
        validN _ _ 0 _ = n'
        validN eenv' m i (Lam _ _ e') = validN eenv' m (i - 1) e'
        validN eenv' m i (Var (Id v _))
            | Just i' <- M.lookup v m
            , Just e' <- E.lookup v eenv' =
                if i >= i' then n' - i `min` i' else validN eenv' m' i e'
            | Just e' <- E.lookup v eenv' = validN eenv' m' i e'
            | otherwise = n'
            where
                m' = M.insert v i m
        validN _ _ i (Data _) = i
        validN eenv' m i (App e' _) = validN eenv' m (i + 1) e'
        validN eenv' m i (Let b e') =
            let
                eenv'' = E.insertExprs (map (\(i', e'') -> (idName i', e'')) b) eenv'
            in
            validN eenv'' m i e'
        validN _ _ i _ = n' - i

        addLamApps :: [Name] -> Type -> Expr -> Expr
        addLamApps [] _ e' = e'
        addLamApps (_:ns) (TyForAll b t') e' =
            Lam TypeL b (App (addLamApps ns t' e') (Type (TyVar b)))
        addLamApps (ln:ns) (TyFun t t') e' =
            Lam TermL (Id ln t) (App (addLamApps ns t' e') (Var (Id ln t)))
        addLamApps _ _ e' = e'


-- | Forces the complete evaluation of an expression
mkStrict :: (ASTContainer m Expr) => Walkers -> m -> m
mkStrict w = modifyContainedASTs (mkStrict' w)

mkStrict' :: Walkers -> Expr -> Expr
mkStrict' w e =
    let
        rt = returnType e
        t = tyAppCenter rt
        ts = tyAppArgs rt
    in
    case t of
        (TyCon n _) -> case M.lookup n w of
            Just i -> App (foldl' (App) (Var i) (map Type ts ++ map (typeToWalker w) ts)) e
            Nothing -> error $ "mkStrict: failed to find walker with type: " ++ show n
        _ -> error $ "No walker found in mkStrict\n e = " ++ show e ++ "\nt = " ++ show (typeOf e) ++ "\nret = " ++ show (returnType e)

typeToWalker :: Walkers -> Type -> Expr
typeToWalker w t
  | TyCon n _ <- tyAppCenter t
  , ts <- tyAppArgs t =
  case M.lookup n w of
    Just i -> foldl' (App) (Var i) (map Type ts ++ map (typeToWalker w) ts)
    Nothing -> error $ "typeToWalker: failed to find type: " ++ show n
typeToWalker _ t = mkIdentity t

mkStrict_maybe :: Walkers -> Expr -> Maybe Expr
mkStrict_maybe w e =
    let
        t = tyAppCenter (typeOf e)
        ts = tyAppArgs (typeOf e)
    in
    case t of
        (TyCon n _) -> case M.lookup n w of
            Just i -> Just $ App (foldl' (App) (Var i) (map Type ts ++ map (typeToWalker_maybe w) ts)) e
            Nothing -> Nothing
        _ -> Nothing

typeToWalker_maybe :: Walkers -> Type -> Expr
typeToWalker_maybe w t
  | TyCon n _ <- tyAppCenter t
  , ts <- tyAppArgs t =
  case M.lookup n w of
    Just i -> foldl' (App) (Var i) (map Type ts ++ map (typeToWalker_maybe w) ts)
    Nothing -> mkIdentity t
typeToWalker_maybe _ t = mkIdentity t
