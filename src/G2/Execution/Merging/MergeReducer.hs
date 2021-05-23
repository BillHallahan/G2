{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TupleSections #-}

module G2.Execution.Merging.MergeReducer (MergeReducer (..)) where

import G2.Execution.NormalForms
import G2.Execution.NewPC
import G2.Execution.Reducer
import G2.Execution.Rules
import G2.Execution.Merging.StateMerging
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.Monad
import qualified G2.Language.PathConds as PC
import G2.Solver

import Control.Exception
import Control.Monad
import Control.Monad.Extra
import Control.Monad.IO.Class

import qualified Data.HashSet as HS
import qualified Data.Map.Lazy as M

import Debug.Trace

data MergeReducer solver simplifier = MergeReducer solver simplifier

instance (Solver solver, Simplifier simplifier) => Reducer (MergeReducer solver simplifier) () t where
    initReducer _ _ = ()
    redRules r@(MergeReducer solver simplifier) _ s b@(Bindings { name_gen = ng }) = do
        ((rr, xs), ng') <- runNamingT (mergeLitCases s) ng
        let b' = b { name_gen = ng' }
        xs' <- mapMaybeM (reduceNewPC solver simplifier) xs
        putStrLn $ "length xs = " ++ show (length xs) ++ "    length xs' = " ++ show (length xs')
        if length xs' == 0
            then do
                putStrLn "HERE"
                r <- check (solver) s (path_conds s)
                print r
            else return ()
        return (rr, map (,()) xs', b', r)

mergeLitCases :: (MonadIO m, NamingM s m) => State t -> m (ReducerRes, [NewPC t])
mergeLitCases s@(State { expr_env = eenv, curr_expr = CurrExpr er e}) = do
    case collectCases eenv [] e of
        [_] -> return (NoProgress, [newPCEmpty s])
        ile -> do
            xs <- mergeLitCases' er ile s
            return (Finished, xs)

-- Gathers pairs of the form (is, e).  The expression evaluates to e if for
-- each pair (i, l) in is, i = l.
collectCases :: ExprEnv -> [(Id, Lit)] -> Expr -> [([(Id, Lit)], Expr)]
collectCases eenv ils e
    | (Case (Var i@(Id _ t)) _ as) <- e'
    , TyLitInt <- t
    , all isLitAlt as =
        concatMap (\a -> 
                        let
                            (il, e) = litAltInfo i a
                        in
                        collectCases eenv (il:ils) e) as
    | otherwise = [(ils, e')]
    where
        e' = dig HS.empty eenv e

dig :: HS.HashSet Name -> ExprEnv -> Expr -> Expr
dig seen eenv v@(Var (Id n _))
    | E.isSymbolic n eenv = v
    | not (n `HS.member` seen)
    , Just e <- E.lookup n eenv = dig (HS.insert n seen) eenv e
    | otherwise = v
dig _ _ e = e

collapseCollectedCases :: [(Id, Lit)] -> NewPC t -> NewPC t
collapseCollectedCases il new_pc@(NewPC { state = s@(State { known_values = kv }) }) =
    let
        pc = map (flip ExtCond True)
           $ map (\(i, l) -> App (App (mkEqPrimInt kv) (Var i)) (Lit l)) il
    in
    new_pc { new_pcs = pc ++ new_pcs new_pc }

litAltInfo :: Id -> Alt -> ((Id, Lit), Expr)
litAltInfo i (Alt (LitAlt l) e) = ((i, l), e)
litAltInfo _ _ = error "litAltInfo: Bad Lit"

data MergeableExpr = FromVar Id SymbolicIds Expr | OtherExpr Expr deriving (Show, Read)

getExpr :: MergeableExpr -> Expr
getExpr (FromVar _ _ e) = e
getExpr (OtherExpr e) = e

mergeLitCases' :: (MonadIO m, NamingM s m) => EvalOrReturn -> [([(Id, Lit)], Expr)] -> State t -> m [NewPC t]
mergeLitCases' er iles s = do
    liftIO $ putStrLn (show iles)
    iles' <- concatMapM (expandVar (expr_env s) (type_env s)) iles
    merged <-  foldM (mergeWherePossible s) [] iles'
    return $ map (uncurry collapseCollectedCases) merged

expandVar :: NamingM s m => ExprEnv -> TypeEnv -> ([(Id, Lit)], Expr) -> m [([(Id, Lit)], MergeableExpr)]
expandVar eenv tenv (il, Var i@(Id n t))
    | E.isSymbolic n eenv
    , not (isPrimType t) = 
        return . map (\(ars, dc) -> (il, FromVar i ars dc)) =<< allDCs tenv i
expandVar _ _ (il, e) = return [(il, OtherExpr e)]

mergeWherePossible :: (MonadIO m, NamingM s m)
                   => State t
                   -> [([(Id, Lit)], NewPC t)]
                   -> ([(Id, Lit)], MergeableExpr)
                   -> m [([(Id, Lit)], NewPC t)]
mergeWherePossible orig_s@(State { curr_expr = CurrExpr er _ }) m_ile (il, me) = do
    rep_fst <- replaceFirst (uncurry (wJoinExpr il me)) m_ile
    case rep_fst of
        Just v -> return v
        Nothing 
            | FromVar (Id n _) symbs e <- me -> 
                let
                    eenv = foldr (\i -> E.insertSymbolic (idName i) i) (expr_env orig_s) symbs
                    new_pc = newPCEmpty $ orig_s { expr_env = E.insert n e eenv
                                                 , curr_expr = CurrExpr er e
                                                 , symbolic_ids = HS.union symbs (symbolic_ids orig_s) }
                in
                return ((il, new_pc):m_ile)
            | OtherExpr e <- me-> 
                let
                    new_pc = newPCEmpty $ orig_s { curr_expr = CurrExpr er e }
                in
                return ((il, new_pc):m_ile)
    where
        wJoinExpr is1 e1 is2 s = return . fmap ([],) =<< joinToState orig_s is1 e1 is2 s

-- replaces the first element in a list where the provided function returns a Just
-- or returns Nothing if no such element exists
replaceFirst :: Monad m => (a -> m (Maybe a)) -> [a] -> m (Maybe [a])
replaceFirst f ls = do
    r <- go [] ls
    return $ fmap reverse r
    where
        go _ [] = return Nothing
        go ys (x:xs) = do
            v <- f x
            case v of
                Just v' -> return (Just (ys ++ (v':xs)))
                Nothing -> go (x:ys) xs

joinToState :: (MonadIO m, NamingM s m)
            => State t
            -> [(Id, Lit)]
            -> MergeableExpr
            -> [(Id, Lit)]
            -> NewPC t
            -> m (Maybe (NewPC t))
joinToState orig_s is1 me1 is2 new_pc@(NewPC { state = s@(State { curr_expr = CurrExpr er1 ce })
                                            , new_pcs = pc 
                                            }) = do
    i <- freshIdN TyLitInt

    je <- runStateMInNamingM (joinExprs i me1 ce) s

    case je of
        (Just ce', s'@(State { expr_env = eenv, symbolic_ids = s_symbs })) ->  do
            let kv = known_values orig_s

            let imp1 = mkImp kv is1 (Var i) 1
                imp2 = mkImp kv is2 (Var i) 2

                bounds = mkBounds (Var i) 1 2
                pc' = bounds ++ ExtCond imp1 True:ExtCond imp2 True:map (PC.mkAssumePC i 2) pc

            let s'' = s' { curr_expr = CurrExpr er1 ce' }
                new_pc' = new_pc { state = s'', new_pcs = pc'}

            return (Just new_pc')
        (Nothing, _) -> return Nothing
    where
        mkLeading kv_ =
            foldr (mkAndExpr kv_) (mkTrue kv_)
            . map (\(i, l) -> App (App (mkEqPrimInt kv_) (Var i)) (Lit l))

        mkImp kv_ [] _ _ = mkTrue kv_
        mkImp kv_ is_ i_ l_ = App
                            (App (mkEqPrimType (tyBool kv_) kv_) (mkLeading kv_ is_))
                            (App (App (mkEqPrimInt kv_) i_) (Lit (LitInt l_)))

joinExprs :: Id -> MergeableExpr -> Expr -> StateNG t (Maybe Expr)
joinExprs i (FromVar vi symbs e1) e2 = do
    mapM_ (\i_ -> insertSymbolicE (idName i_) i_) symbs
    insertE (idName vi) e1
    unionSymbolicId symbs
    deleteSymbolicId vi
    joinExprs' i e1 e2
joinExprs i (OtherExpr e1) e2 = joinExprs' i e1 e2

joinExprs' :: Id -> Expr -> Expr -> StateNG t (Maybe Expr)
-- joinExprs i v1@(Var (Id n1 t)) v2@(Var (Id n2 _)) = do
--     eenv <- exprEnv

--     if  | E.isSymbolic n1 eenv
--         , E.isSymbolic n2 eenv -> undefined
--         | Just e1 <- smnfVal eenv v1
--         , Just e2 <- smnfVal eenv v2 -> joinExprs i e1 e2 
--         | otherwise -> return Nothing

-- joinExprs i v1@(Var vi@(Id n _)) e2 = do
--     eenv <- exprEnv

--     if  | E.isSymbolic n eenv -> do
--             e1 <- arbDCCase vi
--             insertE n e1
--             joinExprs i e1 e2
--         | Just e1 <- smnfVal eenv v1 -> joinExprs i e1 e2
--         | otherwise -> return Nothing
-- joinExprs i e1 v2@(Var vi@(Id n _)) = do
--     eenv <- exprEnv

--     if  | E.isSymbolic n eenv -> do
--             e2 <- arbDCCase vi
--             insertE n e2
--             joinExprs i e1 e2
--         | Just e2 <- smnfVal eenv v2 -> joinExprs i e1 e2
--         | otherwise -> return Nothing
joinExprs' i e1 e2
    | ce1:es1 <- unApp e1
    , ce2:es2 <- unApp e2
    , equivCenters ce1 ce2 = do
        m_es <- mapM (uncurry (mkInnerJoin i)) (zip es1 es2)
        let me = mkApp $ ce1:m_es
        return . Just $ me
joinExprs' _ _ _ = return Nothing

equivCenters :: Expr -> Expr -> Bool
equivCenters (Var (Id n1 _)) (Var (Id n2 _)) = n1 == n2
equivCenters (Data (DataCon n1 _)) (Data (DataCon n2 _)) = n1 == n2
equivCenters _ _ = False

mkInnerJoin :: Id -> Expr -> Expr -> StateNG t Expr
mkInnerJoin _ t@(Type t1) (Type t2) = assert (t1 == t2) $ return t
mkInnerJoin i@(Id _ t) e1 e2 = do
    kv <- knownValues
    eenv <- exprEnv
    
    if  | primVal eenv e1 && primVal eenv e2 -> do
            n_id <- freshIdN t
            insertSymbolicId n_id
            insertSymbolicE (idName n_id) n_id

            let pc1 = PC.mkAssumePC i 1 $ ExtCond (mkEqPrimExpr t kv (Var n_id) e1) True
                pc2 = PC.mkAssumePC i 2 $ ExtCond (mkEqPrimExpr t kv (Var n_id) e2) True
            insertPCStateNG pc1
            insertPCStateNG pc2

            return (Var n_id)
        | otherwise -> 
        return $ Case (Var i) i
                    [ Alt (LitAlt (LitInt 1)) e1
                    , Alt (LitAlt (LitInt 2)) e2]

primVal :: ExprEnv -> Expr -> Bool
primVal eenv (Var (Id n t))
    | isPrimType t
    , E.isSymbolic n eenv = True
    | otherwise = False
primVal eenv (Lit _) = True
primVal eenv e
    | (Prim _ _):_ <- unApp e = True
primVal _ _ = False

mkBounds :: Expr -> Integer -> Integer -> [PathCond]
mkBounds e l u =
    let
        t = TyFun TyLitInt $ TyFun TyLitInt TyLitInt
    in
    [ ExtCond (App (App (Prim Le t) (Lit (LitInt l))) e) True
    , ExtCond (App (App (Prim Le t) e) (Lit (LitInt u))) True]

allDCs :: NamingM s m => TypeEnv -> Id -> m [(SymbolicIds, Expr)]
allDCs tenv i@(Id _ t) = do
    -- kv <- knownValues
    -- bool <- tyBoolT

    -- if  | (PresType t) .:: bool -> do
    --         let tre@(Data tre_dc) = mkTrue kv
    --             flse@(Data flse_dc) = mkFalse kv

    --         bindee_id <- freshIdN TyLitInt
    --         let bindee = Var bindee_id
    --         let pc = mkBounds bindee 1 2
    --             bool_pc = [ PC.mkAssumePC bindee_id 1 $ ExtCond (Var i) True
    --                       , PC.mkAssumePC bindee_id 2 $ ExtCond (Var i) False ]
    --             e = Case bindee bindee_id
    --                     [ Alt (LitAlt (LitInt 1)) tre
    --                     , Alt (LitAlt (LitInt 2)) flse]

    --         insertSymbolicE (idName bindee_id) bindee_id
    --         insertSymbolicId bindee_id
    --         mapM_ insertPCStateNG (pc ++ bool_pc)

    --         return e

    if  | TyCon tn _:ts <- unTyApp t
        , Just adt <- M.lookup tn tenv -> do
            let dcs = dataCon adt
            bindee_id <- freshIdN TyLitInt

            let bound = boundIds adt
                bound_ts = zip bound ts

                ty_apped_dcs = map (\dc -> mkApp $ Data dc:map Type ts) dcs
            
            apped_dcs <- mapM (\dc -> do
                                    let anon_ts = anonArgumentTypes dc
                                        re_anon = foldr (\(i, t) -> retype i t) anon_ts bound_ts

                                    ars <- freshIdsN re_anon

                                    return (HS.fromList ars, mkApp $ dc:map Var ars)) ty_apped_dcs
            return apped_dcs
        | otherwise -> error $ "allDCs: type not found"
allDCs _ _ = error $ "allDCs: type not found"


arbDCCase :: Id -> StateNG t Expr
arbDCCase i@(Id _ t) = do
    kv <- knownValues
    bool <- tyBoolT

    if  | (PresType t) .:: bool -> do
            let tre@(Data tre_dc) = mkTrue kv
                flse@(Data flse_dc) = mkFalse kv

            bindee_id <- freshIdN TyLitInt
            let bindee = Var bindee_id
            let pc = mkBounds bindee 1 2
                bool_pc = [ PC.mkAssumePC bindee_id 1 $ ExtCond (Var i) True
                          , PC.mkAssumePC bindee_id 2 $ ExtCond (Var i) False ]
                e = Case bindee bindee_id
                        [ Alt (LitAlt (LitInt 1)) tre
                        , Alt (LitAlt (LitInt 2)) flse]

            insertSymbolicE (idName bindee_id) bindee_id
            insertSymbolicId bindee_id
            mapM_ insertPCStateNG (pc ++ bool_pc)

            return e

        | TyCon tn _:ts <- unTyApp t -> do
            m_adt <- lookupT tn
            case m_adt of
                Just adt -> do
                    let dcs = dataCon adt
                    bindee_id <- freshIdN TyLitInt

                    let bound = boundIds adt
                        bound_ts = zip bound ts

                        ty_apped_dcs = map (\dc -> mkApp $ Data dc:map Type ts) dcs
                    
                    apped_dcs <- mapM (\dc -> do
                                            let anon_ts = anonArgumentTypes dc
                                                re_anon = foldr (\(i, t) -> retype i t) anon_ts bound_ts

                                            ars <- freshIdsN re_anon
                                            mapM (\a -> insertSymbolicE (idName a) a) ars
                                            mapM insertSymbolicId ars

                                            return (mkApp $ dc:map Var ars)) ty_apped_dcs

                    let bindee = Var bindee_id
                    let pc = mkBounds bindee 1 (toInteger $ length dcs)
                        e = createCaseExpr bindee_id apped_dcs
                    
                    insertSymbolicE (idName bindee_id) bindee_id
                    insertSymbolicId bindee_id
                    mapM_ insertPCStateNG pc

                    return e
                Nothing -> error $ "arbDCCase: type not found"
        | otherwise -> error $ "arbDCCase: type not found"
arbDCCase _ = error $ "arbDCCase: type not found"

