{-# LANGUAGE OverloadedStrings, TupleSections #-}

module G2.Liquid.Inference.ToSMTHorn (toSMTHorn) where

import G2.Liquid.Inference.Config
import G2.Liquid.Inference.Verify
import G2.Liquid.Types ( GhcInfo, gsData, giSpec )
import G2.Solver

import qualified Language.Fixpoint.Types.Config as LHC
import Language.Fixpoint.Types.Environments ( elemsIBindEnv )
import Language.Fixpoint.Solver
import Language.Fixpoint.SortCheck
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Types
        hiding (TargetInfo (..), TargetSrc (..), TargetSpec (..), GhcSrc (..), GhcSpec (..))
import Language.Fixpoint.Types.Visitor as V

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.Maybe
import Data.Ord
import qualified Data.Text as T
import qualified Text.Builder as TB

import Debug.Trace

toSMTHorn :: InferenceConfig -> Config ->  [GhcInfo] -> IO ()
toSMTHorn infconfig cfg ghci = do
    getFInfo infconfig cfg ghci
    return ()

getFInfo :: InferenceConfig -> Config ->  [GhcInfo] -> IO (F.SInfo Cinfo)
getFInfo infconfig cfg ghci = do
    let meas = measureSpecs ghci
    print meas

    (_, orig_finfo) <- verify' infconfig cfg ghci
    finfo <- simplifyFInfo LHC.defConfig orig_finfo
    let senv = F.bs finfo
        ws = F.ws finfo
    putStrLn "hornCons"
    mapM_ hornCons ws
    let ghc_types_pkvars = ghcTypesPKVars $ HM.elems ws
        
        cleaned_wf = elimPKVarsWF ghc_types_pkvars ws
        cleaned_senv = elimPKVars ghc_types_pkvars senv

        wf_decl = map (wfDecl cleaned_senv) $ HM.elems cleaned_wf

        cleaned_cm = map (elimPKVars ghc_types_pkvars) $ HM.elems $ F.cm finfo
        clauses = map (toHorn meas cleaned_senv) cleaned_cm
    putStrLn "ws"
    print ws
    -- mapM_ (\(kvar, wfc) ->
    --                 putStrLn $ "kvar = " ++ show kvar
    --             ++ "\nwrft = " ++ show (F.wrft wfc)
    --             ++ "\nwinfo = " ++ show (F.wrft wfc)) $ HM.toList ws
    putStrLn "toHorn"
    mapM_ (\(f, r, _) -> do
            putStrLn $ "foralls = " ++ show f
            putStrLn $ "rhs = " ++ show r) clauses
    putStrLn "SMT"
    let smt_headers = wf_decl ++ map (Assert . (\(_, _, smt) -> smt)) clauses
    putStrLn . T.unpack . TB.run $ toSolverText smt_headers
    return finfo
    where
        measureSpecs :: [GhcInfo] -> [F.Symbol]
        measureSpecs = map (F.symbol . msName) . concatMap (gsMeasures . gsData . giSpec)


ghcTypesPKVars :: [F.WfC a] -> HS.HashSet F.KVar
ghcTypesPKVars = HS.fromList . mapMaybe go
    where
        go F.WfC { F.wrft = (_, sort, n) } | sortNameHasPrefix "GHC.Types" sort = Just n
        go _ = Nothing

elimPKVarsWF :: HS.HashSet F.KVar -> HM.HashMap F.KVar a -> HM.HashMap F.KVar a
elimPKVarsWF kvars = HM.filterWithKey (\kvar _ -> not $ HS.member kvar kvars)

elimPKVars  :: Visitable t => HS.HashSet F.KVar -> t -> t
elimPKVars kvars = mapExpr (elimPKVarsExpr kvars)

elimPKVarsExpr :: HS.HashSet F.KVar -> F.Expr -> F.Expr
elimPKVarsExpr pkvars (F.PKVar v _) | HS.member v pkvars = F.PTrue
elimPKVarsExpr _ e = e

wfDecl :: F.BindEnv -> F.WfC a -> SMTHeader
wfDecl bind wfc =
    let
        env = F.wenv wfc
        bound = map (`F.lookupBindEnv` bind) (elemsIBindEnv env)
        bound_sorts = map (F.sr_sort . snd)  $ sortBy (comparing fst) bound
        (_, s, kvar) = F.wrft wfc
    in
    DeclareFun (F.symbolSafeString $ F.kv kvar) ([lhSortToSMTSort s] ++ map lhSortToSMTSort bound_sorts) SortBool

hornCons :: F.WfC Cinfo -> IO ()
hornCons (F.WfC { F.wenv = env, F.wrft = rft, F.winfo = info }) = do
    putStrLn "----"
    print $ elemsIBindEnv env
    print rft
    print info

toHorn :: [F.Symbol] -> F.BindEnv -> F.SimpC Cinfo -> ([(F.Symbol, F.SortedReft)], F.Expr, SMTAST)
toHorn meas bind subC =
    let env = F._cenv subC
        -- lhs = F.clhs subC
        rhs = F._crhs subC

        foralls_binds = map (`F.lookupBindEnv` bind) (elemsIBindEnv env)
        foralls = filter (\(n, _) -> n /= "GHC.Types.True" && n /= "GHC.Types.False")
                . filter (not . F.isFunctionSortedReft . snd)
                . filter (not . sortNameHasPrefix "GHC.Types" . F.sr_sort . snd)
                . filter (not . sortNameHasPrefix "GHC.Classes.Ord" . F.sr_sort . snd)
                . filter (not . sortNameHasPrefix "GHC.Num" . F.sr_sort . snd)
                . filter (\(_, rr) -> F.sr_sort rr /= F.FTC (F.strFTyCon))
                $ foralls_binds

        ms = foldr (\(i, (n, sr)) m -> sortedReftToMap i n m sr) HM.empty $ zip [1..] foralls
        (lhs_smt, ms') = unzip
                      . map (\(smt, smts, m) -> (SmtAnd (smt:smts), m))
                      $ map (\(i, (n, sr)) -> rrToSMTAST meas (show i) ms sr) $ zip [1..] foralls -- ++ [lhs]
        (rhs_smt, rhs_smts, rhs_m) = toSMTAST meas "rhs_val" (mconcat ms') rhs

        forall = ForAll . nub . concatMap HM.elems $ rhs_m:ms'
    in
    (foralls, rhs, forall (SmtAnd (lhs_smt ++ rhs_smts) :=> rhs_smt))

sortNameHasPrefix :: String -> F.Sort -> Bool
sortNameHasPrefix prefix eapp | F.FTC h:_ <- F.unFApp eapp =
    let
        h_symb = F.symbol h
    in
    isPrefixOf prefix (F.symbolSafeString h_symb)
sortNameHasPrefix _ _ = False

rrToSMTAST :: [F.Symbol] -> String -> HM.HashMap SMTName (SMTName, Sort) -> F.SortedReft -> (SMTAST, [SMTAST], HM.HashMap SMTName (SMTName, Sort))
rrToSMTAST meas fresh m rr =
    let
        (smt, smts, m') = toSMTAST meas fresh m (F.expr rr)
    in
    (smt, smts, HM.union m m')

sortedReftToMap :: Int -> F.Symbol -> HM.HashMap SMTName (SMTName, Sort) -> F.SortedReft -> HM.HashMap SMTName (SMTName, Sort)
sortedReftToMap i symb1 m (F.RR { F.sr_sort = sort, F.sr_reft = F.Reft (symb2, _) })
    | Just smt_nme_srt <- HM.lookup nme1 m =
    --    trace ("---\nnme1 = " ++ nme1 ++ "\nnme2 = " ++ nme2 ++ "\nsmt_nme_srt = " ++ show smt_nme_srt)
       HM.insert nme1 smt_nme_srt $ HM.insert nme2 smt_nme_srt m
    | otherwise =
        let
            smt_nme = nme2 ++ "_G2_" ++ show i
            smt_sort = lhSortToSMTSort sort
        in
        HM.insert nme1 (smt_nme, smt_sort) $ HM.insert nme2 (smt_nme, smt_sort) m
    where
        nme1 = F.symbolSafeString symb1
        nme2 = F.symbolSafeString symb2

toSMTAST :: [F.Symbol] -> String -> HM.HashMap SMTName (SMTName, Sort) -> F.Expr -> (SMTAST, [SMTAST], HM.HashMap SMTName (SMTName, Sort))
toSMTAST meas fresh m e =
    let
        (e', es, m') = appRep meas fresh e
    in
    (toSMTAST' m SortBool e', map (toSMTAST' m SortBool) es, m')

appRep :: [F.Symbol] -> String -> F.Expr -> (F.Expr, [F.Expr], HM.HashMap SMTName (SMTName, Sort))
appRep meas fresh e =
    let
        apps_rep = HM.fromList
                --  . filter (relApp . fst)
                 . zip (topEApps e)
                 . map F.symbol
                 . map (\i -> "__G2__meas_r__" ++ fresh ++ "__" ++ i)
                 $ map show [0..]

        meas_apps = map (\(me, n) -> F.EApp me (F.EVar n)) $ HM.toList apps_rep

        ns = HM.fromList
           . map (\kv@(k, _) -> (k, kv))
           . map (\(e, s) -> (s, lhSortToSMTSort $ getSort e))
           . map (\(e, s) -> (e, F.symbolSafeString s))
           $ HM.toList apps_rep
    in
    (repExpr apps_rep e, meas_apps, ns)
    where
        relApp (F.EApp (F.EApp _ (F.ECst (F.EVar n) _)) _) | n `elem` meas = True
        relApp _ = False

getSort :: F.Expr -> F.Sort
getSort eapp@(F.EApp e _) =
    case getSort e of
        F.FFunc _ s -> s
        s -> s
getSort (F.ECst _ s) = s
getSort e = error $ "getSort: Unsupported" ++ show e

repExpr ::  HM.HashMap F.Expr F.Symbol -> F.Expr -> F.Expr
repExpr hm = mapExprTD go
    where
        go e | Just r <- HM.lookup e hm = F.ECst (F.EVar r) F.FInt
             | otherwise = e

mapExprTD :: (F.Expr -> F.Expr) -> F.Expr -> F.Expr
mapExprTD f = go
    where
        go e0 = case f e0 of
                F.EApp fx x -> F.EApp (go fx) (go x)
                F.ENeg e -> F.ENeg (go e)
                F.EBin b e1 e2 -> F.EBin b (go e1) (go e2)
                F.EIte p e1 e2 -> F.EIte (go p) (go e1) (go e2)
                F.ECst e t -> F.ECst (go e) t
                F.PAnd ps -> F.PAnd $ map go ps
                F.POr ps -> F.POr $ map go ps
                F.PNot p -> F.PNot (go p)
                F.PImp p1 p2 -> F.PImp (go p1) (go p2)
                F.PIff p1 p2 -> F.PIff (go p1) (go p2)
                F.PAtom r e1 e2 -> F.PAtom r (go e1) (go e2)
                e@F.PKVar {} -> e
                e@F.EVar {} -> e
                e@F.ESym {} -> e
                e@F.ECon {} -> e
                e -> error $ "mapExprTD: unsupported " ++ show e

topEApps :: F.Expr -> [F.Expr]
topEApps eapp@(F.EApp _ _) = [eapp]
topEApps (F.ENeg e) = topEApps e
topEApps (F.EBin b e1 e2) = topEApps e1 ++ topEApps e2
topEApps (F.EIte p e1 e2) = topEApps p ++ topEApps e1 ++ topEApps e2
topEApps (F.ECst e t) = topEApps e
topEApps (F.PAnd ps) = concatMap topEApps ps
topEApps (F.POr ps) = concatMap topEApps ps
topEApps (F.PNot p) = topEApps p
topEApps (F.PImp p1 p2) = topEApps p1 ++ topEApps p2
topEApps (F.PIff p1 p2) = topEApps p1 ++ topEApps p2
topEApps (F.PAtom _ e1 e2) = topEApps e1 ++ topEApps e2
topEApps F.PKVar {} = []
topEApps F.EVar {} = []
topEApps F.ESym {} = []
topEApps F.ECon {} = []
topEApps e = error $ "mapExprTD: unsupported " ++ show e

toSMTAST' :: HM.HashMap SMTName (SMTName, Sort) -> Sort -> F.Expr -> SMTAST
toSMTAST' m sort (F.EVar v) | Just (fv, _) <- HM.lookup (F.symbolSafeString v) m = V fv sort
                            | otherwise = V (F.symbolSafeString v) sort
toSMTAST' _ _ (F.ECon (F.I i)) = VInt i
toSMTAST' m sort (F.EBin op e1 e2) =
    toSMTASTOp op (toSMTAST' m sort e1) (toSMTAST' m sort e2)
toSMTAST' m _ (F.ECst v@(F.EVar _) s) = toSMTAST' m (lhSortToSMTSort s) v
toSMTAST' m _ (F.ECst e s) = toSMTAST' m (lhSortToSMTSort s) e

-- Handle measures
toSMTAST' m _ eapp@(F.EApp
                    (F.EApp
                        (F.EApp
                            (F.ECst (F.EVar "apply") _)
                            (F.ECst (F.EVar meas) _)
                        ) 
                        (F.ECst arg1@(F.EVar _) arg_s)
                    )
                    arg2
              ) = Func (F.symbolSafeString meas) [toSMTAST' m (lhSortToSMTSort arg_s) arg1, toSMTAST' m SortInt arg2]
toSMTAST' m _ eapp@(F.EApp {}) | (F.ECst (F.EVar f) _:es) <- splitApplyApp eapp =
    Func (F.symbolSafeString f) $ map (toSMTAST' m (error "expected ECst")) es
toSMTAST' m _ eapp@(F.EApp {}) | (F.EVar f:es) <- splitApplyApp eapp =
    Func (F.symbolSafeString f) $ map (toSMTAST' m (error "expected ECst")) es
    -- error $ "toSMTAST': \neapp = " ++ show eapp ++ "\nes = " ++ show es -- (func, xs@(_:_)) <- F.splitEApp eapp = error $ "toSMTAST': eapp = " ++ show eapp ++ "\nfunc = " ++ show func ++ "\nxs = " ++ show xs

toSMTAST' m _ (F.PAtom atom e1 e2) =
    let
        sort = case (predictSort m e1, predictSort m e2) of
                (Just s1, _) -> s1
                (_, Just s2) -> s2
                (Nothing, Nothing) -> error $ "toSMTAST': cannot calculate sort\n" ++ show e1 ++ "\n" ++ show e2
    in
    toSMTASTAtom atom (toSMTAST' m sort e1) (toSMTAST' m sort e2)
toSMTAST' _ _ (F.POr []) = VBool False
toSMTAST' _ _ (F.PAnd []) = VBool True
toSMTAST' m _ (F.PAnd xs) = SmtAnd $ map (toSMTAST' m SortBool) xs
toSMTAST' m _ (F.PNot e) = (:!) (toSMTAST' m SortBool e)
toSMTAST' m _ (F.PIff e1 e2) = toSMTAST' m SortBool e1 :<=> toSMTAST' m SortBool e2
toSMTAST' m _ (F.PKVar k (F.Su subst)) =
    let
        args = map snd . sortBy (comparing fst) $ HM.toList subst
    in
    Func (F.symbolSafeString . F.kv $ k) $ map (toSMTAST' m SortInt) args

toSMTAST' _ sort e = error $ "toSMTAST: unsupported " ++ show e ++ "\n" ++ show sort

splitApplyApp :: F.Expr -> [F.Expr]
splitApplyApp eapp | (F.ECst (F.EVar "apply") _, h:xs) <- F.splitEApp eapp = splitApplyApp h ++ xs
splitApplyApp eapp | (h, xs@(_:_)) <- F.splitEApp eapp = h:xs
splitApplyApp (F.ECst e _) = splitApplyApp e 
splitApplyApp e = [e]

toSMTASTAtom :: F.Brel -> SMTAST -> SMTAST -> SMTAST
toSMTASTAtom (F.Ueq) = (:=)
toSMTASTAtom (F.Eq) = (:=)
toSMTASTAtom (F.Ne) = (:/=)
toSMTASTAtom (F.Gt) = (:>)
toSMTASTAtom (F.Ge) = (:>=)
toSMTASTAtom (F.Lt) = (:<)
toSMTASTAtom (F.Le) = (:<=)
toSMTASTAtom atom = error $ "toSMTASTAtom: unsupported " ++ show atom

toSMTASTOp :: F.Bop -> SMTAST -> SMTAST -> SMTAST
toSMTASTOp F.Plus = (:+)
toSMTASTOp F.Minus = (:-)
toSMTASTOp op = error $ "toSMTASTOp: unsupported " ++ show op

lhSortToSMTSort :: F.Sort -> Sort
lhSortToSMTSort F.FInt = SortInt
lhSortToSMTSort (F.FObj s) = SortVar (F.symbolSafeString s)
lhSortToSMTSort eapp | F.FTC h:es <- F.unFApp eapp =
    let
        h_symb = F.symbolSafeString $ F.symbol h
    in
    case h_symb of
        "bool" -> SortBool
        _ -> SortDC h_symb $ map lhSortToSMTSort es
lhSortToSMTSort (F.FAbs _ _) = SortVar "FAbs" 
lhSortToSMTSort (F.FFunc _ _) = SortVar "FFunc" 
lhSortToSMTSort sort = error $ "lhSortToSMTSort: unsupported " ++ show sort

predictSort :: HM.HashMap SMTName (SMTName, Sort) -> F.Expr -> Maybe Sort
predictSort _ (F.ESym _) = Nothing
predictSort m (F.EVar v) = snd <$> HM.lookup (F.symbolSafeString v) m
predictSort _ (F.ECst _ s) = Just $ lhSortToSMTSort s
predictSort _ (F.PAtom _ _ _) = Just SortBool
predictSort _ (F.PAnd _) = Just SortBool
predictSort _ (F.PNot _) = Just SortBool
predictSort _ e = error $ "predictSort: unsupported " ++ show e

giInfo :: F.SubC Cinfo -> String
giInfo sc =
  "F.SubC Cinfo " ++ "\n_senv = " ++ show (elemsIBindEnv $ F.senv sc) ++ "\nslhs = " ++ show (F.slhs sc) ++ "\nsrhs = " ++ show (F.srhs sc)
                      ++ "\n_sid = " ++ show (F.sid sc) ++ "\n_stag = " ++ show (F.stag sc) ++ "\n_sinfo = " ++ show (F.sinfo sc)
