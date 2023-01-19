{-# LANGUAGE OverloadedStrings, TupleSections #-}

module G2.Liquid.Inference.ToSMTHorn (toSMTHorn) where

import G2.Liquid.Inference.Config
import G2.Liquid.Inference.Verify
import G2.Liquid.Types
import G2.Solver

import qualified Language.Fixpoint.Types.Config as LHC
import Language.Fixpoint.Types.Environments ( elemsIBindEnv )
import Language.Fixpoint.Solver
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Types
        hiding (TargetInfo (..), TargetSrc (..), TargetSpec (..), GhcSrc (..), GhcSpec (..))
import Language.Fixpoint.Types.Visitor as V

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.Maybe
import qualified Data.Text as T
import qualified Text.Builder as TB

import Debug.Trace

toSMTHorn :: InferenceConfig -> Config ->  [GhcInfo] -> IO ()
toSMTHorn infconfig cfg ghci = do
    getFInfo infconfig cfg ghci
    return ()

getFInfo :: InferenceConfig -> Config ->  [GhcInfo] -> IO (F.SInfo Cinfo)
getFInfo infconfig cfg ghci = do
    (_, orig_finfo) <- verify' infconfig cfg ghci
    finfo <- simplifyFInfo LHC.defConfig orig_finfo
    let senv = F.bs finfo
        wf = F.ws finfo
    putStrLn "hornCons"
    mapM_ hornCons wf
    let ghc_types_pkvars = ghcTypesPKVars $ HM.elems wf
        cleaned_wf = elimPKVarsWF ghc_types_pkvars wf
        cleaned_senv = elimPKVars ghc_types_pkvars senv
        cleaned_cm = map (elimPKVars ghc_types_pkvars) $ HM.elems $ F.cm finfo
        clauses = map (toHorn cleaned_senv) cleaned_cm
    putStrLn "gLits"
    print $ F.gLits finfo
    putStrLn "dLits"
    print $ F.dLits finfo
    putStrLn "wf"
    mapM_ (\(kvar, wfc) ->
                    putStrLn $ "kvar = " ++ show kvar
                ++ "\nwrft = " ++ show (F.wrft wfc)
                ++ "\nwinfo = " ++ show (F.wrft wfc)) $ HM.toList cleaned_wf
    putStrLn "toHorn"
    print $ map (\(f, _, _) -> f) clauses
    putStrLn "toHorn rhs"
    print $ map (\(_, r, _) -> r) clauses
    putStrLn "SMT"
    let smt_headers = map (Assert . (\(_, _, smt) -> smt)) clauses
    putStrLn . T.unpack . TB.run $ toSolverText smt_headers
    return finfo

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

hornCons :: F.WfC Cinfo -> IO ()
hornCons (F.WfC { F.wenv = env, F.wrft = rft, F.winfo = info }) = do
    putStrLn "----"
    print $ elemsIBindEnv env
    print rft
    print info

toHorn :: F.BindEnv -> F.SimpC Cinfo -> ([(F.Symbol, F.SortedReft)], F.Expr, SMTAST)
toHorn bind subC =
    let env = F._cenv subC
        -- lhs = F.clhs subC
        rhs = F._crhs subC
        foralls = filter (not . F.isFunctionSortedReft . snd)
                . filter (not . sortNameHasPrefix "GHC.Types" . F.sr_sort . snd)
                . filter (\(_, rr) -> F.sr_sort rr /= F.FTC (F.strFTyCon))
                $ map (`F.lookupBindEnv` bind) (elemsIBindEnv env)
        foralls_unfilter = map (`F.lookupBindEnv` bind) (elemsIBindEnv env)

        (lhs_smt, ms) = unzip
                      . map (\(smt, smts, m') -> (SmtAnd (smt:smts), m'))
                      $ map (uncurry rrToSMTAST) . zip [1..] $ map snd foralls -- ++ [lhs]
        m = mconcat ms
        (rhs_smt, rhs_smts, rhs_m) = toSMTAST m rhs

        forall = ForAll (concatMap HM.elems $ rhs_m:ms)
    in
    trace ("foralls = " ++ show foralls_unfilter ++ "\nlhs_smt = " ++ show lhs_smt ++ "\nrhs_smt = " ++ show rhs_smt)
    (foralls, rhs, forall (SmtAnd (lhs_smt ++ rhs_smts) :=> rhs_smt))

sortNameHasPrefix :: String -> F.Sort -> Bool
sortNameHasPrefix prefix eapp | F.FTC h:_ <- F.unFApp eapp =
    let
        h_symb = F.symbol h
    in
    isPrefixOf prefix (F.symbolSafeString h_symb)
sortNameHasPrefix _ _ = False

rrToSMTAST :: Int -> F.SortedReft -> (SMTAST, [SMTAST], HM.HashMap SMTName (SMTName, Sort))
rrToSMTAST i rr =
    let
        m = sortedReftToMap i rr
        (smt, smts, m') = toSMTAST m (F.expr rr)
    in
    (smt, smts, HM.union m m')

sortedReftToMap :: Int -> F.SortedReft -> HM.HashMap SMTName (SMTName, Sort)
sortedReftToMap i (F.RR { F.sr_sort = sort, F.sr_reft = F.Reft (sym, _) }) =
    let
        nme = F.symbolSafeString sym
    in
    HM.singleton nme (nme ++ "_G2_" ++ show i, lhSortToSMTSort sort)

toSMTAST :: HM.HashMap SMTName (SMTName, Sort) -> F.Expr -> (SMTAST, [SMTAST], HM.HashMap SMTName (SMTName, Sort))
toSMTAST m e =
    let
        (e', es, m') = appRep e
    in
    (toSMTAST' m SortBool e', map (toSMTAST' m SortBool) es, m')

appRep :: F.Expr -> (F.Expr, [F.Expr], HM.HashMap SMTName (SMTName, Sort))
appRep e =
    let
        apps_rep = HM.fromList
                 . filter (relApp . fst)
                 . zip (V.eapps e)
                 . map F.symbol
                 . map ("__G2__meas_r__" ++)
                 $ map show [0..]

        meas_apps = map (\(me, n) -> F.EApp me (F.EVar n)) . HM.toList $ apps_rep

        names = HM.fromList . map (\kv@(k, _) -> (k, kv)) $ map (,SortInt) . map F.symbolSafeString $ HM.elems apps_rep
    in
    (repExpr apps_rep e, meas_apps, names)
    where
        relApp (F.EApp (F.EApp _ _) _) = True
        relApp _ = False

repExpr :: Visitable e => HM.HashMap F.Expr F.Symbol -> e -> e
repExpr hm = mapExpr go
    where
        go e | Just r <- HM.lookup e hm = F.ECst (F.EVar r) F.FInt
             | otherwise = e

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

toSMTAST' m _ (F.PAtom atom e1 e2) =
    let
        sort = case (predictSort m e1, predictSort m e2) of
                (Just s1, _) -> s1
                (_, Just s2) -> s2
                (Nothing, Nothing) -> error $ "toSMTAST': cannot calculate sort\n" ++ show e1 ++ "\n" ++ show e2
    in
    toSMTASTAtom atom (toSMTAST' m sort e1) (toSMTAST' m sort e2)
toSMTAST' _ _ (F.PAnd []) = VBool True
toSMTAST' m _ (F.PAnd xs) = SmtAnd $ map (toSMTAST' m SortBool) xs
toSMTAST' m _ (F.PNot e) = (:!) (toSMTAST' m SortBool e)
toSMTAST' m _ pkvar@(F.PKVar k (F.Su subst)) | [(_, arg)] <- HM.toList subst =
                        Func (F.symbolSafeString . F.kv $ k) [toSMTAST' m SortInt arg]

toSMTAST' _ sort e = error $ "toSMTAST: unsupported " ++ show e ++ "\n" ++ show sort

toSMTASTAtom :: F.Brel -> SMTAST -> SMTAST -> SMTAST
toSMTASTAtom (F.Eq) = (:=)
toSMTASTAtom (F.Gt) = (:>)
toSMTASTAtom (F.Ge) = (:>=)
toSMTASTAtom atom = error $ "toSMTASTAtom: unsupported " ++ show atom

toSMTASTOp :: F.Bop -> SMTAST -> SMTAST -> SMTAST
toSMTASTOp F.Plus = (:+)
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
predictSort _ (F.PAtom _ _ _) = Just SortBool
predictSort _ (F.PAnd _) = Just SortBool
predictSort _ (F.PNot _) = Just SortBool
predictSort _ e = error $ "predictSort: unsupported " ++ show e

giInfo :: F.SubC Cinfo -> String
giInfo sc =
  "F.SubC Cinfo " ++ "\n_senv = " ++ show (elemsIBindEnv $ F.senv sc) ++ "\nslhs = " ++ show (F.slhs sc) ++ "\nsrhs = " ++ show (F.srhs sc)
                      ++ "\n_sid = " ++ show (F.sid sc) ++ "\n_stag = " ++ show (F.stag sc) ++ "\n_sinfo = " ++ show (F.sinfo sc)
