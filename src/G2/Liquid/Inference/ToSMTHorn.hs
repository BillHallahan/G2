{-# LANGUAGE OverloadedStrings #-}

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
import Language.Fixpoint.Types.Visitor

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.Maybe
import qualified Data.Text as T
import qualified Text.Builder as TB

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
    putStrLn "wf"
    mapM_ (\(kvar, wfc) ->
                    putStrLn $ "kvar = " ++ show kvar
                ++ "\nwrft = " ++ show (F.wrft wfc)
                ++ "\nwinfo = " ++ show (F.wrft wfc)) $ HM.toList wf
    putStrLn "hornCons"
    mapM_ hornCons wf
    putStrLn "toHorn"
    let ghc_types_pkvars = ghcTypesPKVars $ HM.elems wf
        cleaned_senv = elimPKVars ghc_types_pkvars senv
        cleaned_cm = map (elimPKVars ghc_types_pkvars) $ HM.elems $ F.cm finfo
        clauses = map (toHorn cleaned_senv) cleaned_cm
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

        (lhs_smt, ms) = unzip $ map (uncurry rrToSMTAST) . zip [1..] $ map snd foralls -- ++ [lhs]
        m = mconcat ms
        rhs_smt = toSMTAST m rhs

        forall = ForAll (HM.elems m)
    in
    (foralls, rhs, forall (SmtAnd lhs_smt :=> rhs_smt))

sortNameHasPrefix :: String -> F.Sort -> Bool
sortNameHasPrefix prefix eapp | F.FTC h:_ <- F.unFApp eapp =
    let
        h_symb = F.symbol h
    in
    isPrefixOf prefix (F.symbolSafeString h_symb)
sortNameHasPrefix _ _ = False

rrToSMTAST :: Int -> F.SortedReft -> (SMTAST, HM.HashMap SMTName (SMTName, Sort))
rrToSMTAST i rr =
    let
        m = sortedReftToMap i rr
    in
    (toSMTAST m (F.expr rr), m)

sortedReftToMap :: Int -> F.SortedReft -> HM.HashMap SMTName (SMTName, Sort)
sortedReftToMap i (F.RR { F.sr_sort = sort, F.sr_reft = F.Reft (sym, _) }) =
    let
        nme = F.symbolSafeString sym
    in
    HM.singleton nme (nme ++ "_G2_" ++ show i, lhSortToSMTSort sort)

toSMTAST :: HM.HashMap SMTName (SMTName, Sort) -> F.Expr -> SMTAST
toSMTAST m = toSMTAST' m SortBool

toSMTAST' :: HM.HashMap SMTName (SMTName, Sort) -> Sort -> F.Expr -> SMTAST
toSMTAST' m sort (F.EVar v) | Just (fv, _) <- HM.lookup (F.symbolSafeString v) m = V fv sort
                            | otherwise = V (F.symbolSafeString v) sort
toSMTAST' _ _ (F.ECon (F.I i)) = VInt i
toSMTAST' m sort (F.EBin op e1 e2) =
    toSMTASTOp op (toSMTAST' m sort e1) (toSMTAST' m sort e2)
toSMTAST' m _ (F.ECst (F.EVar v) s) = V (F.symbolSafeString v) (lhSortToSMTSort s)
toSMTAST' m _ (F.ECst e s) = toSMTAST' m (lhSortToSMTSort s) e

-- Handle measures
toSMTAST' m _ eapp@(F.EApp
                    (F.EApp
                        (F.ECst (F.EVar "apply") _)
                        (F.ECst (F.EVar meas) _)
                    ) 
                    (F.ECst arg@(F.EVar _) arg_s)
              ) = Func (F.symbolSafeString meas) [toSMTAST' m (lhSortToSMTSort arg_s) arg]

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
lhSortToSMTSort eapp | F.FTC h:es <- F.unFApp eapp=
    let
        h_symb = F.symbol h
    in
    SortDC (F.symbolSafeString h_symb) $ map lhSortToSMTSort es
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
