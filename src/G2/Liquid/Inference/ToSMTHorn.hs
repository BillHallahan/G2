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

import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T
import Language.Haskell.Liquid.Constraint.Types (SubC(lhs))

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
    let clauses = map (toHorn senv) (HM.elems $ F.cm finfo)
    print $ map (\(f, r, _) -> (f, r)) clauses
    print clauses
    return finfo

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
                . filter (\(_, rr) -> F.sr_sort rr /= F.FTC (F.strFTyCon))
                $ map (`F.lookupBindEnv` bind) (elemsIBindEnv env)

        lhs_smt = map rrToSMTAST $ map snd foralls -- ++ [lhs]
        m = mconcat $ map (sortedReftToMap . snd) foralls
        rhs_smt = toSMTAST m rhs -- rrToSMTAST rhs
    in
    (foralls, rhs, SmtAnd lhs_smt :=> rhs_smt)


rrToSMTAST :: F.SortedReft -> SMTAST
rrToSMTAST rr = toSMTAST (sortedReftToMap rr) (F.expr rr)

sortedReftToMap :: F.SortedReft -> HM.HashMap SMTName Sort
sortedReftToMap (F.RR { F.sr_sort = sort, F.sr_reft = F.Reft (sym, _) }) =
    HM.singleton (F.symbolSafeString sym) (lhSortToSMTSort sort) 

toSMTAST :: HM.HashMap SMTName Sort -> F.Expr -> SMTAST
toSMTAST m = toSMTAST' m SortBool

toSMTAST' :: HM.HashMap SMTName Sort -> Sort -> F.Expr -> SMTAST
toSMTAST' m sort (F.EVar v) = V (F.symbolSafeString v) sort
toSMTAST' _ _ (F.ECon (F.I i)) = VInt i
toSMTAST' m sort (F.EBin op e1 e2) =
    toSMTASTOp op (toSMTAST' m sort e1) (toSMTAST' m sort e2)
toSMTAST' m _ (F.ECst e s) = toSMTAST' m (lhSortToSMTSort s) e
toSMTAST' m _ (F.PAtom atom e1 e2) =
    let
        sort = case (predictSort m e1, predictSort m e2) of
                (Just s1, _) -> s1
                (_, Just s2) -> s2
                (Nothing, Nothing) -> error $ "toSMTAST': cannot calculate sort\n" ++ show e1 ++ "\n" ++ show e2
    in
    toSMTASTAtom atom (toSMTAST' m sort e1) (toSMTAST' m sort e2)
toSMTAST' _ _ (F.PAnd []) = VBool True
toSMTAST' m _ (F.PNot e) = (:!) (toSMTAST' m SortBool e)
toSMTAST' m _ pkvar@(F.PKVar k (F.Su subst)) | [(_, arg)] <- HM.toList subst =
                        Func (F.symbolSafeString . F.kv $ k) [toSMTAST' m SortInt arg]
toSMTAST' _ sort e = error $ "toSMTAST: unsupported " ++ show e ++ "\n" ++ show sort

toSMTASTAtom :: F.Brel -> SMTAST -> SMTAST -> SMTAST
toSMTASTAtom (F.Eq) = (:=)
toSMTASTAtom (F.Gt) = (:>)
toSMTASTAtom atom = error $ "toSMTASTAtom: unsupported " ++ show atom

toSMTASTOp :: F.Bop -> SMTAST -> SMTAST -> SMTAST
toSMTASTOp F.Plus = (:+)
toSMTASTOp op = error $ "toSMTASTOp: unsupported " ++ show op

lhSortToSMTSort :: F.Sort -> Sort
lhSortToSMTSort F.FInt = SortInt
lhSortToSMTSort sort = error $ "lhSortToSMTSort: unsupported " ++ show sort

predictSort :: HM.HashMap SMTName Sort -> F.Expr -> Maybe Sort
predictSort _ (F.ESym _) = Nothing
predictSort m (F.EVar v) = HM.lookup (F.symbolSafeString v) m
predictSort _ (F.PAtom _ _ _) = Just SortBool
predictSort _ (F.PAnd _) = Just SortBool
predictSort _ (F.PNot _) = Just SortBool
predictSort _ e = error $ "predictSort: unsupported " ++ show e

giInfo :: F.SubC Cinfo -> String
giInfo sc =
  "F.SubC Cinfo " ++ "\n_senv = " ++ show (elemsIBindEnv $ F.senv sc) ++ "\nslhs = " ++ show (F.slhs sc) ++ "\nsrhs = " ++ show (F.srhs sc)
                      ++ "\n_sid = " ++ show (F.sid sc) ++ "\n_stag = " ++ show (F.stag sc) ++ "\n_sinfo = " ++ show (F.sinfo sc)
