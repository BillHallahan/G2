{-# LANGUAGE OverloadedStrings, TupleSections #-}

module G2.Liquid.Inference.ToSMTHorn (toSMTHorn) where

import G2.Liquid.Inference.Config
import G2.Liquid.Inference.Verify ( verify' )
import G2.Liquid.Types ( GhcInfo, gsData, giSrc, giSpec )
import G2.Solver

import qualified Language.Fixpoint.Types.Config as LHC
import Language.Fixpoint.Types.Environments ( elemsIBindEnv )
import Language.Fixpoint.Solver
import Language.Fixpoint.SortCheck
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Types
        hiding (TargetInfo (..), GhcSrc (..), GhcSpec (..), gsData)
import Language.Fixpoint.Types.Visitor as V

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.Maybe
import Data.Ord
import qualified Data.Text as T
import qualified Text.Builder as TB

import DataCon
import GHC
import Name
import Var as V

import Debug.Trace
import G2.Liquid.Inference.Sygus.SpecInfo (Forms(BoolForm))
import Language.Fixpoint.Types (splitEApp)

toSMTHorn :: InferenceConfig -> Config ->  [GhcInfo] -> IO ()
toSMTHorn infconfig cfg ghci = do
    getFInfo infconfig cfg ghci
    return ()

getFInfo :: InferenceConfig -> Config ->  [GhcInfo] -> IO (F.SInfo Cinfo)
getFInfo infconfig cfg ghci = do
    putStrLn "TyCon"
    mapM_ (print . gsTcs . giSrc) ghci
    -- mapM_ (print . gsTconsP . gsName . giSpec) $ ghci

    let meas_spec = measureSpecs ghci

    let data_decl = map (gsCtors . gsData . giSpec) $ ghci
        
        type_decl = smtTypeDecl meas_spec
    print type_decl

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
        clauses = map (toHorn cleaned_senv) cleaned_cm

        used_eapps = concatMap (funcEApps cleaned_senv) cleaned_cm

    putStrLn "used_eapps"
    print used_eapps

    let meas_apps = foldr (HM.unionWith (\xs ys -> nub $ xs ++ ys)) HM.empty $ map (measureApps senv) (HM.elems $ F.cm finfo)
        used_meas = filter (\M { msName = n } -> F.val n `elem` used_eapps) meas_spec
        used_meas_dc = usedMeasureDC meas_apps used_meas
        meas_decl = measureDecl meas_apps used_meas

        comb_apps = HM.unionWith (\xs ys -> nub $ xs ++ ys) meas_apps used_meas_dc

        data_dc = toSMTData  comb_apps {- . filter (\(v, _) -> F.symbol v `elem` used_eapps) -} $ concat data_decl

    putStrLn "used_meas_dc"
    print used_meas_dc

    putStrLn "measureApps"
    print meas_apps

    print $ map (\(n, l) -> (n, length l)) $ HM.toList comb_apps

    putStrLn "ws"
    print ws
    -- mapM_ (\(kvar, wfc) ->
    --                 putStrLn $ "kvar = " ++ show kvar
    --             ++ "\nwrft = " ++ show (F.wrft wfc)
    --             ++ "\nwinfo = " ++ show (F.wrft wfc)) $ HM.toList ws
    -- putStrLn "toHorn"
    -- mapM_ (\(f, r, _) -> do
    --         putStrLn $ "foralls = " ++ show f
    --         putStrLn $ "rhs = " ++ show r) clauses
    putStrLn "SMT"
    let smt_headers = type_decl ++ callStack ++ kindRep ++ classesNum ++ classesOrd ++ tycon_dd ++ trName ++ mod_dd ++ srcLoc ++ char
                        ++ [Comment "Data"]
                        ++ data_dc
                        ++ [Comment "Measures"]
                        ++ meas_decl ++ wf_decl ++ map (Assert . (\(_, _, smt) -> smt)) clauses
    putStrLn . T.unpack . TB.run $ toSolverText smt_headers
    return finfo
    where
        measureNames :: [GhcInfo] -> [F.Symbol]
        measureNames = map (F.symbol . msName) . measureSpecs

        measureSpecs :: [GhcInfo] -> [Measure SpecType DataCon]
        measureSpecs = filter (not . irrelName . symbolStringCon . F.val . msName)
                     . concatMap (gsMeasures . gsData . giSpec)

        irrelName :: String -> Bool
        irrelName "head" = True
        irrelName "tail" = True
        -- irrelName "isJust" = True
        -- irrelName "fromJust" = True
        irrelName _ = False

        classesNum = [DeclareData "GHC.Num.Num" ["num_var_sort"] [("GHC.Num.Num", [("num_var", SortVar "num_var_sort")])]]
        classesOrd = [DeclareData "GHC.Classes.Ord" ["ord_var_sort"] [("GHC.Classes.Ord", [("ord_var", SortVar "ord_var_sort")])]]
        trName = [DeclareData "GHC.Types.TrName" [] [("GHC.Types.TrName", [])]]
        mod_dd = [DeclareData "GHC.Types.Module" [] [("GHC.Types.Module", [])]]
        tycon_dd = [DeclareData "GHC.Types.TyCon" [] [("GHC.Types.TyCon", [])]]
        callStack = [DeclareData "GHC.Stack.Types.CallStack" [] [("GHC.Stack.Types.CallStack", [])]]
        kindRep = [DeclareData "GHC.Types.KindRep" [] [("GHC.Types.KindRep", [])]]
        srcLoc = [DeclareData "GHC.Stack.Types.SrcLoc" [] [("GHC.Stack.Types.SrcLoc", [])]]
        char = [DeclareData "Char" [] [("Char", [("char_v", SortInt)])]]


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
    DeclareFun (symbolStringCon $ F.kv kvar) ([lhSortToSMTSort s] ++ map lhSortToSMTSort bound_sorts) SortBool

hornCons :: F.WfC Cinfo -> IO ()
hornCons (F.WfC { F.wenv = env, F.wrft = rft, F.winfo = info }) = do
    putStrLn "----"
    print $ elemsIBindEnv env
    print rft
    print info

smtTypeDecl :: [Measure SpecType DataCon] -> [SMTHeader]
smtTypeDecl ms =
    let
        ms_def = filter (isJust . measArg) ms
        all_types = groupBy (\m1 -> cmpEq . comparing measArg m1) $ sortBy (comparing measArg) ms
    in
    mapMaybe toSMTDataSort' all_types
    where

        cmpEq EQ = True
        cmpEq _ = False

toSMTDataSort' :: [Measure SpecType DataCon] -> Maybe SMTHeader
toSMTDataSort' ms@(m:_) =
    let
        mdc = measArg m
        ret_types = map (\m -> (symbolStringCon . F.val $ msName m, last . toSMTDataSort . msSort $ m)) ms
    in
    case mdc of
        Just dc ->
            let
                n = symbolStringCon . tyConName . dataConTyCon $ dc
                dc_decl = ret_types -- [(n, zipWith (\i (mn, st) -> (\i -> mn, st)) [0 :: Integer ..] ret_types)]

                ty_vars = dataConUnivTyVars dc
                ty_vars_n = map (nameStableString . V.varName) ty_vars
            in
            case n of
                "Tuple" ->
                    let n' = n ++ show (length ty_vars_n) in
                    Just $ DeclareData n' ty_vars_n [(n', dc_decl)]
                _ -> Just $ DeclareData n ty_vars_n [(n, dc_decl)]
        Nothing -> Nothing
toSMTDataSort' [] = Nothing

measArg :: Measure ty a -> Maybe a
measArg m = case msEqns m of
                [] -> Nothing
                (h:_) -> Just $ ctor h


type AppSorts = HM.HashMap F.Symbol [(String, [F.Sort], F.Sort)]

measureApps :: F.BindEnv -> F.SimpC Cinfo -> AppSorts
measureApps bind subC =
    let
        top_eapps = allEApps bind subC
    in
      fmap nub 
    . foldr (uncurry (HM.insertWith (++))) HM.empty
    $ mapMaybe toMeasSymb top_eapps
    where
        toMeasSymb eapp | ((F.ECst (F.EVar "apply") srt), (F.ECst (F.EVar meas) meas_s):xs) <- F.splitEApp eapp =
            let
                split_sort = splitFFunc srt
                arg_s = init split_sort -- map (\(F.ECst arg1@(F.EVar _) s) -> s) xs
                ret_s = last split_sort

                all_smt_s = map lhSortToSMTSort split_sort
            in
            Just (meas, [(monoMeasName meas all_smt_s, arg_s, ret_s)])
        -- toMeasSymb (F.EApp
        --                 (F.EApp
        --                     (F.ECst (F.EVar "apply") _)
        --                     (F.ECst (F.EVar meas) meas_s@(F.FFunc _ ret_s))
        --                 ) 
        --                 (F.ECst arg1@(F.EVar _) arg_s)
        --       ) = Just (meas, [(monoMeasName meas arg_s, arg_s, ret_s)])
        toMeasSymb meas = Nothing

        ret (F.FFunc _ r) = ret r
        ret r = r

usedMeasureDC :: AppSorts -> [Measure SpecType DataCon] -> AppSorts
usedMeasureDC app_sorts = foldr (HM.unionWith (\xs ys -> nubBy (\(n1, _, _) (n2, _, _) -> n1 == n2) $ xs ++ ys)) HM.empty . (app_sorts:) . map (usedMeasureDC' app_sorts) 

usedMeasureDC' :: AppSorts -> Measure SpecType DataCon -> AppSorts
usedMeasureDC' app_sorts (M { msName = mn, msSort = st, msEqns = defs }) =
    case HM.lookup (F.val mn) app_sorts of
        Just mns -> foldr (HM.unionWith (\xs ys -> nub $ xs ++ ys)) HM.empty
                    $ map
                        (\(n, [arg_sort], ret_sort) ->
                            case F.unFApp arg_sort of
                                (_:es) -> HM.fromListWith (\xs ys -> nub $ xs ++ ys)
                                        $ map (\d ->
                                                    let
                                                        tycon = F.symbolString . tyConName . dataConTyCon $ ctor d
                                                        use_n = monoMeasNameStr (dcString $ ctor d) $ map lhSortToSMTSort es ++ [SortVar tycon]
                                                    in
                                                    (F.symbol (dcString $ ctor d), [(use_n, es, ret_sort)])) defs
                                [] -> error "usedMeasureDC': unsupported") mns
        Nothing -> HM.empty

splitFFunc :: F.Sort -> [F.Sort]
splitFFunc (F.FFunc s1 s2) = s1:splitFFunc s2
splitFFunc s = [s]

funcEApps :: F.BindEnv -> F.SimpC Cinfo -> [F.Symbol]
funcEApps bind subC =
    let
        eapps = allEApps bind subC
    in
    map (\eapp -> case F.splitEApp eapp of
                        (F.EVar "apply", F.EVar v:_) -> v
                        (F.ECst (F.EVar "apply") _, (F.ECst (F.EVar v) _):_) -> v
                        (F.EVar v, _) -> v
                        (F.ECst (F.EVar v) _, _) -> v) eapps

allEApps :: F.BindEnv -> F.SimpC Cinfo -> [F.Expr]
allEApps bind subC =
    let env = F._cenv subC
        -- lhs = F.clhs subC
        rhs = F._crhs subC

        forall_expr = map F.expr
                    $ map (`F.lookupBindEnv` bind) (elemsIBindEnv env)
    in
    concatMap topEApps $ rhs:forall_expr

measureDecl :: AppSorts -> [Measure SpecType DataCon] -> [SMTHeader]
measureDecl mas = concatMap (measureDecl' mas)

measureDecl' :: AppSorts -> Measure SpecType DataCon -> [SMTHeader]
measureDecl' mas (M { msName = mn, msSort = st, msEqns = defs }) =
    case HM.lookup (F.val mn) mas of
        Just mns -> concatMap
                        (\(n, [arg_sort], ret_sort) ->
                            let
                                def_clauses = measureDef (F.val mn) n st arg_sort defs
                            in
                            DeclareFun n [lhSortToSMTSort arg_sort, lhSortToSMTSort ret_sort] SortBool:def_clauses) mns
        Nothing ->
            let
                srt = toSMTDataSort st
                n = monoMeasName (F.symbol mn) srt
            in
            [DeclareFun n srt SortBool]
    where
        repSort s1 (_:s2) = lhSortToSMTSort s1:s2

measureDef :: F.Symbol -> String -> SpecType -> F.Sort -> [Def SpecType DataCon] -> [SMTHeader]
measureDef orig_n n st arg_srt = map (measureDef' orig_n n st arg_srt)

measureDef' :: F.Symbol -> String -> SpecType -> F.Sort -> Def SpecType DataCon -> SMTHeader
measureDef' orig_n n st lh_arg_srt def@(Def { binds = binds, body = bdy, ctor = dc }) =
    let
        real_dc_n = occNameString . nameOccName $ dataConName dc
        dc_n = dcString dc
        dc_tycon_n = tyConName $ dataConTyCon dc

        arg_srt = case lhSortToSMTSort lh_arg_srt of
                    SortDC _ xs -> xs
                    _ -> error "measureDef': unsupported"
        arg_poly_srt = case toSMTDataSort st of
                    [SortDC _ xs, _] -> xs
                    _ -> error "measureDef': unsupported"
        ret_srt = last $ toSMTDataSort st

        bind_vs = if isTuple real_dc_n
                    then zipWith (\(b, _) s -> (symbolStringCon b, s)) binds arg_srt
                    else if isLen n then zipWith (\(b, _) s -> (symbolStringCon b, s)) binds [head arg_srt, SortDC "_open_bracket__close_bracket_" [head arg_srt]]
                        else map (\(b, s) -> (symbolStringCon b, maybe (SortDC "BAD" []) (head . toSMTDataSort) s)) binds
        bind_srts = if isTuple real_dc_n
                        then map snd bind_vs else
                            if isLen n then arg_srt
                                else map snd bind_vs ++ arg_srt
        
        dc_use_n = monoMeasNameStr dc_n (bind_srts ++ [SortVar $ F.symbolString dc_tycon_n])
        ret_dc = V "RET_LH_G2" (lhSortToSMTSort lh_arg_srt)
        dc_smt = Func dc_use_n $ map (uncurry V) bind_vs ++ [ret_dc]

        extra_vs = map (\(n, _) -> (n, ret_srt)) $ HM.elems ms
        vs = ("RET_LH_G2", lhSortToSMTSort lh_arg_srt):bind_vs ++ extra_vs

        vs_m = HM.fromList $ (symbolStringCon orig_n, (n, Nothing)):(map (\(v, s) -> (v, (v, Just s))) vs)
        (lhs, rhs, ms) = measureDefBody vs_m bdy
    in
    Assert $ ForAll vs (SmtAnd (dc_smt:rhs) :=> Func n [ret_dc, lhs])
    where
        isTuple [] = True
        isTuple ('(':xs) = isTuple xs
        isTuple (')':xs) = isTuple xs
        isTuple (',':xs) = isTuple xs
        isTuple _ = False

        isLen ('l':'e':'n':_) = True
        isLen _ = False

dcString :: DataCon -> String
dcString dc =
    let
        dc_n = dataConName dc
        mdl = case nameModule_maybe dc_n of
                  Nothing -> ""
                  Just md -> (moduleNameString . moduleName $ md) ++ "."
    in
    mdl ++ (occNameString . nameOccName $ dc_n)

measureDefBody :: HM.HashMap SMTName (SMTName, Maybe Sort) -> Body -> (SMTAST, [SMTAST], HM.HashMap SMTName (SMTName, Maybe Sort))
measureDefBody m (E e) = measureDefExpr m e
measureDefBody m (P e) = measureDefExpr m e

measureDefExpr ::  HM.HashMap SMTName (SMTName, Maybe Sort) -> F.Expr -> (SMTAST, [SMTAST], HM.HashMap SMTName (SMTName, Maybe Sort))
measureDefExpr = toSMTAST "fresh"

toSMTData :: AppSorts -> [(Var, LocSpecType)] -> [SMTHeader]
toSMTData app_sorts = concatMap (uncurry (toSMTData' app_sorts))

toSMTData' :: AppSorts -> Var -> LocSpecType -> [SMTHeader]
toSMTData' app_sorts v st =
        case HM.lookup (F.symbol v) app_sorts of
            Just as -> map (\(n, arg_srt, ret_srt) ->
                                let
                                    poly = map nameStableString $ specTypeToPoly $ F.val st
                                    lh_srt = map lhSortToSMTSort $ arg_srt ++ [ret_srt]
                                    poly_srt = zip poly lh_srt

                                    dc_poly_srt = toSMTDataSort $ F.val st
                                    dc_srt = map (flip (foldr (uncurry repPoly)) poly_srt) dc_poly_srt
                                in
                                DeclareFun n dc_srt SortBool) as
            Nothing -> [] -- [DeclareFun (symbolStringCon $ F.symbol v) (toSMTDataSort $ F.val st) SortBool]

repPoly :: String -> Sort -> Sort -> Sort
repPoly n rep SortInt = SortInt
repPoly n rep v@(SortVar vn) | n == vn = rep
                             | otherwise = v
repPoly n rep (SortDC dc xs) = SortDC dc (map (repPoly n rep) xs)
repPoly _ _ s = error $ "repPoly: unhandled " ++ show s

toSMTDataSort :: SpecType -> [Sort]
toSMTDataSort (RVar {rt_var = (RTV v)}) =
    let
        n = nameStableString $ V.varName v
    in
    [SortVar n]
toSMTDataSort (RAllP { rt_ty = rty}) = toSMTDataSort rty
toSMTDataSort (RAllT { rt_ty = rty}) = toSMTDataSort rty
toSMTDataSort (RFun {rt_in = fin, rt_out = fout }) = toSMTDataSort fin ++ toSMTDataSort fout
toSMTDataSort (RApp { rt_tycon = c, rt_args = as }) =
    let
        n = symbolStringCon . tyConName $ rtc_tc c
        es = concatMap toSMTDataSort as
    in
    case n of
        "GHC.Types.Int" -> [SortInt]
        "GHC.Types.Char" -> [SortDC "Char" []]
        "GHC.Types.Bool" -> [SortBool]
        "Tuple" -> [SortDC (n ++ show (length as)) es]
        _ -> [SortDC n es]
toSMTDataSort st = error $ "toSMTDataSort: " ++ show st

specTypeToPoly :: SpecType -> [Name]
specTypeToPoly (RAllT { rt_tvbind = RTVar (RTV v) _, rt_ty = rty }) = V.varName v:specTypeToPoly rty
specTypeToPoly _ = []

toHorn :: F.BindEnv -> F.SimpC Cinfo -> ([(F.Symbol, F.SortedReft)], F.Expr, SMTAST)
toHorn bind subC =
    let env = F._cenv subC
        -- lhs = F.clhs subC
        rhs = F._crhs subC

        foralls_binds = map (`F.lookupBindEnv` bind) (elemsIBindEnv env)
        foralls = -- filter (\(n, _) -> n /= "GHC.Types.True" && n /= "GHC.Types.False")
                  filter (not . F.isFunctionSortedReft . snd)
                -- . filter (not . sortNameHasPrefix "GHC.Types" . F.sr_sort . snd)
                -- . filter (not . sortNameHasPrefix "GHC.Classes.Ord" . F.sr_sort . snd)
                -- . filter (not . sortNameHasPrefix "GHC.Num" . F.sr_sort . snd)
                -- . filter (\(_, rr) -> F.sr_sort rr /= F.FTC (F.strFTyCon))
                $ foralls_binds

        ms = foldr (\(i, (n, sr)) m -> sortedReftToMap i n m sr) HM.empty $ zip [1..] foralls
        (lhs_smt, ms') = unzip
                      . map (\(smt, smts, m) -> (SmtAnd (smt:smts), m))
                      $ map (\(i, (n, sr)) -> rrToSMTAST (show i) ms sr) $ zip [1..] foralls -- ++ [lhs]
        (rhs_smt, rhs_smts, rhs_m) = toSMTAST "rhs_val" (mconcat ms') rhs

        forall = ForAll
               . nub
               . fmap (fmap fromJust)
               . filter (isJust . snd)
               . concatMap HM.elems
               $ rhs_m:ms'
    in
    (foralls, rhs, forall (SmtAnd (lhs_smt ++ rhs_smts) :=> rhs_smt))

sortNameHasPrefix :: String -> F.Sort -> Bool
sortNameHasPrefix prefix eapp | F.FTC h:_ <- F.unFApp eapp =
    let
        h_symb = F.symbol h
    in
    isPrefixOf prefix (symbolStringCon h_symb)
sortNameHasPrefix _ _ = False

rrToSMTAST :: String -> HM.HashMap SMTName (SMTName, Maybe Sort) -> F.SortedReft -> (SMTAST, [SMTAST], HM.HashMap SMTName (SMTName, Maybe Sort))
rrToSMTAST fresh m rr =
    let
        (smt, smts, m') = toSMTAST fresh m (F.expr rr)
    in
    (smt, smts, HM.union m m')

sortedReftToMap :: Int -> F.Symbol -> HM.HashMap SMTName (SMTName, Maybe Sort) -> F.SortedReft -> HM.HashMap SMTName (SMTName, Maybe Sort)
sortedReftToMap i symb1 m (F.RR { F.sr_sort = sort, F.sr_reft = F.Reft (symb2, _) })
    | Just smt_nme_srt <- HM.lookup nme1 m =
    --    trace ("---\nnme1 = " ++ nme1 ++ "\nnme2 = " ++ nme2 ++ "\nsmt_nme_srt = " ++ show smt_nme_srt)
       HM.insert nme1 smt_nme_srt $ HM.insert nme2 smt_nme_srt m
    | otherwise =
        let
            smt_nme = nme2 ++ "_G2_" ++ show i
            smt_sort = Just $ lhSortToSMTSort sort
        in
        HM.insert nme1 (smt_nme, smt_sort) $ HM.insert nme2 (smt_nme, smt_sort) m
    where
        nme1 = symbolStringCon symb1
        nme2 = symbolStringCon symb2

toSMTAST :: String -> HM.HashMap SMTName (SMTName, Maybe Sort) -> F.Expr -> (SMTAST, [SMTAST], HM.HashMap SMTName (SMTName, Maybe Sort))
toSMTAST fresh m e =
    let
        (e', es, m') = appRep fresh e

        union_m = m `HM.union` m'
    in
    (toSMTAST' union_m SortBool e', map (toSMTAST' union_m SortBool) es, m')

appRep :: String -> F.Expr -> (F.Expr, [F.Expr], HM.HashMap SMTName (SMTName, Maybe Sort))
appRep fresh e =
    let
        apps_rep = HM.fromList
                 . filter (relApp . fst)
                 . zip (topEApps e)
                 . map F.symbol
                 . map (\i -> "__G2__meas_r__" ++ fresh ++ "__" ++ i)
                 $ map show [0..]

        meas_apps = map (\(me, n) -> F.EApp me (F.EVar n)) $ HM.toList apps_rep

        ns = HM.fromList
           . map (\kv@(k, _) -> (k, kv))
           . map (\(e, s) -> (s, fmap lhSortToSMTSort $ getSort e))
           . map (\(e, s) -> (e, symbolStringCon s))
           $ HM.toList apps_rep
    in
    (repExpr apps_rep e, meas_apps, ns)
    where
        -- relApp eapp | (F.ECst (F.EVar "apply") s, es) <- F.splitEApp eapp = length (splitFFunc s) == length es
        relApp eapp | (F.ECst (F.EVar "strLen") _, _) <- F.splitEApp eapp = True
        relApp eapp | (F.ECst _ s, es) <- F.splitEApp eapp = length (splitFFunc s) == length es
        relApp eapp | (F.EVar _, es) <- F.splitEApp eapp = True
        relApp eapp = False

getSort :: F.Expr -> Maybe F.Sort
getSort eapp@(F.EApp e _) =
    case getSort e of
        Just (F.FFunc _ s) -> Just s
        s -> s
getSort (F.ECst _ s) = Just s
getSort e = Nothing

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
topEApps eapp@(F.EApp _ _) = [eapp] ++ concat (mapRightEApp topEApps eapp)
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

mapRightEApp :: (F.Expr -> a) -> F.Expr -> [a]
mapRightEApp f (F.EApp e1 e2) = f e2:mapRightEApp f e1
mapRightEApp _ _ = []

toSMTAST' :: HM.HashMap SMTName (SMTName, Maybe Sort) -> Sort -> F.Expr -> SMTAST
toSMTAST' m sort (F.EVar v) | Just (fv, _) <- HM.lookup (symbolStringCon v) m = V fv sort
                            | otherwise = V (symbolStringCon v) sort
toSMTAST' _ _ (F.ESym (F.SL v)) =
    let
        list = symbolStringCon "[]"
    in
    Func list [VInt $ toInteger (T.length v)]
toSMTAST' _ _ (F.ECon (F.I i)) = VInt i
toSMTAST' m sort (F.EBin op e1 e2) =
    toSMTASTOp op (toSMTAST' m sort e1) (toSMTAST' m sort e2)
toSMTAST' m _ (F.ECst v@(F.EVar _) s) = toSMTAST' m (lhSortToSMTSort s) v
toSMTAST' m _ (F.ECst e s) = toSMTAST' m (lhSortToSMTSort s) e

-- Handle measures
toSMTAST' m _ eapp@(F.EApp _ _) | ((F.ECst (F.EVar "apply") srt), (F.ECst (F.EVar meas) meas_s):es) <- F.splitEApp eapp  =
    let    
        -- ret (F.FFunc _ r) = ret r
        -- ret r = r
        -- ret_s = ret meas_s
        srts = map lhSortToSMTSort $ splitFFunc srt
    in
    Func (monoMeasName meas srts) $ map (toSMTAST' m (SortDC "UNKNOWN" [])) es -- [toSMTAST' m (lhSortToSMTSort arg_s) arg1, toSMTAST' m SortInt arg2]
    where        
        sortECstVar (F.ECst arg1@(F.EVar _) s) = Just s

toSMTAST' m _ eapp@(F.EApp
                    (F.EApp
                        (F.EApp
                            (F.ECst (F.EVar "apply") _)
                            (F.ECst (F.EVar meas) _)
                        ) 
                        (F.ECst arg1@(F.EVar _) arg_s)
                    )
                    arg2
              ) = Func (monoMeasName meas [lhSortToSMTSort arg_s]) [toSMTAST' m (lhSortToSMTSort arg_s) arg1, toSMTAST' m SortInt arg2]
toSMTAST' m _ eapp@(F.EApp {}) | (F.ECst (F.EVar f) _:es) <- splitApplyApp eapp
                               , m_arg_s <- map (predictSort m) es
                               , all isJust m_arg_s
                               , arg_s <- map (fromMaybe (SortDC "UNKNOWN" [])) m_arg_s =
    let
        f_str = symbolStringCon f
    in
    case HM.lookup f_str m of
        Just (f', _) -> Func f' $ map (toSMTAST' m (SortDC "UNKNOWN" [])) es
        Nothing -> Func (monoMeasName f arg_s) $ map (toSMTAST' m (SortDC "UNKNOWN" [])) es
toSMTAST' m _ eapp@(F.EApp {}) | (F.EVar f:es) <- splitApplyApp eapp
                               , m_arg_s <- map (predictSort m) es
                               , all isJust m_arg_s
                               , arg_s <- map (fromMaybe (SortDC "UNKNOWN" [])) m_arg_s =
    let
        f_str = symbolStringCon f
    in
    case HM.lookup f_str m of
        Just (f', _) -> Func f' $ map (toSMTAST' m (SortDC "UNKNOWN" [])) es
        Nothing -> Func (monoMeasName f arg_s) $ map (toSMTAST' m (SortDC "UNKNOWN" [])) es
    -- error $ "toSMTAST': \neapp = " ++ show eapp ++ "\nes = " ++ show es -- (func, xs@(_:_)) <- F.splitEApp eapp = error $ "toSMTAST': eapp = " ++ show eapp ++ "\nfunc = " ++ show func ++ "\nxs = " ++ show xs
toSMTAST' m _ eapp@(F.EApp {}) =
    let
        (_, es) = F.splitEApp eapp
    in
    error $ "toSMTAST': map " ++ show m ++ "\neapp = " ++ show eapp ++ "\nes = " ++ show (map (\e -> (e, predictSort m e)) es)

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
    Func (symbolStringCon . F.kv $ k) $ map (toSMTAST' m SortInt) args

toSMTAST' _ sort e = error $ "toSMTAST': unsupported " ++ show e ++ "\n" ++ show sort

monoMeasName :: F.Symbol -> [Sort] -> String
monoMeasName meas = monoMeasNameStr' (symbolStringCon meas)

monoMeasNameStr :: String -> [Sort] -> String
monoMeasNameStr meas = monoMeasNameStr' (conString meas)

monoMeasNameStr' :: String -> [Sort] -> String
monoMeasNameStr' meas sort =
    let
        sort_str = conString $ sortMeasName sort
    in
    meas ++ "_" ++ sort_str

sortMeasName :: [Sort] -> String
sortMeasName xs = intercalate "_" (map sortMeasName' xs)

sortMeasName' :: Sort -> [Char]
sortMeasName' SortInt = "Int"
sortMeasName' (SortVar n) = n
sortMeasName' (SortDC dc xs) =
    dc ++ sortMeasName xs
sortMeasName' sort = error $ "sortMeasName: unsupported " ++ show sort

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
lhSortToSMTSort (F.FObj s) = SortVar (symbolStringCon s)
lhSortToSMTSort (F.FObj s) = SortVar (symbolStringCon s)
lhSortToSMTSort eapp | F.FTC h:es <- F.unFApp eapp =
    let
        h_symb = symbolStringCon $ F.symbol h
    in
    case h_symb of
        "bool" -> SortBool
        "GHC.Types.Char" -> SortDC "Char" []
        "Str" -> SortDC listCons [SortDC "Char" []]
        "Tuple" -> let h_symb' = h_symb ++ show (length es) in
                    SortDC h_symb' $ map lhSortToSMTSort es
        _ -> SortDC h_symb $ map lhSortToSMTSort es
lhSortToSMTSort (F.FAbs _ _) = SortVar "FAbs" 
lhSortToSMTSort (F.FFunc _ _) = SortVar "FFunc" 
lhSortToSMTSort sort = error $ "lhSortToSMTSort: unsupported " ++ show sort

listCons :: String
listCons = conString "[]"

predictSort :: HM.HashMap SMTName (SMTName, Maybe Sort) -> F.Expr -> Maybe Sort
predictSort _ (F.ESym _) = Nothing
predictSort m (F.EVar v) = snd =<< (HM.lookup (symbolStringCon v) m)
predictSort _ (F.ECst _ s) = Just $ lhSortToSMTSort s
predictSort _ (F.PAtom _ _ _) = Just SortBool
predictSort _ (F.PAnd _) = Just SortBool
predictSort _ (F.PNot _) = Just SortBool
predictSort _ e = error $ "predictSort: unsupported " ++ show e

giInfo :: F.SubC Cinfo -> String
giInfo sc =
  "F.SubC Cinfo " ++ "\n_senv = " ++ show (elemsIBindEnv $ F.senv sc) ++ "\nslhs = " ++ show (F.slhs sc) ++ "\nsrhs = " ++ show (F.srhs sc)
                      ++ "\n_sid = " ++ show (F.sid sc) ++ "\n_stag = " ++ show (F.stag sc) ++ "\n_sinfo = " ++ show (F.sinfo sc)

symbolStringCon :: F.Symbol -> String
symbolStringCon = conString . F.symbolString

conString :: String -> String
conString = concatMap conString'

conString' :: Char -> String
conString' '(' = "_open_paren_"
conString' ')' = "_close_paren_"
conString' '[' = "_open_bracket_"
conString' ']' = "_close_bracket_"
conString' ',' = "_comma_"
conString' ':' = "_colon_"
conString' '#' = "_ns_"
conString' x = [x]