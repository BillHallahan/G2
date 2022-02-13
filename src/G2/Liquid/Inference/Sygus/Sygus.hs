{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.Inference.Sygus.Sygus ( BlockedSygus
                                       , BlockedSyguses
                                       , generateSygusProblem) where

import G2.Language as G2
import G2.Liquid.Helpers
import G2.Liquid.Interface
import G2.Liquid.Types
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.FuncConstraint
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.GeneratedSpecs
import G2.Liquid.Inference.PolyRef
import G2.Liquid.Inference.Sygus.FCConverter
import G2.Liquid.Inference.Sygus.SpecInfo
import G2.Solver as Solver

import Sygus.LexSygus
import Sygus.ParseSygus
import Sygus.Print
import Sygus.Syntax as Sy

import Control.Exception
import Control.Monad.IO.Class 
import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Ratio
import qualified Data.Text as T
import System.Directory
import qualified System.Process as P
import System.IO
import System.IO.Temp

import Language.Haskell.Liquid.Types as LH hiding (SP, ms, isBool)
import Language.Fixpoint.Types.Refinements as LH hiding (pAnd, pOr)
import qualified Language.Fixpoint.Types as LH
import qualified Language.Fixpoint.Types as LHF

generateSygusProblem :: (InfConfigM m, ProgresserM m, MonadIO m) =>
                        [GhcInfo]
                     -> LiquidReadyState
                     -> Evals Bool
                     -> MeasureExs
                     -> FuncConstraints
                     -> BlockedSyguses
                     -> ToBeNames
                     -> ToSynthNames
                     -> m SynthRes
generateSygusProblem ghci lrs evals meas_ex fc blk_sygus to_be_ns ns_synth = do
    infConfig <- infConfigM
    MaxSize max_sz <- maxSynthSizeM
    let clmp_int = 2 * max_sz

    -- Figure out the type of each of the functions we need to synthesize
    let eenv = buildNMExprEnv $ expr_env . state $ lr_state lrs
        tenv = type_env . state $ lr_state lrs
        tc = type_classes . state $ lr_state lrs
        meas = lrsMeasures ghci lrs

    si <- buildSpecInfo eenv tenv tc meas ghci fc to_be_ns ns_synth

    let grammar = buildGrammars si

    let eval_ids = assignIds evals
        to_be_consts = createToBeConsts si eval_ids
    constraints <- constraintsToSygus eenv tenv meas meas_ex eval_ids si fc

    let cmds = [ SmtCmd (Sy.SetLogic "ALL"), clampIntDecl clmp_int] ++ to_be_consts ++ grammar ++ constraints ++ [CheckSynth]

    liftIO $ putStrLn "-------------\nSyGuS\n"
    let sygus = T.unpack . printSygus $ cmds
    liftIO . putStrLn $ sygus
    -- res <- runCVC4 infConfig sygus
    res <- runCVC4Streaming blk_sygus infConfig undefined sygus
    liftIO $ putStrLn "-------------"
    case res of
        Right r -> return $ SynthEnv (getGeneratedSpecs clmp_int si r)
                                     max_sz Nothing emptyBlockedModels (Just r)
        _ -> return $ SynthFail emptyFC

-------------------------------
-- Grammar
-------------------------------

buildGrammars :: M.Map Name SpecInfo -> [Cmd]
buildGrammars =
    concatMap buildGrammars' . M.elems . M.filter (\si -> s_status si == Synth)

buildGrammars' :: SpecInfo -> [Cmd]
buildGrammars' si =
    map buildGrammars'' $ extractValues (s_syn_post si) ++ concatMap extractValues (s_syn_pre si)

buildGrammars'' :: SynthSpec -> Cmd
buildGrammars'' sy_spec =
    SynthFun (sy_name sy_spec)
             (map buildGramArgs $ sy_args_and_ret sy_spec)
             (IdentSort (ISymb "Bool"))
           . Just $ buildGrammar sy_spec

buildGramArgs :: SpecArg -> SortedVar
buildGramArgs sa = SortedVar (smt_var sa) (smtSortToSygusSort $ smt_sort sa)

buildGrammar :: SynthSpec -> GrammarDef
buildGrammar sy_spec =
    forceVarInGrammar (map buildGramArgs $ sy_rets sy_spec)
                      (map buildGramArgs $ sy_args sy_spec)
                      (buildGrammar' sy_spec)

buildGrammar' :: SynthSpec -> GrammarDef
buildGrammar' sy_spec =
    GrammarDef 
        [ SortedVar "B" (IdentSort (ISymb "Bool"))
        , SortedVar "IClamp" (IdentSort (ISymb "Int"))
        , SortedVar "IConst" (IdentSort (ISymb "Int"))
        , SortedVar "I" (IdentSort (ISymb "Int"))]
        [ GroupedRuleList "B" (IdentSort (ISymb "Bool"))
            [ GVariable (IdentSort (ISymb "Bool"))
            , GConstant (IdentSort (ISymb "Bool"))
            , GBfTerm (BfIdentifierBfs (ISymb "and") [BfIdentifier (ISymb "B"), BfIdentifier (ISymb "B")])
            , GBfTerm (BfIdentifierBfs (ISymb "or") [BfIdentifier (ISymb "B"), BfIdentifier (ISymb "B")])
            , GBfTerm (BfIdentifierBfs (ISymb "=") [BfIdentifier (ISymb "I"), BfIdentifier (ISymb "I")])
            , GBfTerm (BfIdentifierBfs (ISymb ">") [BfIdentifier (ISymb "I"), BfIdentifier (ISymb "I")])
            , GBfTerm (BfIdentifierBfs (ISymb ">=") [BfIdentifier (ISymb "I"), BfIdentifier (ISymb "I")])
            ]
        , GroupedRuleList "IClamp" (IdentSort (ISymb "Int"))
            [
            GBfTerm (BfIdentifierBfs (ISymb clampIntSymb) [BfIdentifier (ISymb "IConst")])
            ]
        , GroupedRuleList "IConst" (IdentSort (ISymb "Int"))
            [ GConstant (IdentSort (ISymb "Int")) ]
        , GroupedRuleList "I" (IdentSort (ISymb "Int"))
            [ GVariable (IdentSort (ISymb "Int"))
            , GBfTerm (BfIdentifierBfs (ISymb clampIntSymb) [BfIdentifier (ISymb "IConst")])
            , GBfTerm (BfIdentifierBfs (ISymb "+") [BfIdentifier (ISymb "I"), BfIdentifier (ISymb "I")])
            , GBfTerm (BfIdentifierBfs (ISymb "*") [BfIdentifier (ISymb "IClamp"), BfIdentifier (ISymb "I")])
            ]
        ]

-------------------------------
-- Constraints
-------------------------------

constraintsToSygus :: (InfConfigM m, ProgresserM m) =>
                      NMExprEnv
                   -> TypeEnv
                   -> Measures
                   -> MeasureExs
                   -> Evals (Integer, Bool)
                   -> M.Map Name SpecInfo
                   -> FuncConstraints
                   -> m [Cmd]
constraintsToSygus eenv tenv meas meas_ex evals si fc =
    return . map Constraint =<<
        convertConstraints 
                    convertExprToTerm
                    (ifNotNull mkSygusAnd (TermLit (LitBool True)))
                    (ifNotNull mkSygusOr (TermLit (LitBool False)))
                    mkSygusNot
                    mkSygusImplies
                    (\s ts -> if null ts then TermIdent (ISymb s) else TermCall (ISymb s) ts)
                    (\_ _ -> TermLit . LitBool)
                    (\n i b ->
                        if b then
                            TermIdent (ISymb $ n ++ "__SYGUS_INT__" ++ show i)
                            else TermLit (LitBool False))
                    eenv tenv meas meas_ex evals si fc
    where
        ifNotNull _ def [] = def
        ifNotNull f _ xs = f xs

        mkSygusAnd = TermCall (ISymb "and") 
        mkSygusOr = TermCall (ISymb "or") 
        mkSygusNot t = TermCall (ISymb "not") [t]
        mkSygusImplies t1 t2 = TermCall (ISymb "=>") [t1, t2]

convertExprToTerm :: G2.Expr -> Term
convertExprToTerm (Data (DataCon (Name n _ _ _) _))
    | "True" <- n = TermLit $ LitBool True
    | "False" <- n =TermLit $ LitBool False
convertExprToTerm (Lit l) = litToTerm l
convertExprToTerm e = error $ "convertExprToTerm: Unhandled Expr " ++ show e

litToTerm :: G2.Lit -> Term
litToTerm (LitInt i) = TermLit (LitNum i)
litToTerm (LitDouble d) = TermCall (ISymb "/") [ TermLit . LitNum $ numerator d
                                               , TermLit . LitNum $ denominator d]
litToTerm (LitChar c) = TermLit (LitStr [c])
litToTerm _ = error "litToTerm: Unhandled Lit"

createToBeConsts :: M.Map Name SpecInfo -> Evals (Integer, Bool) -> [Cmd]
createToBeConsts si ev =
    let si' = M.mapKeys zeroOutName si in
       createToBeConsts' s_to_be_pre_name si' (pre_evals ev)
    ++ createToBeConsts' s_to_be_post_name si' (post_evals ev)
    where
      zeroOutName (Name n m _ l) = Name n m 0 l


createToBeConsts' :: (SpecInfo -> SMTName) ->  M.Map Name SpecInfo -> FCEvals ((Integer, Bool)) -> [Cmd]
createToBeConsts' f si = mapMaybe (createToBeConsts'' f si)
                       . concatMap (\(n, es) -> map (n,) es)
                       . HM.toList
                       . HM.map HM.elems

createToBeConsts'' :: (SpecInfo -> SMTName) -> M.Map Name SpecInfo -> (Name, (Integer, Bool)) -> Maybe Cmd
createToBeConsts'' f si (n, (i, b))
    | Just si' <- M.lookup n si
    , s_status si' == ToBeSynthed =
        Just $ DeclareVar (f si' ++ "__SYGUS_INT__" ++ show i) (IdentSort (ISymb "Bool"))
    | otherwise = Nothing

-------------------------------
-- Sorts
-------------------------------

smtSortToSygusSort :: Solver.Sort -> Sy.Sort
smtSortToSygusSort SortBool = IdentSort (ISymb "Bool")
smtSortToSygusSort SortInt = IdentSort (ISymb "Int")
smtSortToSygusSort s = error $ "smtSortToSygusSort: unsupported sort" ++ "\n" ++ show s

-------------------------------
-- Enforcing return value use
-------------------------------

-- Adjusts a grammar to force using a given GTerm

forceVarInGrammar :: [SortedVar] -- ^ Force using at least one of these variables
                  -> [SortedVar]  -- ^ All other variables
                  -> GrammarDef
                  -> GrammarDef
forceVarInGrammar vars params (GrammarDef sv grls) =
    let
        prod_srt = mapMaybe (\grl@(GroupedRuleList grl_symb srt' _) ->
                            if any (flip canProduceVar grl) (vars ++ params)
                                then Just grl_symb
                                else Nothing ) grls

        reach = gramSymbReachableFrom prod_srt grls

        sv_reach = concatMap (grammarDefSortedVars reach) sv

        (sv_final, grl_final) = elimNonTermGRL vars (forceVarInGRLList vars reach grls) sv_reach
    in
    GrammarDef sv_final grl_final

forceVarInGRLList :: [SortedVar] -> [Symbol] -> [GroupedRuleList] -> [GroupedRuleList]
forceVarInGRLList vars reach grls =
    let
        fv_map = HM.fromList $ map (\n -> (toBf n, toBf $ forcedVarSymb n)) reach

    in
    concatMap (forceVarInGRL vars reach fv_map) grls
    where
        toBf = BfIdentifier . ISymb

forceVarInGRL :: [SortedVar] -> [Symbol] -> HM.HashMap BfTerm BfTerm -> GroupedRuleList -> [GroupedRuleList]
forceVarInGRL vars reach fv_map grl@(GroupedRuleList grl_symb grl_srt gtrms)
    | grl_symb `elem` reach =
        let
            vars' = filter (\(SortedVar _ sv_sort) -> sv_sort == grl_srt) vars
            bf_vars = map (\(SortedVar sv_symb _) -> GBfTerm $ BfIdentifier (ISymb sv_symb)) vars'
            fv_gtrms' = filter (not . isClamp) $ elimVariable fv_gtrms

        in
        [GroupedRuleList fv_symb grl_srt (bf_vars ++ fv_gtrms'), grl]
    | otherwise = [grl]
    where
        fv_symb = forcedVarSymb grl_symb
        fv_gtrms = substOnceGTerms fv_map gtrms


forcedVarSymb :: Symbol -> Symbol
forcedVarSymb = ("fv_" ++)

elimVariable :: [GTerm] -> [GTerm]
elimVariable = filter (\t -> case t of
                            GVariable _ -> False
                            _ -> True)

elimNonTermGRL :: [SortedVar] -> [GroupedRuleList] -> [SortedVar] -> ([SortedVar], [GroupedRuleList])
elimNonTermGRL sorted_v grls sv =
    let
        has_term = hasTermFix (HS.fromList $ map (\(SortedVar sv_n _) -> sv_n) sorted_v) grls

        sv' = filter (\(SortedVar n _) -> n `elem` has_term) sv
        grls' = map (elimRules has_term)
              $ filter (\(GroupedRuleList n _ _) -> n `elem` has_term) grls
    in
    (sv', grls')

hasTermFix :: HS.HashSet Symbol -> [GroupedRuleList] -> [Symbol]
hasTermFix ht grl =
    let
        ht' = HS.fromList
            . map (\(GroupedRuleList n _ _) -> n)
            $ filter (hasTermGRL ht) grl


        ht_all = HS.union ht ht'
    in
    if ht == ht_all then HS.toList ht_all else hasTermFix ht_all grl

hasTermGRL :: HS.HashSet Symbol -> GroupedRuleList -> Bool
hasTermGRL ht (GroupedRuleList n _ r) = n `HS.member` ht || any (hasTermGTerm ht) r

hasTermGTerm :: HS.HashSet Symbol -> GTerm -> Bool
hasTermGTerm _ (GConstant _) = True
hasTermGTerm _ (GVariable _) = True
hasTermGTerm ht (GBfTerm bft) = hasTermBfTerm ht bft

hasTermBfTerm :: HS.HashSet Symbol -> BfTerm -> Bool
hasTermBfTerm ht (BfIdentifier (ISymb i)) = i `HS.member` ht
hasTermBfTerm _ (BfLiteral _) = True
hasTermBfTerm ht (BfIdentifierBfs _ bfs) = all (hasTermBfTerm ht) bfs

isClamp :: GTerm -> Bool
isClamp (GBfTerm (BfIdentifier (ISymb "IClamp"))) = True
isClamp (GBfTerm (BfIdentifier (ISymb "DClamp"))) = True
isClamp _ = False

elimRules :: [Symbol] -> GroupedRuleList -> GroupedRuleList
elimRules grls (GroupedRuleList symb srt r) =
    GroupedRuleList symb srt $ filter (elimRules' grls) r

elimRules' :: [Symbol] -> GTerm -> Bool
elimRules' _ (GConstant _) = True
elimRules' _ (GVariable _) = True
elimRules' grls (GBfTerm bft) = elimRulesBfT grls bft

elimRulesBfT :: [Symbol] -> BfTerm -> Bool
elimRulesBfT grls (BfIdentifier (ISymb i)) = i `elem` grls
elimRulesBfT _ (BfLiteral _) = True
elimRulesBfT grls (BfIdentifierBfs _ bfs) = all (elimRulesBfT grls) bfs


-------------------------------
-- define-fun
-------------------------------

-- We define a function safe-mod, which forces the denominator of mod to be positive.

safeModSymb :: Symbol
safeModSymb = "safe-mod"

safeModDecl :: Cmd
safeModDecl =
    SmtCmd
        . Sy.DefineFun safeModSymb [SortedVar "x" intSort, SortedVar "y" intSort] intSort
            $ TermCall (ISymb "mod")
                [ TermIdent (ISymb "x")
                , TermCall (ISymb "+") [TermLit (LitNum 1), TermCall (ISymb "abs") [TermIdent (ISymb "y")]]
                ]

-- We define a function clamp, which forces (Constant sort) to fall only in a fixed range
clampIntSymb :: Symbol
clampIntSymb = clampSymb "int"

clampIntDecl :: Integer -> Cmd
clampIntDecl = clampDecl clampIntSymb intSort

clampSymb :: Symbol -> Symbol
clampSymb = (++) "clamp-"

clampDecl :: Symbol -> Sy.Sort -> Integer -> Cmd
clampDecl fn srt mx =
    SmtCmd
        . Sy.DefineFun fn [SortedVar "x" srt] srt
        $ TermCall (ISymb "ite")
            [ TermCall (ISymb "<") [TermLit $ LitNum mx, TermIdent (ISymb "x")]
            , TermLit $ LitNum mx
            , TermCall (ISymb "ite")
                [ TermCall (ISymb "<") [TermIdent (ISymb "x"), TermLit $ LitNum 0]
                , TermLit $ LitNum 0
                , TermIdent (ISymb "x")
                ]
            ]

intSort :: Sy.Sort
intSort = IdentSort (ISymb "Int")

-------------------------------
-- Conversion to LH Specs
-------------------------------

getGeneratedSpecs :: Size -> M.Map Name SpecInfo -> [Cmd]  -> GeneratedSpecs
getGeneratedSpecs max_sz m_si cmd =
  let
      lh_spec = M.map (\si -> buildSpecFromSygus max_sz si cmd) . M.filter (\si -> s_status si == Synth) $ m_si
  in
  M.foldrWithKey insertAssertGS emptyGS lh_spec

buildSpecFromSygus :: Size -> SpecInfo -> [Cmd] -> [PolyBound LHF.Expr]
buildSpecFromSygus max_sz si cmds = buildSpecFromSygus' max_sz si fs
    where
        fs = M.fromList
           $ mapMaybe (\cmds -> case cmds of
                                    SmtCmd (Sy.DefineFun n sv _ t) -> Just (n, t)
                                    _ -> Nothing
                      ) cmds

buildSpecFromSygus' :: Size -> SpecInfo -> M.Map Sy.Symbol Term -> [PolyBound LH.Expr]
buildSpecFromSygus' max_sz si fs =
    let
        -- post_ars = allPostSpecArgs si

        build = buildSpec max_sz si fs
        pre = map (mapPB build) $ s_syn_pre si
        post = mapPB build $ s_syn_post si
    in
    pre ++ [post]


buildSpec :: Size -> SpecInfo -> M.Map Sy.Symbol Term -> SynthSpec -> LH.Expr
buildSpec max_sz si fs sy_sp@(SynthSpec { sy_name = sy_n })
    | Just t <- M.lookup sy_n fs = buildSpec' t
    | otherwise = error "buildSpec: spec not found"
    where
        buildSpec' (TermIdent (ISymb v)) =
            case find (\ar -> smt_var ar == v) $ sy_args_and_ret sy_sp of
                Just v' -> lh_rep v'
                Nothing -> error "buildSpec: Variable not found"
        buildSpec' (TermLit l) = litToLHConstant l
        buildSpec' (TermCall (ISymb v) ts)
            | clampIntSymb == v
            , [TermLit l] <- ts = clampedInt max_sz l
            -- EBin
            | "+" <- v
            , [t1, t2] <- ts = EBin LH.Plus (buildSpec' t1) (buildSpec' t2)
            | "-" <- v
            , [t1] <- ts = ENeg (buildSpec' t1)
            | "-" <- v
            , [t1, t2] <- ts = EBin LH.Minus (buildSpec' t1) (buildSpec' t2)
            | "*" <- v
            , [t1, t2] <- ts = EBin LH.Times (buildSpec' t1) (buildSpec' t2)
            | "/" <- v
            , [t1, t2] <- ts
            , Just n1 <- getInteger t1
            , Just n2 <- getInteger t2 = ECon . LHF.R $ fromRational (n1 % n2)
            | "mod" <- v
            , [t1, t2] <- ts = EBin LH.Mod (buildSpec' t1) (buildSpec' t2)
            -- More EBin...
            | "and" <- v = PAnd $ map (buildSpec') ts
            | "or" <- v = POr $ map (buildSpec') ts
            | "not" <- v, [t1] <- ts = PNot (buildSpec' t1)
            | "=>" <- v
            , [t1, t2] <- ts = PImp (buildSpec' t1) (buildSpec' t2)
            -- PAtom
            | "=" <- v
            , [t1, t2] <- ts = PAtom LH.Eq (buildSpec' t1) (buildSpec' t2)
            | ">" <- v 
            , [t1, t2] <- ts = PAtom LH.Gt (buildSpec' t1) (buildSpec' t2)
             | ">=" <- v 
            , [t1, t2] <- ts = PAtom LH.Ge (buildSpec' t1) (buildSpec' t2)
            | "<" <- v 
            , [t1, t2] <- ts = PAtom LH.Lt (buildSpec' t1) (buildSpec' t2)
           | "<=" <- v 
            , [t1, t2] <- ts = PAtom LH.Le (buildSpec' t1) (buildSpec' t2)

getInteger :: Term -> Maybe Integer
getInteger (TermLit (LitNum n)) = Just n
getInteger (TermCall (ISymb "-") [TermLit (LitNum n)]) = Just  (- n)
getInteger _ = Nothing

litToLHConstant :: Sy.Lit -> LH.Expr
litToLHConstant (LitNum n) = ECon (I n)
litToLHConstant (LitBool b) = if b then PTrue else PFalse
litToLHConstant l = error $ "litToLHConstant: Unhandled literal " ++ show l

clampedInt :: Size -> Sy.Lit -> LH.Expr
clampedInt max_sz (LitNum n)
    | n < 0 = ECon (LHF.I 0)
    | n > max_sz = ECon (LHF.I max_sz)
    | otherwise = ECon (LHF.I n)
clampedInt _ _ = error $ "clampedInt: Unhandled literals"

-------------------------------
-- Calling SyGuS
-------------------------------

runCVC4 :: MonadIO m => InferenceConfig -> String -> m (Either SomeException (Maybe [Cmd]))
runCVC4 infconfig sygus =
    liftIO $ try (
        withSystemTempFile ("cvc4_input.sy")
        (\fp h -> do
            hPutStr h sygus
            -- We call hFlush to prevent hPutStr from buffering
            hFlush h

            toCommand <- timeOutCommand

            sol <- P.readProcess toCommand ([show (timeout_sygus infconfig), "cvc4", fp, "--lang=sygus2"]) ""

            return . fmap (parse . lexSygus) $ stripPrefix "unsat" sol)
        )

runCVC4Streaming :: MonadIO m => HS.HashSet [Cmd] -> InferenceConfig -> Int -> String -> m (Either SomeException [Cmd])
runCVC4Streaming seen infconfig grouped sygus =
    liftIO $ try (
        withSystemTempFile ("cvc4_input.sy")
            (\fp h -> do
                hPutStr h sygus
                -- We call hFlush to prevent hPutStr from buffering
                hFlush h

                timeout <- timeOutCommand

                -- --no-sygus-fair-max searches for functions that minimize the sum of the sizes of all functions
                (inp, outp, errp, _) <- P.runInteractiveCommand
                                            $ timeout ++ " " ++ show (timeout_sygus infconfig)
                                                ++ " cvc4 " ++ fp ++ " --lang=sygus2 --sygus-stream --no-sygus-fair-max"

                lnes <- checkIfSolution seen grouped outp

                hClose inp
                hClose outp
                hClose errp

                return lnes
            )
        )

timeOutCommand :: IO String
timeOutCommand = do
    toCommandOSX <- findExecutable "gtimeout" 
    let toCommand = case toCommandOSX of
            Just c -> c          -- Mac
            Nothing -> "timeout" -- Linux
    return toCommand

checkIfSolution :: HS.HashSet [Cmd] -> Int -> Handle -> IO [Cmd]
checkIfSolution seen grouped h = do
    sol <- getSolution grouped h
    let sol' = concatMap (parse . lexSygus) $ sol
    if not (HS.member sol' seen) then return sol' else checkIfSolution seen grouped h 

getSolution :: Int -> Handle -> IO [String]
getSolution 0 _ = return []
getSolution !n h = do
    lne <- hGetLine h
    lnes <- getSolution (n - 1) h
    return $ lne:lnes

-----------------------------------------------------

-- Substitution functions

substOnceGTerms :: HM.HashMap BfTerm BfTerm -> [GTerm] -> [GTerm]
substOnceGTerms m = concatMap (substOnceGTerm m)

substOnceGTerm :: HM.HashMap BfTerm BfTerm -> GTerm -> [GTerm]
substOnceGTerm m (GBfTerm bf) = map GBfTerm $ substOnceBfTerm m bf
substOnceGTerm _ gt = [gt]

substOnceBfTerm :: HM.HashMap BfTerm BfTerm -> BfTerm -> [BfTerm]
substOnceBfTerm m (BfIdentifierBfs c bfs) = elimRedundant . map (BfIdentifierBfs c) $ substsOnces m bfs
substOnceBfTerm _ bf = [bf]

elimRedundant :: [BfTerm] -> [BfTerm]
elimRedundant (b@(BfIdentifierBfs (ISymb s) [b1, b2]):xs) =
    let
        xs' = if isCommutative s
                then delete (BfIdentifierBfs (ISymb s) [b2, b1]) xs
                else xs
    in
    b:elimRedundant xs'
elimRedundant (x:xs) = x:elimRedundant xs
elimRedundant [] = []

isCommutative :: Symbol -> Bool
isCommutative "and" = True
isCommutative "=" = True
isCommutative "+" = True
isCommutative _ = False

-- | Given:
--      * A mapping of list element to be replaced, to new elements
--      * A list, xs
-- returns a list of new lists.  Each new list is xs, but with exactly one
-- occurence of an old element replaced by the corresponding new element.
substsOnces :: (Eq a, Hashable a) => HM.HashMap a a -> [a] -> [[a]]
substsOnces m = substsOnces' m []

substsOnces' :: (Eq a, Hashable a) => HM.HashMap a a -> [a] -> [a] -> [[a]]
substsOnces' m rv [] = []
substsOnces' m rv (x:xs)
    | Just new <- HM.lookup x m = (reverse rv ++ new:xs):rst
    | otherwise = rst
        where
            rst = substsOnces' m (x:rv) xs

-----------------------------------------------------

grammarDefSortedVars :: [Symbol] -> SortedVar -> [SortedVar]
grammarDefSortedVars symbs sv@(SortedVar n srt)
    | n `elem` symbs = [SortedVar (forcedVarSymb n) srt, sv]
    | otherwise = [sv]

canProduceVar :: SortedVar -> GroupedRuleList -> Bool
canProduceVar var@(SortedVar symb sv_srt) (GroupedRuleList _ grl_srt gtrms)
    | sv_srt == grl_srt = any (canProduceVarGTerm var) gtrms
    | otherwise = False

canProduceVarGTerm :: SortedVar -> GTerm -> Bool
canProduceVarGTerm (SortedVar _ sv_srt) (GVariable gv_srt) = sv_srt == gv_srt
canProduceVarGTerm (SortedVar s _) (GBfTerm (BfIdentifier (ISymb is))) = s == is
canProduceVarGTerm s (GBfTerm (BfIdentifierBfs _ bfs)) = any (canProduceVarGTerm s) $ map GBfTerm bfs
canProduceVarGTerm _ (GBfTerm (BfLiteral _)) = False
canProduceVarGTerm _ (GConstant _) = False
canProduceVarGTerm _ t = error $ "Unhandled term" ++ show t

-----------------------------------------------------

-- Reachability checks

gramSymbReachableFrom :: [Symbol] -> [GroupedRuleList] -> [Symbol]
gramSymbReachableFrom = gramSymbReachableFrom' HS.empty

gramSymbReachableFrom' :: HS.HashSet Symbol -> [Symbol] -> [GroupedRuleList] -> [Symbol]
gramSymbReachableFrom' searched [] _ = HS.toList searched
gramSymbReachableFrom' searched (x:xs) grls
    | x `HS.member` searched = gramSymbReachableFrom' searched xs grls
    | otherwise =
        let
            contains_x = map (\(GroupedRuleList s _ _) -> s)
                       $ filter (containsSymbol x) grls
        in
        gramSymbReachableFrom' (HS.insert x searched) (contains_x ++ xs) grls

containsSymbol :: Symbol -> GroupedRuleList -> Bool
containsSymbol symb (GroupedRuleList _ _ gtrms) = any (containsSymbolGTerm symb) gtrms

containsSymbolGTerm :: Symbol -> GTerm -> Bool
containsSymbolGTerm symb (GBfTerm bf) = containsSymbolBfTerm symb bf
containsSymbolGTerm _ _ = False

containsSymbolBfTerm :: Symbol -> BfTerm -> Bool
containsSymbolBfTerm symb (BfIdentifier ident) = containsSymbolIdent symb ident
containsSymbolBfTerm symb (BfIdentifierBfs ident bfs) =
    containsSymbolIdent symb ident || any (containsSymbolBfTerm symb) bfs
containsSymbolBfTerm _ (BfLiteral _) = False

containsSymbolIdent :: Symbol -> Identifier -> Bool
containsSymbolIdent symb (ISymb symb') = symb == symb'
containsSymbolIdent symb _ = False

