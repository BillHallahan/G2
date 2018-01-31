{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Liquid.Interface where

import G2.Internals.Translation
import G2.Internals.Interface
import G2.Internals.Language as Lang
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Execution
import G2.Internals.Liquid.Conversion
import G2.Internals.Liquid.CreateFuncs
import G2.Internals.Liquid.CreateMeasures
import G2.Internals.Liquid.ElimPartialApp
import G2.Internals.Liquid.SimplifyAsserts
import G2.Internals.Liquid.TCGen
import G2.Internals.Liquid.TCValues
import G2.Internals.Solver

import qualified Language.Haskell.Liquid.GHC.Interface as LHI
import Language.Haskell.Liquid.Types
import qualified Language.Haskell.Liquid.Types.PrettyPrint as PPR
import Language.Haskell.Liquid.UX.CmdLine
import  Language.Fixpoint.Types.Names
import Language.Fixpoint.Types.PrettyPrint as FPP

import Data.Time

import qualified GHC as GHC
import Var

import G2.Lib.Printers

import G2.Internals.Language.KnownValues

-- | findCounterExamples
-- Given (several) LH sources, and a string specifying a function name,
-- attempt to find counterexamples to the functions liquid type
findCounterExamples :: FilePath -> FilePath -> FilePath -> String -> Maybe FilePath -> Int -> IO [(State, [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))]
findCounterExamples proj primF fp entry m_mapsrc steps = do
    ghcInfos <- getGHCInfos proj [fp]
    let specs = funcSpecs ghcInfos
    let measures = measureSpecs ghcInfos

    (mod_name, pre_bnds, pre_tycons, pre_cls) <- translateLoaded proj fp primF False m_mapsrc
    let (bnds, tycons, cls) = (pre_bnds, pre_tycons, pre_cls)
    
    let init_state = initState bnds tycons cls Nothing Nothing Nothing True entry (Just mod_name)

    -- mapM_ (putStrLn . show . idName . fst) $ concatMap id bnds

    -- timedMsg "state inited"

    -- let init_state' = elimPartialApp init_state
    let no_part_state = elimPartialApp init_state

    -- timedMsg "state cleaned"

    let (lh_state, eq_walkers, tcv) = createLHTC no_part_state

    let measure_state = lh_state
    -- let measure_state = createMeasures measures tcv lh_state

    let lhtc_state = addLHTC measure_state tcv

    -- putStrLn $ pprExecStateStr lhtc_state

    let (merged_state, mkv) = mergeLHSpecState specs lhtc_state tcv
    -- putStrLn $ pprExecStateStr merged_state

    hhp <- getZ3ProcessHandles

    -- let beta_red_state = merged_state
    let beta_red_state = simplifyAsserts mkv merged_state

    run smt2 hhp steps beta_red_state

getGHCInfos :: FilePath -> [FilePath] -> IO [GhcInfo]
getGHCInfos proj fp = do
    config <- getOpts []
    let config' = config {idirs = idirs config ++ [proj], ghcOptions = ["-v"]}
    return . fst =<< LHI.getGhcInfos Nothing config' fp
    
funcSpecs :: [GhcInfo] -> [(Var, LocSpecType)]
funcSpecs = concatMap (gsTySigs . spec)

measureSpecs :: [GhcInfo] -> [Measure SpecType GHC.DataCon]
measureSpecs = concatMap (gsMeasures . spec)

pprint :: (Var, LocSpecType) -> IO ()
pprint (v, r) = do
    let i = mkId v

    let doc = PPR.rtypeDoc Full $ val r
    putStrLn $ show i
    putStrLn $ show doc
