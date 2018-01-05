{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Liquid.Interface where

import G2.Internals.Translation
import G2.Internals.Interface
import G2.Internals.Language as Lang
import G2.Internals.Execution
import G2.Internals.Liquid.Conversion
import G2.Internals.Liquid.CreateFuncs
import G2.Internals.Solver

import qualified Language.Haskell.Liquid.GHC.Interface as LHI
import Language.Haskell.Liquid.Types
import qualified Language.Haskell.Liquid.Types.PrettyPrint as PPR
import Language.Haskell.Liquid.UX.CmdLine
import Language.Fixpoint.Types.PrettyPrint

import Var

import G2.Lib.Printers

-- | findCounterExamples
-- Given (several) LH sources, and a string specifying a function name,
-- attempt to find counterexamples to the functions liquid type
findCounterExamples :: FilePath -> FilePath -> FilePath -> String -> Int -> IO [(State, [Rule], [Expr], Expr)]
findCounterExamples proj primF fp entry steps = do
    ghcInfos <- getGHCInfos [fp]
    let specs = funcSpecs ghcInfos

    (bnds, tycons, cls) <- translateLoaded proj fp primF False
    let init_state = initState bnds tycons cls Nothing Nothing Nothing True entry

    let merged_state = mergeLHSpecState specs init_state

    -- putStrLn $ pprExecStateStr merged_state
    putStrLn $ "tc = " ++ (show $ type_classes merged_state)

    hhp <- getZ3ProcessHandles

    run smt2 hhp steps merged_state

getGHCInfos :: [FilePath] -> IO [GhcInfo]
getGHCInfos fp = do
    config <- getOpts []
    return . fst =<< LHI.getGhcInfos Nothing config fp
    
funcSpecs :: [GhcInfo] -> [(Var, LocSpecType)]
funcSpecs = concatMap (gsTySigs . spec)

pprint :: (Var, LocSpecType) -> IO ()
pprint (v, r) = do
    let i = mkId v

    let doc = PPR.rtypeDoc Full $ val r
    putStrLn $ show i
    putStrLn $ show doc
