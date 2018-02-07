{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Liquid.Interface where

import G2.Internals.Translation
import G2.Internals.Interface
import G2.Internals.Language as Lang
import G2.Internals.Execution
import G2.Internals.Liquid.Conversion
import G2.Internals.Liquid.Measures
import G2.Internals.Liquid.ElimPartialApp
import G2.Internals.Liquid.SimplifyAsserts
import G2.Internals.Liquid.TCGen
import G2.Internals.Solver

import qualified Language.Haskell.Liquid.GHC.Interface as LHI
import Language.Haskell.Liquid.Types
import qualified Language.Haskell.Liquid.Types.PrettyPrint as PPR
import Language.Haskell.Liquid.UX.CmdLine
import Language.Fixpoint.Types.PrettyPrint as FPP

import Data.Coerce
import qualified Data.Map as M
import qualified Data.Text as T

import qualified GHC as GHC
import Var

import G2.Internals.Language.KnownValues

-- | findCounterExamples
-- Given (several) LH sources, and a string specifying a function name,
-- attempt to find counterexamples to the functions liquid type
findCounterExamples :: FilePath -> FilePath -> FilePath -> T.Text -> Maybe FilePath -> Int -> IO [(State, [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))]
findCounterExamples proj primF fp entry m_mapsrc steps = do
    ghcInfos <- getGHCInfos proj [fp]
    let specs = funcSpecs ghcInfos
    let lh_measures = measureSpecs ghcInfos

    (mod_name, pre_bnds, pre_tycons, pre_cls) <- translateLoaded proj fp primF False m_mapsrc
    let (bnds, tycons, cl) = (pre_bnds, pre_tycons, pre_cls)
    
    let init_state = initState bnds tycons cl Nothing Nothing Nothing True entry (Just mod_name)

    -- We filter the State to clean up the expr env
    -- We can't do this to the Types, because we don't know what the measures
    -- will require.
    let cleaned_state = (markAndSweepPreserving (reqNames init_state) init_state) {type_env = type_env init_state}
    let no_part_state = elimPartialApp cleaned_state

    let (lh_state, tcv) = createLHTC no_part_state


    let lhtc_state = addLHTC lh_state tcv
    let measure_state = createMeasures lh_measures tcv lhtc_state

    let (merged_state, mkv) = mergeLHSpecState specs measure_state tcv

    hhp <- getZ3ProcessHandles

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

reqNames :: State -> [Name]
reqNames (State { expr_env = eenv
                , type_classes = tc
                , known_values = kv }) = 
    Lang.names [ mkGe eenv
               , mkGt eenv
               , mkEq eenv
               , mkNeq eenv
               , mkLt eenv
               , mkLe eenv
               , mkAnd eenv
               , mkOr eenv
               , mkNot eenv
               , mkPlus eenv
               , mkMinus eenv
               , mkMult eenv
               -- , mkDiv eenv
               -- , mkMod eenv
               , mkNegate eenv
               , mkImplies eenv
               , mkIff eenv
               , mkFromInteger eenv
               -- , mkToInteger eenv
               ]
    ++
    Lang.names (M.filterWithKey (\k _ -> k == eqTC kv || k == numTC kv || k == ordTC kv) (coerce tc :: M.Map Name Class))

pprint :: (Var, LocSpecType) -> IO ()
pprint (v, r) = do
    let i = mkIdUnsafe v

    let doc = PPR.rtypeDoc Full $ val r
    putStrLn $ show i
    putStrLn $ show doc
