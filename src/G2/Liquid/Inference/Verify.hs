{-# LANGUAGE ScopedTypeVariables #-}

module G2.Liquid.Inference.Verify ( VerifyResult (..)
                                  , verifyVarToName
                                  , tryHardToVerifyIgnoring
                                  , checkGSCorrect
                                  , verify
                                  , ghcInfos
                                  , lhConfig) where

import qualified G2.Language.Syntax as G2
import G2.Liquid.Helpers
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.GeneratedSpecs
import G2.Translation.Haskell

import Data.Maybe
import GHC
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.UX.CmdLine
import Text.PrettyPrint.HughesPJ
import qualified Var as V
---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- Copied from LiquidHaskell (because checkMany not exported)
import Control.Monad (when)
import qualified Control.Exception as Ex
import HscTypes (SourceError)
import Language.Haskell.Liquid.UX.Tidy
import qualified Language.Haskell.Liquid.UX.DiffCheck as DC
import Language.Haskell.Liquid.GHC.Interface
import Language.Haskell.Liquid.Constraint.Generate
import Language.Haskell.Liquid.Constraint.ToFixpoint
import Language.Haskell.Liquid.Constraint.Types
import Language.Haskell.Liquid.Misc
import Language.Fixpoint.Solver
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Errors as F (FixResult (..))
import CoreSyn

-- For Show instance of Cinfo
import Language.Haskell.Liquid.Liquid ()

---------------------------------------------------------------------------
---------------------------------------------------------------------------

data VerifyResult v = Safe
                    | Crash [(Integer, Cinfo)] String
                    | Unsafe [v]

verifyVarToName :: VerifyResult V.Var -> VerifyResult G2.Name
verifyVarToName Safe = Safe
verifyVarToName (Crash ic s) = Crash ic s
verifyVarToName (Unsafe v) = Unsafe (map varToName v)

-- Tries to verify the assertions, specifically for the set of functions,
-- that we care about. If that fails, removes any synthesized
-- assertions/assumptions on the failing functions.
tryHardToVerifyIgnoring :: InferenceConfig
                        -> Config
                        -> [GhcInfo]
                        -> GeneratedSpecs
                        -> GeneratedSpecs
                        -> [G2.Name]
                        -> IO (Either [G2.Name] GeneratedSpecs)
tryHardToVerifyIgnoring infconfig lhconfig ghci gs lower_gs ignore = do
    let both_gs = unionDroppingGS gs lower_gs
    let merged_ghci = addSpecsToGhcInfos ghci both_gs

    putStrLn "---\nVerify"
    putStrLn "gsAsmSigs"
    mapM_ (print . gsAsmSigs . spec) merged_ghci
    putStrLn "gsTySigs"
    mapM_ (print . gsTySigs . spec) merged_ghci
    putStrLn "---\nEnd Verify"

    res <- return . verifyVarToName =<< verify infconfig lhconfig merged_ghci
    case res of
        Unsafe ns
          | f_ns <- filterIgnoring ns
          , f_ns /= [] -> do
            let f_gs = filterOutSpecs f_ns gs
                f_both_gs = filterOutSpecs f_ns both_gs
                f_merged_ghci = addSpecsToGhcInfos ghci f_both_gs

            filtered_res <- return . verifyVarToName =<<
                                        verify infconfig lhconfig f_merged_ghci
            case filtered_res of
                Unsafe _ -> return $ Left f_ns
                Safe -> return $ Right f_gs
                Crash ci err -> error $ "Crash\n" ++ show ci ++ "\n" ++ err
          | otherwise -> return $ Right gs
        Safe -> return $ Right gs
        Crash ci err -> error $ "Crash\n" ++ show ci ++ "\n" ++ err
    where
        ignore' = map (\(G2.Name n m _ _) -> (n, m)) ignore
        filterIgnoring = filter (\(G2.Name n m _ _) -> (n, m) `notElem` ignore')

-- | Confirm that we have actually found exactly the needed specs
checkGSCorrect :: InferenceConfig -> Config -> [GhcInfo] -> GeneratedSpecs -> IO (VerifyResult V.Var)
checkGSCorrect infconfig lhconfig ghci gs
    | nullAssumeGS gs = do
        let merged_ghci = addSpecsToGhcInfos ghci gs
        verify infconfig lhconfig merged_ghci
    | otherwise = error "Non-null assumes."

verify :: InferenceConfig -> Config ->  [GhcInfo] -> IO (VerifyResult V.Var)
verify infconfig cfg ghci = do
    r <- verify' infconfig cfg ghci
    case F.resStatus r of
        F.Safe -> return Safe
        F.Crash ci err -> return $ Crash ci err
        F.Unsafe bad -> return . Unsafe . catMaybes $ map (ci_var . snd) bad


verify' :: InferenceConfig -> Config ->  [GhcInfo] -> IO (F.Result (Integer, Cinfo))
verify' infconfig cfg ghci = checkMany infconfig cfg mempty ghci

ghcInfos :: Maybe HscEnv -> Config -> [FilePath] -> IO [GhcInfo]
ghcInfos me cfg fp = do
    (ghci, _) <- getGhcInfos me cfg fp
    return ghci

lhConfig :: [FilePath] -> [FilePath] -> IO Config
lhConfig  proj lhlibs = do
    config <- getOpts []
    return config { idirs = idirs config ++ proj ++ lhlibs
                  , files = files config ++ lhlibs
                  , ghcOptions = ["-v"]}

---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- Copied from LiquidHaskell (because checkMany not exported)
checkMany :: InferenceConfig -> Config -> F.Result (Integer, Cinfo) -> [GhcInfo] -> IO (F.Result (Integer, Cinfo))
checkMany infconfig cfg d (g:gs) = do
  d' <- checkOne infconfig cfg g
  checkMany infconfig cfg (d `mappend` d') gs

checkMany _ _  d [] =
  return d

checkOne :: InferenceConfig -> Config -> GhcInfo -> IO (F.Result (Integer, Cinfo))
checkOne infconfig cfg g = do
  z <- actOrDie $ liquidOne infconfig g
  case z of
    Left  e -> undefined
    Right r -> return r


actOrDie :: IO a -> IO (Either ErrorResult a)
actOrDie act =
    (Right <$> act)
      `Ex.catch` (\(e :: SourceError) -> handle e)
      `Ex.catch` (\(e :: Error)       -> handle e)
      `Ex.catch` (\(e :: UserError)   -> handle e)
      `Ex.catch` (\(e :: [Error])     -> handle e)

handle :: (Result a) => a -> IO (Either ErrorResult b)
handle = return . Left . result

liquidOne :: InferenceConfig -> GhcInfo -> IO (F.Result (Integer, Cinfo))
liquidOne infconfig info = do
  let cfg   = getConfig info
  let tgt   = target info
  let cbs' = cbs info
  edcs <- newPrune      cfg cbs' tgt info
  liquidQueries infconfig cfg      tgt info edcs

newPrune :: Config -> [CoreBind] -> FilePath -> GhcInfo -> IO (Either [CoreBind] [DC.DiffCheck])
newPrune cfg cbs tgt info
  | not (null vs) = return . Right $ [DC.thin cbs sp vs]
  | timeBinds cfg = return . Right $ [DC.thin cbs sp [v] | v <- exportedVars info ]
  | diffcheck cfg = maybeEither cbs <$> DC.slice tgt cbs sp
  | otherwise     = return  (Left cbs)
  where
    vs            = gsTgtVars sp
    sp            = spec    info

maybeEither :: a -> Maybe b -> Either a [b]
maybeEither d Nothing  = Left d
maybeEither _ (Just x) = Right [x]

liquidQueries :: InferenceConfig -> Config -> FilePath -> GhcInfo -> Either [CoreBind] [DC.DiffCheck] -> IO (F.Result (Integer, Cinfo))
liquidQueries infconfig cfg tgt info (Left cbs')
  = liquidQuery infconfig cfg tgt info (Left cbs')
liquidQueries infconfig cfg tgt info (Right dcs)
  = mconcat <$> mapM (liquidQuery infconfig cfg tgt info . Right) dcs

liquidQuery   :: InferenceConfig -> Config -> FilePath -> GhcInfo -> Either [CoreBind] DC.DiffCheck -> IO (F.Result (Integer, Cinfo))
liquidQuery infconfig cfg tgt info edc = do
  when False (dumpCs cgi)
  -- whenLoud $ mapM_ putStrLn [ "****************** CGInfo ********************"
                            -- , render (pprint cgi)                            ]
  timedAction names $ solveCs infconfig cfg tgt cgi info'
  where
    cgi    = {-# SCC "generateConstraints" #-} generateConstraints $! info' {cbs = cbs''}
    cbs''  = either id              DC.newBinds                        edc
    info'  = either (const info)    (\z -> info {spec = DC.newSpec z}) edc
    names  = either (const Nothing) (Just . map show . DC.checkedVars) edc
    oldOut = either (const mempty)  DC.oldOutput                       edc

dumpCs :: CGInfo -> IO ()
dumpCs cgi = do
  putStrLn "***************************** SubCs *******************************"
  putStrLn $ render $ pprintMany (hsCs cgi)
  putStrLn "***************************** FixCs *******************************"
  putStrLn $ render $ pprintMany (fixCs cgi)
  putStrLn "***************************** WfCs ********************************"
  putStrLn $ render $ pprintMany (hsWfs cgi)

pprintMany :: (PPrint a) => [a] -> Doc
pprintMany xs = vcat [ F.pprint x $+$ text " " | x <- xs ]

-- instance Show Cinfo where
--   show = show . F.toFix

solveCs :: InferenceConfig -> Config -> FilePath -> CGInfo -> GhcInfo -> IO (F.Result (Integer, Cinfo))
solveCs infconfig cfg tgt cgi info = do
  finfo <- cgInfoFInfo info cgi
  -- We only want qualifiers we have found with G2 Inference, so we have to force the correct set here
  let finfo' = finfo { F.quals = (gsQualifiers . spec $ info) ++ if keep_quals infconfig then F.quals finfo else [] }
  solve (fixConfig tgt cfg) finfo'
