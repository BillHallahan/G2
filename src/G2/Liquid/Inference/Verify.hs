{-# LANGUAGE ScopedTypeVariables #-}

module G2.Liquid.Inference.Verify (verify, ghcInfos, lhConfig) where

import GHC
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.UX.CmdLine
import Text.PrettyPrint.HughesPJ

---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- Copied from LiquidHaskell (because checkMany not exported)
import Control.Monad (when)
import qualified Control.Exception as Ex
import HscTypes (SourceError)
import Language.Haskell.Liquid.UX.Annotate
import Language.Haskell.Liquid.UX.Tidy
import Language.Haskell.Liquid.UX.Errors
import qualified Language.Haskell.Liquid.UX.DiffCheck as DC
import Language.Haskell.Liquid.GHC.Interface
import Language.Haskell.Liquid.Constraint.Generate
import Language.Haskell.Liquid.Constraint.ToFixpoint
import Language.Haskell.Liquid.Constraint.Types
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Model
import Language.Fixpoint.Solver
import qualified Language.Fixpoint.Types as F
import CoreSyn
---------------------------------------------------------------------------
---------------------------------------------------------------------------

verify :: Config ->  [GhcInfo] -> IO (Output Doc)
verify cfg ghci = checkMany cfg mempty ghci

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
checkMany :: Config -> Output Doc -> [GhcInfo] -> IO (Output Doc)
checkMany cfg d (g:gs) = do
  d' <- checkOne cfg g
  checkMany cfg (d `mappend` d') gs

checkMany _   d [] =
  return d

checkOne :: Config -> GhcInfo -> IO (Output Doc)
checkOne cfg g = do
  z <- actOrDie $ liquidOne g
  case z of
    Left  e -> exitWithResult cfg [target g] $ mempty { o_result = e }
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

liquidOne :: GhcInfo -> IO (Output Doc)
liquidOne info = do
  let cfg   = getConfig info
  let tgt   = target info
  let cbs' = cbs info
  edcs <- newPrune      cfg cbs' tgt info
  out' <- liquidQueries cfg      tgt info edcs
  DC.saveResult       tgt  out'
  exitWithResult cfg [tgt] out'

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

liquidQueries :: Config -> FilePath -> GhcInfo -> Either [CoreBind] [DC.DiffCheck] -> IO (Output Doc)
liquidQueries cfg tgt info (Left cbs')
  = liquidQuery cfg tgt info (Left cbs')
liquidQueries cfg tgt info (Right dcs)
  = mconcat <$> mapM (liquidQuery cfg tgt info . Right) dcs

liquidQuery   :: Config -> FilePath -> GhcInfo -> Either [CoreBind] DC.DiffCheck -> IO (Output Doc)
liquidQuery cfg tgt info edc = do
  when False (dumpCs cgi)
  -- whenLoud $ mapM_ putStrLn [ "****************** CGInfo ********************"
                            -- , render (pprint cgi)                            ]
  out   <- timedAction names $ solveCs cfg tgt cgi info' names
  return $  mconcat [oldOut, out]
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

instance Show Cinfo where
  show = show . F.toFix

solveCs :: Config -> FilePath -> CGInfo -> GhcInfo -> Maybe [String] -> IO (Output Doc)
solveCs cfg tgt cgi info names = do
  finfo            <- cgInfoFInfo info cgi
  F.Result r sol _ <- solve (fixConfig tgt cfg) finfo :: IO (F.Result (Integer, Cinfo))
  let resErr        = applySolution sol . cinfoError . snd <$> r
  resModel_        <- fmap (e2u sol) <$> getModels info cfg resErr
  let resModel      = resModel_  `addErrors` (e2u sol <$> logErrors cgi)
  let out0          = mkOutput cfg resModel sol (annotMap cgi)

  case r of
    F.Unsafe xs -> mapM_ (\(_, Ci _ err v) -> putStrLn ("\nv = " ++ show v ++ "\n")) xs
    _ -> return ()
  return            $ out0 { o_vars    = names    }
                           { o_result  = resModel }

solveCs' :: Config -> FilePath -> CGInfo -> GhcInfo -> Maybe [String] -> IO (F.Result (Integer, Cinfo))
solveCs' cfg tgt cgi info names = do
  finfo            <- cgInfoFInfo info cgi
  fres@(F.Result r sol _) <- solve (fixConfig tgt cfg) finfo
  return fres

e2u :: F.FixSolution -> Error -> UserError
e2u s = fmap F.pprint . tidyError s
