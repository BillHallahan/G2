module G2.QuasiQuotes.ModuleGraphLoader
  where

import Language.Haskell.TH.Syntax as TH

import GHC
import GHC.Paths
import Outputable


-- | Make IO String from Outputable
--   Simple print dump.
mkIOStr :: (Outputable a) => a -> IO String
mkIOStr obj = runGhc (Just libdir) $ do
    -- Appropriate dynamic flags not relevant here.
    dflags <- getSessionDynFlags
    let ppr_str = showPpr dflags obj
    return ppr_str


guessModules :: [TH.Module] -> IO [String]
guessModules mods = do
  let modNames = map (\(Module _ (ModName name)) -> name) mods
  targets <- runGhc (Just libdir) $ do
      mapM ((flip guessTarget) Nothing) modNames

  mapM mkIOStr targets

