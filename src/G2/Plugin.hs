module G2.Plugin (plugin) where

import G2.Config
import G2.Translation

import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import GhcPlugins
import System.Directory
import System.FilePath

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = addOutputLamG }

addOutputLamG :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
addOutputLamG cl todo = do
    let fdr = strArg "out" cl M.empty id "g2_out"
    return $ todo ++ [CoreDoPluginPass "Outputs LamG" (outputLamG fdr)]

outputLamG :: FilePath -> ModGuts -> CoreM ModGuts
outputLamG fdr mg = do
    liftIO $ createDirectoryIfMissing True fdr

    -- Write the information needed by G2
    let name = moduleNameString . moduleName . mg_module $ mg
    hsc <- getHscEnv
    c <- liftIO $ hskToG2 HM.empty HM.empty =<< mkCompileClosure hsc [mg]
    liftIO $ writeFile (fdr </> name ++ ".g2i") (show c)

    return mg