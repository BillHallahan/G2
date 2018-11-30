module ToLamG (plugin) where

import GhcPlugins

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = addOutputLamG }

addOutputLamG :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
addOutputLamG _ todo = do
    return $ CoreDoPluginPass "Outputs LamG" outputLamG:todo

outputLamG :: ModGuts -> CoreM ModGuts
outputLamG = return