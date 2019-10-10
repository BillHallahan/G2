module G2.Liquid.Inference.Interface (inference) where

import G2.Liquid.Inference.Verify

import Language.Fixpoint.Types.Errors (FixResult (..))
import Language.Haskell.Liquid.Types

inference :: [FilePath] -> [FilePath] -> [FilePath] -> IO ()
inference proj fp lhlibs = do
    config <- lhConfig proj lhlibs
    ghci <- ghcInfos Nothing config fp

    res <- verify config ghci

    case o_result res of
        Safe -> putStrLn "Safe"
        Crash _ _ -> putStrLn "Crash"
        Unsafe bad -> do putStrLn "Unsafe"
            -- putStrLn "\n\no_types"
            -- print $ o_types res
            -- putStrLn "\n\no_templs"
            -- print $ o_templs res
            -- putStrLn "\n\no_bots"
            -- print $ o_bots res
            -- putStrLn "\n\nbad"
            -- print bad