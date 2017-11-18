{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Liquid.Interface where

import G2.Internals.Translation.Haskell

import qualified Language.Haskell.Liquid.GHC.Interface as LHI
import Language.Haskell.Liquid.Liquid
import Language.Haskell.Liquid.Types
import qualified Language.Haskell.Liquid.Types.PrettyPrint as PPR
import Language.Fixpoint.Types.PrettyPrint
import Language.Fixpoint.Types.Spans
import Language.Haskell.Liquid.UX.CmdLine 

import Var

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