module G2.Haskell.Translator where

import ConLike
import CoreMonad
import CoreSubst
import CoreSyn
import Data.List
import DataCon
import DynFlags
import FloatOut
import GHC
import GHC.Paths
import HscTypes
import qualified G2.Core.Language as G2
import Literal
import Name
import OccName
import Outputable
import TyCon
import Type
import TypeRep
import Unique
import UniqFM
import UniqSupply
import Var

{- Raw Core Extraction

This is primarily because we might need to run additional passes of filtering
and lifting on Core Haskell.
-}
mkRawCore :: FilePath -> IO CoreModule
mkRawCore filepath = runGhc (Just libdir) $ do
    setSessionDynFlags =<< getSessionDynFlags
    compileToCoreSimplified filepath

{- Outputable to String

Basic printing capabilities of converting an Outputable into a String.
-}
outStr :: (Outputable a) => a -> IO String
outStr obj = runGhc (Just libdir) $ do
    flags <- getSessionDynFlags
    return $ showPpr flags obj

{- G2Core

Pipeline the raw core results (after liftings?) into making the G2 Core.
-}
mkG2Core :: CoreModule -> (G2.TEnv, G2.EEnv)
mkG2Core core = (mkTEnv core, mkEEnv core)

----
{- Type Extraction

We want to extract out ADT bindings from the type environment.

Maybe we are also interested in other functions
-}
mkTEnv :: CoreModule -> G2.TEnv
mkTEnv (CoreModule mod types binds safe) = undefined 



----

mkEEnv :: CoreModule -> G2.EEnv
mkEEnv (CoreModule mod types binds safe) = undefined
