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

import qualified Data.Map as M

{- Raw Core Extraction

This is primarily because we might need to run additional passes of filtering
and lifting on Core Haskell.
-}
mkRawCore :: FilePath -> IO CoreModule
mkRawCore filepath = runGhc (Just libdir) $ do
    setSessionDynFlags =<< getSessionDynFlags
    compileToCoreSimplified filepath
    -- compileToCoreModule filepath

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
mkName :: Name -> G2.Name
mkName name = occNameString $ nameOccName name

{- Type Extraction

We want to extract out ADT bindings from the type environment.

Maybe we are also interested in other functions
-}
mkTEnv :: CoreModule -> G2.TEnv
mkTEnv (CoreModule mod tenv binds safe) = M.fromList $ map mkADTs tycons
  where tycons = filter isAlgTyCon $ typeEnvTyCons tenv


mkADTs :: TyCon -> (G2.Name, G2.Type)
mkADTs algtc = (gname, G2.TyAlg gname gdcs)
  where name  = tyConName algtc
        dcs   = tyConDataCons algtc
        gname = mkName name
        gdcs  = map (\d -> mkDC gname d) dcs

mkDC :: G2.Name -> DataCon -> G2.DataCon
mkDC tyname dc = (dcname, dctag, G2.TyConApp tyname [], args)
  where dcname = mkName $ dataConName dc
        dctag  = dataConTag dc
        args   = map mkType $ dataConOrigArgTys dc


mkType :: Type -> G2.Type
mkType (TyVarTy var)    = G2.TyVar (mkName $ tyVarName var)
mkType (AppTy t1 t2)    = G2.TyApp (mkType t1) (mkType t2)
mkType (TyConApp tc kt) = G2.TyConApp (mkName $ tyConName tc) (map mkType kt)
mkType (FunTy t1 t2)    = G2.TyFun (mkType t1) (mkType t2)
mkType (ForAllTy v t)   = undefined
mkType (LitTy tl)       = undefined


-------

mkEEnv :: CoreModule -> G2.EEnv
mkEEnv (CoreModule mod tenv binds safe) = M.fromList []
