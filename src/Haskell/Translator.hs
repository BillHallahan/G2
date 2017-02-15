module G2.Haskell.Translator where

import ConLike
import CoreMonad
import CoreSubst
import CoreSyn
import CoreUtils as CU
import Data.List
import DataCon
import GHC
import GHC.Paths
import HscTypes
import Literal
import Name
import Outputable
import TyCon
import Type
import TypeRep
import Var

import G2.Core.CoreManipulator
import qualified G2.Core.Language as G2
import qualified G2.Haskell.Prelude as P
import G2.Core.Utils

import qualified Data.Map as M

import qualified Data.Monoid as Mon

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
mkTEnv (CoreModule mod tenv binds safe) = M.fromList $ map mkADT tycons
  where tycons = filter isAlgTyCon $ typeEnvTyCons tenv

mkADT :: TyCon -> (G2.Name, G2.Type)
mkADT algtc = (gname, G2.TyAlg gname gdcs)
  where name  = tyConName algtc
        dcs   = tyConDataCons algtc
        gname = mkName name
        gdcs  = map mkDC dcs

mkDC :: DataCon -> G2.DataCon
mkDC dc = G2.DC (dcname, dctag, G2.TyConApp tyname [], args)
  where tyname = mkName $ tyConName $ dataConTyCon dc
        dcname = mkName $ dataConName dc
        dctag  = dataConTag dc
        args   = map mkType $ dataConOrigArgTys dc

mkType :: Type -> G2.Type
mkType (TyVarTy var)    = G2.TyVar (mkName $ tyVarName var)
mkType (AppTy t1 t2)    = G2.TyApp (mkType t1) (mkType t2)
mkType (TyConApp tc kt) = G2.TyConApp (mkName $ tyConName tc) (map mkType kt)
mkType (FunTy t1 t2)    = G2.TyFun (mkType t1) (mkType t2)
mkType (ForAllTy v t)   = G2.TyForAll (mkName $ Var.varName v) (mkType t)
mkType (LitTy tl)       = error "Literal types are sketchy?"

-------

mkEEnv :: CoreModule -> G2.EEnv
mkEEnv (CoreModule mod tenv binds safe) = M.fromList $ concatMap mkBind binds

mkBind :: CoreBind -> [(G2.Name, G2.Expr)]
mkBind (Rec binds) = map (\(b, e) -> (mkName $ Var.varName b, mkExpr e)) binds
mkBind (NonRec bndr expr) = [(gname, gexpr)]
  where gname = mkName $ Var.varName bndr
        gexpr = mkExpr expr

mkExpr :: CoreExpr -> G2.Expr
mkExpr (Var id)  = G2.Var (mkName $ Var.varName id) (mkType $ varType id)
mkExpr (Lit lit) = G2.Const (mkLit lit)
mkExpr (App f a) = G2.App (mkExpr f) (mkExpr a)
mkExpr l@(Lam b e) = let ge = mkExpr e
                         et = typeOf ge
                         an = mkName $ Var.varName b

                   in G2.Lam an ge (mkType . CU.exprType $ l)
mkExpr (Case e b t as) = G2.Case (mkExpr e) (map mkAlt as) (mkType t)
mkExpr (Cast e c) = mkExpr e
mkExpr (Tick t e) = mkExpr e
mkExpr (Type t)   = G2.Type (mkType t)
mkExpr (Let b e)  = error "We should have lifted lets out"

mkLit :: Literal -> G2.Const
mkLit (MachChar char)  = G2.CChar char
mkLit (MachStr bytstr) = G2.CString (show bytstr)
mkLit (MachInt int)    = G2.CInt (fromInteger int)
mkLit (MachInt64 int)  = G2.CInt (fromInteger int)
mkLit (MachWord int)   = G2.CInt (fromInteger int)
mkLit (MachWord64 int) = G2.CInt (fromInteger int)
mkLit (MachFloat rat)  = G2.CFloat rat
mkLit (MachDouble rat) = G2.CDouble rat
mkLit (LitInteger i t) = G2.CInt (fromInteger i)
mkLit otherwise        = error "No other lits please?"

mkAlt :: CoreAlt -> (G2.Alt, G2.Expr)
mkAlt (ac, args, exp) = (G2.Alt (mkA ac, map (mkName . Var.varName) args), mkExpr exp)
  where mkA (DataAlt dc) = mkDC dc
        mkA DEFAULT      = P.dc_default
        mkA (LitAlt lit) = case lit of
            MachChar char  -> P.p_d_char
            MachStr bstr   -> error "Should we even have strings?"
            MachInt int    -> P.p_d_int
            MachInt64 int  -> P.p_d_int
            MachFloat rat  -> P.p_d_float
            MachDouble rat -> P.p_d_double
            otherwise      -> error "Unsupported alt condition."