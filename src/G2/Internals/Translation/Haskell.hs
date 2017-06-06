module G2.Internals.Translation.Haskell where

import ConLike
import CoreMonad
import CoreSubst
import CoreSyn
import CoreUtils as CU
import Data.List
import DataCon
import FastString
import GHC
import GHC.Paths
import HscTypes
import Literal
import Name
import Outputable
import SrcLoc
import TyCon
import Type
import TypeRep
import Var

import G2.Internals.Core.CoreManipulator
import qualified G2.Internals.Core.Language as G2
import qualified G2.Internals.Core.Utils as G2CU
import qualified G2.Internals.Translation.Prelude as P

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
-- mkName = mkQualName

mkQualName :: Name -> G2.Name
mkQualName name = case srcSpanFileName_maybe $ nameSrcSpan name of
    Just fs -> (occNameString $ nameOccName name)  ++ ".__." ++ (unpackFS fs)
    Nothing -> occNameString $ nameOccName name

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
mkDC dc = G2.DataCon dcname dctag (G2.TyConApp tyname []) args
  where tyname = mkName $ tyConName $ dataConTyCon dc
        dcname = mkName $ dataConName dc
        dctag  = dataConTag dc
        args   = map mkType $ dataConOrigArgTys dc

mkType :: Type -> G2.Type
mkType (TyVarTy var)    = G2.TyVar (mkName $ tyVarName var)
mkType (AppTy t1 t2)    = G2.TyApp (mkType t1) (mkType t2)
mkType (TyConApp tc kt) = 
    case mkName . tyConName $ tc of 
        "Int#" -> G2.TyRawInt
        "Float#" -> G2.TyRawFloat
        "Double#" -> G2.TyRawDouble
        "Char#" -> G2.TyRawChar
        n -> G2.TyConApp n (map mkType kt)
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
                         et = G2CU.exprType ge
                         an = mkName $ Var.varName b
                   in G2.Lam an ge (mkType . CU.exprType $ l)
{-
mkExpr (Case e b t as) = let ex = mkExpr e
                             ls = map mkAlt as
                             ty = mkType t
             in G2.App (G2.Lam (mkName $ Var.varName b)
                               (G2.Case ex ls ty)
                               (G2.TyFun (mkType $ CU.exprType (Var b)) ty)) ex
-}
mkExpr (Case e b t as) = let ex = mkExpr e
                             ty = mkType t
                         in case recoverCons $ mkType (CU.exprType e) of
      Nothing -> G2.App (G2.Lam (mkName $ Var.varName b)
                                (G2.Case ex (map mkAlt as) ty)
                                (G2.TyFun (mkType $ CU.exprType (Var b)) ty)) ex
      Just dc -> cascadeAlt ex dc (sortAlt as)

mkExpr (Cast e c) = mkExpr e
mkExpr (Tick t e) = mkExpr e
mkExpr (Type t)   = G2.Type (mkType t)
mkExpr (Let  bs e) = G2.Let (mkBind bs) (mkExpr e)

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
        mkA DEFAULT      = G2.DEFAULT
        mkA (LitAlt lit) = case lit of
            MachChar char  -> P.p_d_char
            MachStr bstr   -> error "Should we even have strings?"
            MachInt int    -> P.p_d_int
            MachInt64 int  -> P.p_d_int
            MachFloat rat  -> P.p_d_float
            MachDouble rat -> P.p_d_double
            otherwise      -> error "Unsupported alt condition."

sortAlt :: [CoreAlt] -> [CoreAlt]
sortAlt [] = []
sortAlt ((ac, args, exp):as) = case ac of
    DataAlt dc -> (ac, args, exp) : sortAlt as
    LitAlt lit -> (ac, args, exp) : sortAlt as
    DEFAULT    -> sortAlt as ++ [(ac, args, exp)]

cascadeAlt :: G2.Expr -> G2.DataCon -> [CoreAlt] -> G2.Expr
cascadeAlt mx recon [] = G2.BAD
cascadeAlt mx recon@(G2.DataCon n _ t ts) ((ac, args, exp):as) = case ac of
    DataAlt dc -> error "We should not see non-raw data consturctors here"
    DEFAULT    -> mkExpr exp
    LitAlt lit -> G2.Case (G2.App (G2.App (G2.App (G2.App P.op_eq
                                                          (G2.Type G2.TyBottom))
                                                  P.d_eq)
                                          (G2.App (G2.Var n . toTyFun ts $ t) mx))--(G2.App (G2.DCon recon) mx))
                                  (G2.App (G2.Var n . toTyFun ts $ t)--(G2.App (G2.DCon recon)
                                          (G2.Const (mkLit lit))))
                          [(G2.Alt (P.p_d_true, []), mkExpr exp),
                           (G2.Alt (P.p_d_false, []), cascadeAlt mx recon as)]
                          (mkType $ CU.exprType exp)
    where
        toTyFun :: [G2.Type] -> G2.Type -> G2.Type
        toTyFun [] t' = t'
        toTyFun (t:[]) t' = G2.TyFun t t'
        toTyFun (t:ts) t' = G2.TyFun t (toTyFun ts t')

recoverCons :: G2.Type -> Maybe G2.DataCon
recoverCons G2.TyRawInt    = Just P.p_d_int
recoverCons G2.TyRawFloat  = Just P.p_d_float
recoverCons G2.TyRawDouble = Just P.p_d_double
recoverCons G2.TyRawChar   = Just P.p_d_char
recoverCons otherwise      = Nothing

{-
recoverCons (G2.TyConApp "Int#" [])    = Just P.p_d_int
recoverCons (G2.TyConApp "Float#" [])  = Just P.p_d_float
recoverCons (G2.TyConApp "Double#" []) = Just P.p_d_double
recoverCons (G2.TyConApp "Char#" [])   = Just P.p_d_char
recoverCons otherwise = if otherwise `elem` [(G2.TyConApp "Peano" [])
                                            ,(G2.TyConApp "Bool" [])
                                            ,(G2.TyConApp "Int" [])]
                        then Nothing
                        else error $ "HEREEREREREE: " ++ show otherwise
-}

