-- | Haskell Translation
--   This module is used for translating Haskell source files into G2 Core.
--   Everything is slightly broken because we are trying to shove Haskell into
--   G2 Core as hard as possible.
--
--   In particular, we have to do some faking with Haskell's primitive types
--   such as Int# and Double#, which means that the implementation of this
--   this module heavily depends on the GHC version we are working with.
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

import qualified Data.Map    as M
import qualified Data.Monoid as Mon

import qualified G2.Internals.Core.Language       as G2
import qualified G2.Internals.Core.TypeChecker    as G2TC
import qualified G2.Internals.Translation.Prelude as P

-- | Make Raw Core
--   Make a raw GHC Core given a FilePath (String).
--   Alternate the last two lines to let GHC perform optimizations, or not!
mkRawCore :: FilePath -> IO CoreModule
mkRawCore filepath = runGhc (Just libdir) $ do
    setSessionDynFlags =<< getSessionDynFlags
    compileToCoreSimplified filepath  -- Optimizations on.
    -- compileToCoreModule filepath  -- No optimizations.

-- | Make Multiple Cores
--   Make multiple GHC Cores given a list of FilePaths.
mkMultiCore :: [FilePath] -> IO [CoreModule]
mkMultiCore filepaths = mapM mkRawCore filepaths

-- | Outputable to String
--   Basic printing capabilities for converting an Outputable into a String.
outStr :: (Outputable a) => a -> IO String
outStr obj = runGhc (Just libdir) $ do
    flags <- getSessionDynFlags
    return $ showPpr flags obj

-- | Make G2 Core
--   Given a GHC Core, we convert it into a G2 Core.
mkG2Core :: CoreModule -> (G2.TEnv, G2.EEnv)
mkG2Core core = (mkTEnv core, mkEEnv core)

-- | Make Multiple G2 Cores
mkMultiG2Core :: [CoreModule] -> [(G2.TEnv, G2.EEnv)]
mkMultiG2Core cores = map mkG2Core cores

-- | Combine G2 Cores
combineG2Cores :: [(G2.TEnv, G2.EEnv)] -> (G2.TEnv, G2.EEnv)
combineG2Cores cores = foldl pairjoin (M.empty, M.empty) cores
  where pairjoin (acc_t, acc_e) (t, e) = (M.union acc_t t, M.union acc_e e)

-- | Make Name
--   From a GHC Name, make a raw G2 Name.
mkName :: Name -> G2.Name
mkName name = occNameString $ nameOccName name
-- mkName = mkQualName

-- | Make Qualified Name
--   From a GHC Name, make a qualified G2 Name.
mkQualName :: Name -> G2.Name
mkQualName name = let raw_name = occNameString $ nameOccName name
                  in case nameModule_maybe name of
                      Nothing -> raw_name
                      Just md -> (moduleNameString $ moduleName md) ++
                                 ".__." ++ raw_name

--  mkQualName name = case srcSpanFileName_maybe $ nameSrcSpan name of
--     Just fs -> (occNameString $ nameOccName name)  ++ ".__." ++ (unpackFS fs)
--     Nothing -> occNameString $ nameOccName name

-- | Make Type Environment
--   Make the type environment given a GHC Core.
mkTEnv :: CoreModule -> G2.TEnv
mkTEnv (CoreModule mod tenv binds safe) = M.fromList $ map mkADT tycons
  where tycons = filter isAlgTyCon $ typeEnvTyCons tenv

-- | Make Algebraic Data Type
--   Given a type constructor, make the corresonding G2 ADT instance. Returned
--   as a pair in order to make binding into the type environment easier.
mkADT :: TyCon -> (G2.Name, G2.Type)
mkADT algtc = (gname, G2.TyAlg gname gdcs)
  where name  = tyConName algtc
        dcs   = tyConDataCons algtc
        gname = mkName name
        gdcs  = map mkData dcs

-- | Make Data Constructor
--   Make a G2 data constructor from a GHC Core one.
mkData :: DataCon -> G2.DataCon
mkData dc = G2.DataCon dcname dctag (G2.TyConApp tyname []) args
  where tyname = mkName $ tyConName $ dataConTyCon dc
        dcname = mkName $ dataConName dc
        dctag  = dataConTag dc
        args   = map mkType $ dataConOrigArgTys dc

-- | Make Type
--   Make a G2 Type given a GHC Core one.
mkType :: Type -> G2.Type
mkType (TyVarTy var)    = G2.TyVar (mkName $ tyVarName var)
mkType (AppTy t1 t2)    = G2.TyApp (mkType t1) (mkType t2)
mkType (FunTy t1 t2)    = G2.TyFun (mkType t1) (mkType t2)
mkType (ForAllTy v t)   = G2.TyForAll (mkName $ Var.varName v) (mkType t)
mkType (LitTy tl)       = error "Literal types are sketchy?"
mkType (TyConApp tc kt) = case mkName . tyConName $ tc of 
    "Int#" -> G2.TyRawInt
    "Float#" -> G2.TyRawFloat
    "Double#" -> G2.TyRawDouble
    "Char#" -> G2.TyRawChar
    n -> G2.TyConApp n (map mkType kt)

-- | Make Expression Environment
--   Make the expression environment given a GHC Core.
mkEEnv :: CoreModule -> G2.EEnv
mkEEnv (CoreModule mod tenv binds safe) = M.fromList $ concatMap mkBinds binds

-- | Make Bindings
--   Make G2 Binding given a GHC Core binding.
mkBinds :: CoreBind -> [(G2.Name, G2.Expr)]
mkBinds (Rec binds) = map (\(b, e) -> (mkName $ Var.varName b, mkExpr e)) binds
mkBinds (NonRec bndr expr) = [(gname, gexpr)]
  where gname = mkName $ Var.varName bndr
        gexpr = mkExpr expr

-- | Make Expression
--   Make a G2 Expression from a GHC Core Expression.
mkExpr :: CoreExpr -> G2.Expr
mkExpr (Var id)    = G2.Var (mkName $ Var.varName id) (mkType $ varType id)
mkExpr (Lit lit)   = G2.Const (mkLit lit)
mkExpr (App f a)   = G2.App (mkExpr f) (mkExpr a)
mkExpr l@(Lam b e) =
    let ge = mkExpr e
        et = G2TC.exprType ge
        an = mkName $ Var.varName b
    in G2.Lam an ge ((mkType . CU.exprType) l)
mkExpr (Case e b t as) =
    let ex = mkExpr e
        ty = mkType t
    in case recoverCons $ mkType (CU.exprType e) of
        -- This means that the matching expression has a data constructor that
        -- is one of the primitive types. Consequently, we must adapt the rest
        -- of the Alts in order to accommodate for this. We use cascadeAlt in
        -- order to convert every pattern match into a pattern match on Bool
        -- values as opposed to one on constructor structural isomorphism.
        Just dc -> cascadeAlt ex dc (sortAlt as)

        -- Otherwise we are free to make simplifications :)
        Nothing -> G2.App (G2.Lam (mkName $ Var.varName b)
                            (G2.Case ex (map mkAlt as) ty)
                            (G2.TyFun (mkType $ CU.exprType (Var b)) ty))
                          ex
mkExpr (Cast e c) = mkExpr e
mkExpr (Tick t e) = mkExpr e
mkExpr (Type t)   = G2.Type (mkType t)
mkExpr (Let  bs e) = G2.Let (mkBinds bs) (mkExpr e)

-- | Make Literal
--   GHC Core Literals correspond to G2 Consts actually :)
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

-- | Make Alt
--   Make G2 Alt from GHC Core Alt.
mkAlt :: CoreAlt -> (G2.Alt, G2.Expr)
mkAlt (ac, args, exp) = (G2.Alt (mkA ac,map (mkName . Var.varName) args),g2exp)
  where g2exp = mkExpr exp
        mkA (DataAlt dc) = mkData dc
        mkA DEFAULT      = G2.DEFAULT
        mkA (LitAlt lit) = case lit of
            MachChar char  -> P.p_d_char
            MachStr bstr   -> error "Should we even have strings?"
            MachInt int    -> P.p_d_int
            MachInt64 int  -> P.p_d_int
            MachFloat rat  -> P.p_d_float
            MachDouble rat -> P.p_d_double
            otherwise      -> error "Unsupported alt condition."

-- | Sort Alt
--   Propagate DEFAULT data constructors to the back. This is needed for the
--   cascadeAlt function later.
sortAlt :: [CoreAlt] -> [CoreAlt]
sortAlt [] = []
sortAlt ((ac, args, exp):as) = case ac of
    DataAlt dc -> (ac, args, exp) : sortAlt as
    LitAlt lit -> (ac, args, exp) : sortAlt as
    DEFAULT    -> sortAlt as ++ [(ac, args, exp)]

-- | Cascade Alts
--   The goal here is to convert Literal data constructors into equality case
--   matchings on Bools. Rather complicated and annoying.
--   Injection of operators from Internals.Translation.Prelude.
cascadeAlt :: G2.Expr -> G2.DataCon -> [CoreAlt] -> G2.Expr
cascadeAlt mx recon [] = G2.BAD
cascadeAlt mx recon@(G2.DataCon n _ t ts) ((ac, args, exp):as) = case ac of
    DataAlt dc -> error "We should not see non-raw data consturctors here"
    DEFAULT    -> mkExpr exp
    LitAlt lit ->
        G2.Case (G2.App (G2.App (G2.App (G2.App P.op_eq
                                                (G2.Type G2.TyBottom))
                                        P.d_eq)
                                (G2.App (G2.Var n . toTyFun ts $ t) mx))
                        (G2.App (G2.Var n . toTyFun ts $ t)
                                (G2.Const (mkLit lit))))
                  [(G2.Alt (P.p_d_true, []), mkExpr exp)
                  ,(G2.Alt (P.p_d_false, []), cascadeAlt mx recon as)]
                (mkType $ CU.exprType exp)
  where toTyFun :: [G2.Type] -> G2.Type -> G2.Type
        toTyFun [] t = t
        toTyFun (t:[]) t' = G2.TyFun t t'
        toTyFun (t:ts) t' = G2.TyFun t (toTyFun ts t')

-- | Recover Primitive Data Constructors
--   Given a G2 Type, recover the corresponding data constructor that fakes the
--   primitive data constructor of GHC Core.
recoverCons :: G2.Type -> Maybe G2.DataCon
recoverCons G2.TyRawInt    = Just P.p_d_int
recoverCons G2.TyRawFloat  = Just P.p_d_float
recoverCons G2.TyRawDouble = Just P.p_d_double
recoverCons G2.TyRawChar   = Just P.p_d_char
recoverCons otherwise      = Nothing

