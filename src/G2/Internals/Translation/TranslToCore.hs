-- Converts the core defined in G2.Internals.Translation.Language to
-- the core defined in G2.Internals.Core.Language

module G2.Internals.Translation.TranslToCore
    () where

{-
    
    ( transl
    , namesMapTEEnv
    , namesMapCons) where

import G2.Internals.Core.Language
import qualified G2.Internals.Translation.Language as TL

import qualified Data.Map as M

-- This ensures uniqueness per tuple, and that equal tuples generate equal names
translName :: TL.TName -> Name
translName (n, i) = n ++ "_" ++ show i

transl :: TL.TTEnv -> TL.TEEnv -> (TEnv, EEnv)
transl tenv eenv =
    let
        tenv' = translTEnv tenv
        eenv' = translEEnv eenv
    in
    (tenv', eenv')

translEEnv :: TL.TEEnv -> EEnv
translEEnv = M.map translExpr . M.mapKeys translName

translTEnv :: TL.TTEnv -> TEnv
translTEnv = M.map translType . M.mapKeys translName

translExpr :: TL.TExpr -> Expr
translExpr (TL.Var n t) = Var (translName n) (translType t)
translExpr (TL.Const c) = Const c
translExpr (TL.Prim p t) = Prim p (translType t)
translExpr (TL.Lam n e t) = Lam (translName n) (translExpr e) (translType t)
translExpr (TL.Let bx e) = Let (map (\(n, e') -> (translName n, translExpr e')) bx) (translExpr e)
translExpr (TL.App e e') = App (translExpr e) (translExpr e')
translExpr (TL.Data d) = Data (translDataCon d)
translExpr (TL.Case e ae t) =
    Case (translExpr e) (map (\(a, e') -> (translAlt a, translExpr e')) ae) (translType t)
translExpr (TL.Type t) = Type (translType t)
translExpr (TL.Assume e e') = Assume (translExpr e) (translExpr e')
translExpr (TL.Assert e e') = Assert (translExpr e) (translExpr e')
translExpr TL.BAD = BAD

translDataCon :: TL.TDataCon -> DataCon
translDataCon (TL.DataCon n i t ts) = DataCon (translName n) i (translType t) (map translType ts)
translDataCon (TL.PrimCon c) = PrimCon c
translDataCon TL.DEFAULT = DEFAULT

translType :: TL.TType -> Type
translType (TL.TyVar n) = TyVar (translName n)
translType (TL.TyInt) = TyInt
translType (TL.TyFloat) = TyFloat
translType (TL.TyDouble) = TyDouble
translType (TL.TyChar) = TyChar
translType (TL.TyBool) = TyBool
translType (TL.TyRawInt) = TyRawInt
translType (TL.TyRawFloat) = TyRawFloat
translType (TL.TyRawDouble) = TyRawDouble
translType (TL.TyRawChar) = TyRawChar
translType (TL.TyRawString) = TyRawString
translType (TL.TyFun t t') = TyFun (translType t) (translType t')
translType (TL.TyApp t t') = TyApp (translType t) (translType t')
translType (TL.TyConApp n ts) = TyConApp (translName n) (map translType ts)
translType (TL.TyAlg n dc) = TyAlg (translName n) (map translDataCon dc)
translType (TL.TyForAll n t) = TyForAll (translName n) (translType t)
translType TL.TyBottom = TyBottom

translAlt :: TL.TAlt -> Alt
translAlt (TL.Alt (dc, ns)) = Alt (translDataCon dc, map translName ns)

-- Given a list of TL.TName's returns a mapping from the String portion of each
-- name to the full name from translName
-- This can be used to correctly handle user input
namesMapTLToC :: [TL.TName] -> M.Map Name Name
namesMapTLToC = M.fromList . map (\n@(n', _) -> (n', translName n))

-- Given a list of TL.TName's returns a mapping from the full name from translName
-- to String portion of each
namesMapCToTL :: [TL.TName] -> M.Map Name Name
namesMapCToTL = M.fromList . map (\n@(n', _) -> (translName n, n'))

namesMapTEEnv :: TL.TEEnv -> M.Map Name Name
namesMapTEEnv = namesMapTLToC . M.keys

namesMapCons :: TL.TTEnv -> M.Map Name Name
namesMapCons = namesMapCToTL . concatMap getDCNames . M.elems

getDCNames :: TL.TType -> [TL.TName]
getDCNames (TyAlg _ ts) = map (\(TL.DataCon n _ _ _) -> n) ts
-}
