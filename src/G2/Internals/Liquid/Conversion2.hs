{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.Conversion2 where

import G2.Internals.Language
import G2.Internals.Language.Monad
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Liquid.Types
import G2.Internals.Translation.Haskell

import Language.Fixpoint.Types.Names
import qualified Language.Fixpoint.Types.Refinements as Ref
import Language.Fixpoint.Types.Refinements hiding (Expr, I)
import Language.Haskell.Liquid.Types

import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import Debug.Trace

-- convertLHExpr :: Ref.Expr -> Maybe Type -> TCValues -> State t -> M.Map Name Type -> Expr
convertLHExpr :: M.Map Name Type -> Maybe Type -> Ref.Expr -> LHStateM Expr
convertLHExpr _ t (ECon c) = convertCon t c
convertLHExpr m t (EVar s) = convertEVar (symbolName s) m t
convertLHExpr m t (EApp e e') = do
    f <- convertLHExpr m Nothing e

    let at = argumentTypes f
        f_ar_t = case at of
                    (_:_) -> Just $ last at
                    _ -> Nothing

        f_ar_ts = fmap tyAppArgs f_ar_t

    argE <- convertLHExpr m f_ar_t e'

    let tArgE = typeOf argE
        ctArgE = tyAppCenter tArgE
        ts = tyAppArgs tArgE
    
    case (ctArgE, f_ar_ts) of
        (TyConApp _ _, Just f_ar_ts') -> do
            let specTo = concatMap (map snd) $ map M.toList $ map (snd . uncurry (specializes M.empty)) $ zip ts f_ar_ts'
                te = map Type specTo

            tcs <- mapM (lhTCDict m) ts

            f' <- addLHDictToTypes m f
            let fw = mkApp $ f':te

                apps = mkApp $ fw:tcs ++ [argE]
            
            return apps
        _ -> return $ App f argE
convertLHExpr m t (EBin b e e') = do
    (e2, e2') <- correctTypes m t e e'
    b' <- convertBop b

    let t' = typeOf e2

    lhDict <- lhTCDict m t'
    nDict <- numDict m t'

    return $ mkApp [ b'
                   , Type t'
                   , lhDict
                   , nDict
                   , e2
                   , e2' ]
convertLHExpr m t (PAnd es) = do
    es' <- mapM (convertLHExpr m Nothing) es

    true <- mkTrueE
    an <- mkAndE

    case es' of
        [] -> return $ true
        [e] -> return e
        _ -> return $ foldr (\e -> App (App an e)) true es'
convertLHExpr m t (POr es) = do
    es' <- mapM (convertLHExpr m Nothing) es

    false <- mkFalseE
    or <- mkOrE

    case es' of
        [] -> return false
        [e] -> return e
        _ -> return $ foldr (\e -> App (App or e)) false es'
convertLHExpr _ _ e = error $ "Untranslated LH Expr " ++ (show e)

convertBop :: Bop -> LHStateM Expr
convertBop Ref.Plus = mkPlusE
convertBop Ref.Minus = mkMinusE
convertBop Ref.Times = mkMultE
convertBop Ref.Div = mkDivE
convertBop Ref.Mod = mkModE
convertBop Ref.RTimes = mkMultE
convertBop Ref.RDiv = mkDivE

lhExprType :: M.Map Name Type -> Ref.Expr -> LHStateM Type
lhExprType m (ECon c) =
    case c of
        Ref.I _ -> tyIntT
        Ref.R _ -> tyDoubleT
lhExprType m (EVar s) = return $ maybe TyUnknown id $ M.lookup (symbolName s) m
lhExprType m (EApp e _) = do
    t <- lhExprType m e
    
    case t of
        TyForAll _ t' -> return t'
        TyFun _ t' -> return t'
        _ -> error $ "Non-function type in EApp" ++ show t
lhExprType _ e = error $ "Unhandled in lhExprType " ++ (show e)

correctTypes :: M.Map Name Type -> Maybe Type -> Ref.Expr -> Ref.Expr -> LHStateM (Expr, Expr)
correctTypes m mt re re' = do
    t <- lhExprType m re
    t' <- lhExprType m re'

    e <- convertLHExpr m mt re
    e' <- convertLHExpr m mt re'

    if t == t'
        then return (e, e')
        else do
            e2 <- callFromInteger m t' e
            e2' <- callFromInteger m t e'

            let e3 = maybe e id e2
            let e3' = maybe e' id e2'

            return (e3, e3')

callFromInteger :: M.Map Name Type -> Type -> Expr -> LHStateM (Maybe Expr)
callFromInteger m t e = do
    let retT = returnType e

    lhDict <- lhTCDict m t
    nDict <- numDict m t
    
    fIntgr <- mkFromIntegerE

    tyI <- tyIntegerT

    if retT /= tyI then
        return $ Just e
    else
        return $ Just $ mkApp [ fIntgr
                              , Type t
                              , lhDict
                              , nDict
                              , e]

callFromInteger _ _ _ = error "Nothing in callFromInteger"

-- If possible, we split symbols at the last "." not in parenthesis, to
-- correctly set module names 
symbolName :: Symbol -> Name
symbolName s =
    let
        t = symbolSafeText s
        l = case T.null t of
            True -> Just $ T.last t
            False -> Nothing

        ((m, n), i) =
            case l of
                Just ')' -> (T.breakOnEnd ".(" t, 2)
                _ -> (T.breakOnEnd "." t, 1)

        m' = T.dropEnd i m
    in
    case (m', n) of
        (n', "") -> Name n' Nothing 0 Nothing
        _ -> Name n (Just m') 0 Nothing

convertEVar :: Name -> M.Map Name Type -> Maybe Type -> LHStateM Expr
convertEVar nm@(Name n md _ _) m mt = do
    let mt' = maybe TyUnknown id mt
    let t = maybe mt' id $ M.lookup nm m

    eenv <- exprEnv
    tenv <- typeEnv
    
    case (E.lookupNameMod n md eenv, getDataConNameMod' tenv nm) of
        (Just (n', e), _) -> return $ Var $ Id n' (typeOf e)
        (_, Just dc) -> return $ Data dc 
        _ -> return $ Var $ Id nm t

convertCon :: Maybe Type -> Constant -> LHStateM Expr
convertCon (Just (TyConApp n _)) (Ref.I i) = do
    (TyConApp ti _) <- tyIntT
    dc <- mkDCIntE
    if n == ti
        then return $ App dc (Lit . LitInt $ fromIntegral i)
        else error "Unknown Con"
convertCon _ (Ref.I i) = do
    dc <- mkDCIntegerE
    return $ App dc (Lit . LitInt $ fromIntegral i)
convertCon _ (Ref.R d) = do
    dc <- mkDCDoubleE
    return $ App dc (Lit . LitDouble $ toRational d)
convertCon _ _ = error "convertCon: Unhandled case"

unsafeSpecTypeToType :: SpecType -> LHStateM Type
unsafeSpecTypeToType st = do
    t' <- specTypeToType st
    case t' of
        Just t'' -> return t''
        Nothing -> error "Unhandled SpecType"

specTypeToType :: SpecType -> LHStateM (Maybe Type)
specTypeToType (RVar {rt_var = (RTV v)}) = do
    let i = mkIdUnsafe v
    return $ Just (TyVar i)
specTypeToType (RFun {rt_in = fin, rt_out = fout}) = do
    t <- specTypeToType fin
    t2 <- specTypeToType fout
    
    case (t, t2) of
        (Just t', Just t2') -> return $ Just (TyFun t' t2')
        _ -> return Nothing
specTypeToType (RAllT {rt_tvbind = RTVar (RTV v) _, rt_ty = rty}) = do
    let i = mkIdUnsafe v
    t <- specTypeToType rty
    return $ fmap (TyForAll (NamedTyBndr i)) t
specTypeToType (RApp {rt_tycon = c, rt_args = as}) = rTyConType c as
specTypeToType rty = error $ "Unmatched pattern in specTypeToType " ++ show (pprint rty)

rTyConType :: RTyCon -> [SpecType]-> LHStateM (Maybe Type)
rTyConType rtc sts = do
    tenv <- typeEnv

    let tcn = mkTyConName HM.empty . rtc_tc $ rtc
        n = nameModMatch tcn tenv

    ts <- mapM specTypeToType sts
    
    case (not . any isNothing $ ts) of
        True -> case fmap (\n' -> mkTyConApp n' (catMaybes ts) TYPE) n of
                    Nothing -> return $ primType tcn
                    t -> return t
        False -> return Nothing

primType :: Name -> Maybe Type
primType (Name "Int#" _ _ _) = Just TyLitInt
primType (Name "Float#" _ _ _) = Just TyLitFloat
primType (Name "Double#" _ _ _) = Just TyLitDouble
primType (Name "Word#" _ _ _) = Just TyLitInt
primType _ = Nothing

convertBrel :: Brel -> LHStateM Expr
convertBrel Ref.Eq = convertBrel' lhEqM
convertBrel Ref.Ueq = convertBrel' lhEqM
convertBrel Ref.Ne = convertBrel' lhNeM
convertBrel Ref.Gt = convertBrel' lhGtM
convertBrel Ref.Ge = convertBrel' lhGeM
convertBrel Ref.Lt = convertBrel' lhLtM
convertBrel Ref.Le = convertBrel' lhLeM
convertBrel _ = error "convertBrel: Unhandled brel"

convertBrel' :: LHStateM Name -> LHStateM Expr
convertBrel' f = do
    n <- f
    return $ Var $ Id n TyUnknown

addLHDictToTypes :: ASTContainerM e Type => M.Map Name Type -> e -> LHStateM e
addLHDictToTypes m = modifyContainedASTsM (addLHDictToTypes' m)

addLHDictToTypes' :: M.Map Name Type -> Type -> LHStateM Type
addLHDictToTypes' m t@(TyForAll (NamedTyBndr _) _) = addLHDictToTypes'' m [] t
addLHDictToTypes' m t = modifyChildrenM (addLHDictToTypes' m) t

addLHDictToTypes'' :: M.Map Name Type -> [Id] -> Type -> LHStateM Type
addLHDictToTypes'' m is (TyForAll (NamedTyBndr b) t) =
    return . TyForAll (NamedTyBndr b) =<< addLHDictToTypes'' m (b:is) t
addLHDictToTypes'' m is t = do
    let is' = reverse is
    dictT <- mapM (lhTCDict m . TyVar) is'
    let dictT' = map typeOf dictT

    return $ foldr TyFun t dictT'

lhTCDict :: M.Map Name Type -> Type -> LHStateM Expr
lhTCDict m t = do
    ti <- typeIdList m
    lh <- lhTCM
    tc <- typeClasses
    let ts = tyAppArgs t
    
    case lookupTCDict tc lh t of
        Just lhD -> 
            case t of 
                TyConApp _ _ -> do
                    lhs <- mapM (lhTCDict m) ts
                    return $ mkApp $ Var lhD:lhs ++ map (Type) ts
                _ -> return $ Var lhD
        Nothing -> case lookup t ti of
            Just lhD -> return $ Var lhD
            Nothing -> return $ Var (Id (Name "BAD" Nothing 0 Nothing) TyUnknown)

numDict :: M.Map Name Type -> Type -> LHStateM Expr
numDict m t = return $ Var (Id (Name "BAD" Nothing 0 Nothing) TyUnknown)

typeIdList :: M.Map Name Type -> LHStateM [(Type, Id)]
typeIdList m = do
    lh_tc <- lhTCM
    return . map (\(n, t) -> (head $ tyAppArgs t, Id n t)) . M.toList . M.filter (tyVarInTyAppHasName lh_tc) $ m
    where
        tyVarInTyAppHasName :: Name -> Type -> Bool
        tyVarInTyAppHasName n (TyApp (TyConApp n' _) (TyVar (Id _ _))) = n == n'
        tyVarInTyAppHasName _ _ = False
