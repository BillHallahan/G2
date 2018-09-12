{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.Conversion2 ( mergeLHSpecState
                                       , convertLHExpr
                                       , specTypeToType
                                       , unsafeSpecTypeToType
                                       , symbolName
                                       , addLHDictToTypes) where

import G2.Internals.Language
import qualified G2.Internals.Language.KnownValues as KV
import G2.Internals.Language.Monad
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Liquid.Types
import G2.Internals.Translation.Haskell

import qualified Var as Var

import Language.Fixpoint.Types.Names
import qualified Language.Fixpoint.Types.Refinements as Ref
import Language.Fixpoint.Types.Refinements hiding (Expr, I)
import Language.Haskell.Liquid.Types

import Data.Coerce
import Data.Foldable
import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import Debug.Trace

mergeLHSpecState :: Id -> [(Var.Var, LocSpecType)] -> LHStateM Id
mergeLHSpecState i sp = do
    mapM (uncurry mergeLHSpecState') sp
    return i

mergeLHSpecState' :: Var.Var -> LocSpecType -> LHStateM ()
mergeLHSpecState' v lst = do
    eenv <- exprEnv
    let
        (Id (Name n m _ _) _) = mkIdUnsafe v
        g2N = E.lookupNameMod n m eenv

    case g2N of
        Just (n', e) -> do
            e' <- mergeSpecType (val lst) n' e
            insertE n' e'
        Nothing -> return ()

mergeSpecType :: SpecType -> Name -> Expr -> LHStateM Expr
mergeSpecType st fn e = do
    -- Create new lambda bindings to use in the Ref. Type
    let argT = spArgumentTypes e
    is <- freshIdsN $ map argTypeToType argT
    let lu = map argTypeToLamUse argT

    let e' = foldl' (\e_ -> App e_ . Var) e is

    --Create a variable for the returned value
    r <- freshIdN (typeOf e')
    assert <- convertSpecType M.empty is r st

    let fc = FuncCall { funcName = fn 
                      , arguments = map Var is
                      , returns = Var r }
    let rLet = Let [(r, e')] $ Assert (Just fc) assert (Var r)
    
    let e''' = foldr (uncurry Lam) rLet $ zip lu is

    return e'''

convertSpecType :: M.Map Name Id -> [Id] -> Id -> SpecType -> LHStateM Expr
convertSpecType m is r (RVar {rt_var = (RTV v), rt_reft = reft}) = do
    let symb = reftSymbol $ ur_reft reft
    let i = mkIdUnsafe v

    let symbId = convertSymbolT symb (TyVar i)
        m' = M.insert (idName symbId) i m 

    re <- convertLHExpr m' Nothing (reftExpr $ ur_reft reft)

    return $ App (Lam TermL symbId re) (Var r)
convertSpecType m (i:is) r (RFun {rt_bind = b, rt_in = fin, rt_out = fout }) = do
    t <- unsafeSpecTypeToType fin
    let i' = convertSymbolT b t

    let m' = M.insert (idName i') i' m

    e <- convertSpecType m' [] i' fin
    e' <- convertSpecType m' is r fout

    an <- mkAndE
    let e'' = App (App an e) e'
    
    return $ App (Lam TermL i' e'') (Var i)
convertSpecType m (i:is) r (RAllT {rt_tvbind = RTVar (RTV v) _, rt_ty = rty}) = do
    let i' = mkIdUnsafe v

    let m' = M.insert (idName i') i' m

    e <- convertSpecType m' is r rty
    return $ App (Lam TypeL i' e) (Var i)
convertSpecType m is r (RApp {rt_tycon = c, rt_reft = reft, rt_args = as}) = do
    let symb = reftSymbol $ ur_reft reft
    ty <- return . maybe (error "Error in convertSpecType") id =<< rTyConType c as
    let i = convertSymbolT symb ty

    let m' = M.insert (idName i) i m

    argsPred <- polyPredFunc as ty m r
    re <- convertLHExpr m' Nothing (reftExpr $ ur_reft reft)

    an <- mkAndE

    return $ App (App an (App (Lam TermL i re) (Var r))) argsPred

polyPredFunc :: [SpecType] -> Type -> M.Map Name Id -> Id -> LHStateM Expr
polyPredFunc as ty m b = do
    dict <- lhTCDict m ty
    as' <- mapM (polyPredLam m) as

    lhPP <- lhPPM
    
    return $ mkApp $ [Var $ Id lhPP TyUnknown, Type (typeOf b), dict] ++ as' ++ [Var b]

polyPredLam :: M.Map Name Id -> SpecType -> LHStateM Expr
polyPredLam m rapp  = do
    t <- unsafeSpecTypeToType rapp
    i <- freshIdN t
    
    convertSpecType m undefined i rapp

convertLHExpr :: M.Map Name Id -> Maybe Type -> Ref.Expr -> LHStateM Expr
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
convertLHExpr m t (ENeg e) = do
    e' <- convertLHExpr m t e
    let t' = typeOf e'

    negate <- mkNegateE
    lhDict <- lhTCDict m t'
    nDict <- numDict m t'

    return $ mkApp [ negate
                   , Type t'
                   , lhDict
                   , nDict
                   , e' ]
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
convertLHExpr m t (PIff e1 e2) = do
    e1' <- convertLHExpr m t e1
    e2' <- convertLHExpr m t e2
    iff <- mkIffE
    return $ mkApp [iff, e1', e2']
convertLHExpr m t (PAtom brel e1 e2) = do
    (e1', e2') <- correctTypes m t e1 e2
    brel' <- convertBrel brel
    return $ mkApp [brel', e1', e2']
convertLHExpr _ _ e = error $ "Untranslated LH Expr " ++ (show e)

convertBop :: Bop -> LHStateM Expr
convertBop Ref.Plus = mkPlusE
convertBop Ref.Minus = mkMinusE
convertBop Ref.Times = mkMultE
convertBop Ref.Div = mkDivE
convertBop Ref.Mod = mkModE
convertBop Ref.RTimes = mkMultE
convertBop Ref.RDiv = mkDivE

lhExprType :: M.Map Name Id -> Ref.Expr -> LHStateM Type
lhExprType m (ECon c) =
    case c of
        Ref.I _ -> tyIntT
        Ref.R _ -> tyDoubleT
lhExprType m (EVar s) =
    return $ maybe TyUnknown id (fmap typeOf (M.lookup (symbolName s) m))
lhExprType m (ENeg e) = lhExprType m e
lhExprType m (EApp e _) = do
    t <- lhExprType m e
    
    case t of
        TyForAll _ t' -> return t'
        TyFun _ t' -> return t'
        _ -> error $ "Non-function type in EApp" ++ show t
lhExprType _ e = error $ "Unhandled in lhExprType " ++ (show e)

correctTypes :: M.Map Name Id -> Maybe Type -> Ref.Expr -> Ref.Expr -> LHStateM (Expr, Expr)
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

callFromInteger :: M.Map Name Id -> Type -> Expr -> LHStateM (Maybe Expr)
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

convertSymbolT :: Symbol -> Type -> Id
convertSymbolT s = Id (symbolName s)

reftSymbol :: Reft -> Symbol
reftSymbol = fst . unpackReft

reftExpr :: Reft -> Ref.Expr
reftExpr = snd . unpackReft

unpackReft :: Reft -> (Symbol, Ref.Expr) 
unpackReft = coerce

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

convertEVar :: Name -> M.Map Name Id -> Maybe Type -> LHStateM Expr
convertEVar nm@(Name n md _ _) m mt = do
    let mt' = maybe TyUnknown id mt
    let d = maybe (Id nm mt') id $ M.lookup nm m

    eenv <- exprEnv
    tenv <- typeEnv
    
    case (E.lookupNameMod n md eenv, getDataConNameMod' tenv nm) of
        (Just (n', e), _) -> return $ Var $ Id n' (typeOf e)
        (_, Just dc) -> return $ Data dc 
        _ -> return $ Var d

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

addLHDictToTypes :: ASTContainerM e Type => M.Map Name Id -> e -> LHStateM e
addLHDictToTypes m = modifyContainedASTsM (addLHDictToTypes' m)

addLHDictToTypes' :: M.Map Name Id -> Type -> LHStateM Type
addLHDictToTypes' m t@(TyForAll (NamedTyBndr _) _) = addLHDictToTypes'' m [] t
addLHDictToTypes' m t = modifyChildrenM (addLHDictToTypes' m) t

addLHDictToTypes'' :: M.Map Name Id -> [Id] -> Type -> LHStateM Type
addLHDictToTypes'' m is (TyForAll (NamedTyBndr b) t) =
    return . TyForAll (NamedTyBndr b) =<< addLHDictToTypes'' m (b:is) t
addLHDictToTypes'' m is t = do
    let is' = reverse is
    dictT <- mapM (lhTCDict m . TyVar) is'
    let dictT' = map typeOf dictT

    return $ foldr TyFun t dictT'

lhTCDict :: M.Map Name Id -> Type -> LHStateM Expr
lhTCDict m t = do
    lh <- lhTCM
    tc <- typeClassInstTC m lh t
    case tc of
        Just e -> return e
        Nothing -> return $ Var (Id (Name "BAD" Nothing 0 Nothing) TyUnknown) -- error $ "No lh dict " ++ show t ++ "\n" ++ show m

numDict :: M.Map Name Id -> Type -> LHStateM Expr
numDict m t = do
    num <- return . KV.numTC =<< knownValues
    tc <- typeClassInstTC m num t
    case tc of
        Just e -> return e
        Nothing -> return $ Var (Id (Name "BAD" Nothing 0 Nothing) TyUnknown) -- error $ "No lh dict " ++ show t ++ "\n" ++ show m
