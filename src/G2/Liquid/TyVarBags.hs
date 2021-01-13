-- This module creates IR functions to extract an arbitrary (non-deterministic)
-- value of type a_i from a type of the form T a_1 ... a_n.  If there are no
-- values with type a_i, the function calls `Assume False`.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.TyVarBags ( TyVarBags
                           , InstFuncs
                           , createBagFuncs
                           , createInstFuncs

                           , extractTyVarCall
                           , instTyVarCall

                           , wrapUnitLam) where

import G2.Language
import G2.Language.Monad
import G2.Liquid.Types

import qualified Data.Map.Lazy as M
import qualified Data.Text as T

createBagFuncs :: [Name] -- ^ Which types do we need bag functions for?
               -> LHStateM ()
createBagFuncs ns = do
    tenv <- typeEnv
    let tenv' = M.filterWithKey (\n _ -> n `elem` ns) tenv
    func_names <- assignBagFuncNames tenv'
    bf <- mapM (uncurry (createBagFunc func_names)) (M.toList tenv')
    setTyVarBags (M.fromList bf)

-- | Creates a mapping of type names to bag creation function names 
assignBagFuncNames :: ExState s m => TypeEnv -> m TyVarBags
assignBagFuncNames tenv =
    return . M.fromList
        =<< mapM
            (\(n@(Name n' m _ _), adt) -> do
                let bi = bound_ids adt
                    mkName i = Name (n' `T.append` "_create_bag_" `T.append` (T.pack . show $ i)) m 0 Nothing

                fn <- mapM
                        (\(i, tbi) -> do
                            n_fn <- freshSeededNameN (mkName i)
                            let t = foldr (\ntb -> TyForAll (NamedTyBndr ntb)) (TyVar tbi) bi
                            return $ Id n_fn t)
                        $ zip [0 :: Int ..] bi
                return (n, fn)
            )(M.toList tenv)

createBagFunc :: TyVarBags -> Name -> AlgDataTy -> LHStateM (Name, [Id])
createBagFunc func_names tn adt
    | Just fs <- M.lookup tn func_names = do
        is <- mapM (uncurry (createBagFunc' func_names tn adt)) $ zip fs (bound_ids adt)
        return (tn, is) 
    | otherwise = error "createBagFunc: type not found"

createBagFunc' :: ExState s m =>
                  TyVarBags
               -> Name
               -> AlgDataTy
               -> Id -- ^ The Id of the function to create
               -> Id -- ^ The Id of the TyVar to extract
               -> m Id -- ^ The Id of the new function
createBagFunc' func_names tn adt fn tyvar_id = do
    bi <- freshIdsN $ map (const TYPE) (bound_ids adt)
    adt_i <- freshIdN $ mkFullAppedTyCon tn (map TyVar bi) TYPE

    cse <- createBagFuncCase func_names adt_i tyvar_id bi adt
    let e = mkLams (map (TypeL,) bi) $ Lam TermL adt_i cse

    insertE (idName fn) e
    return fn

-- | Examines the passed `Id` adt_i, which is the ADT to extract the tyvar tyvar_id from,
-- and constructs an expression to actually nondeterministically extract a tyvar_id.
createBagFuncCase :: ExState s m => 
                     TyVarBags
                  -> Id
                  -> Id
                  -> [Id]
                  -> AlgDataTy
                  -> m Expr
createBagFuncCase func_names adt_i tyvar_id _ (DataTyCon { data_cons = dc }) = do
    bindee <- freshIdN (typeOf adt_i)
    alts <- mapM (createBagFuncCaseAlt func_names tyvar_id) dc

    return $ Case (Var adt_i) bindee alts
createBagFuncCase func_names adt_i tyvar_id bi (NewTyCon { bound_ids = adt_bi
                                                         , rep_type = rt }) = do
    let rt' = foldr (uncurry retype) rt $ zip adt_bi (map TyVar bi)
        cst = Cast (Var adt_i) (typeOf adt_i :~ rt')
    extractTyVarCall func_names tyvar_id cst
createBagFuncCase _ _ _ _ (TypeSynonym {}) =
    error "creatBagFuncCase: TypeSynonyms unsupported"

createBagFuncCaseAlt :: ExState s m => TyVarBags -> Id -> DataCon -> m Alt
createBagFuncCaseAlt func_names tyvar_id dc = do
    let at = anonArgumentTypes dc
    is <- freshIdsN at
    es <- mapM (extractTyVarCall func_names tyvar_id . Var) is
    case null es of
        True -> do 
            flse <- mkFalseE
            return $ Alt (DataAlt dc is) 
                         (Assume Nothing flse (Prim Undefined (TyVar tyvar_id)))
        False -> return $ Alt (DataAlt dc is) (NonDet es)

-- | Creates an extractTyVarBag function call to get all TyVars i out of an
-- expression e. 
extractTyVarCall :: ExState s m => TyVarBags -> Id -> Expr -> m Expr
extractTyVarCall func_names i e 
    | TyVar i' <- t
    , i == i' = return e
    | TyCon n tc_t:ts <- unTyApp t
    , Just fn <- M.lookup n func_names = do
        let is = anonArgumentTypes (PresType tc_t)
            ty_ars = map Type $ take (length is) ts
        
        return . NonDet $ map (\f -> App (mkApp (Var f:ty_ars)) e) fn
    | otherwise = do 
        flse <- mkFalseE
        return $ Assume Nothing flse (Prim Undefined (TyVar i))
    where
        t = typeOf e

-- | Turns an expression `e` into `\() -> e`
wrapUnitLam :: ExState s m => Expr -> m Expr
wrapUnitLam e = do
    tUnit <- tyUnitT
    lb <- freshIdN tUnit
    return $ Lam TermL lb e

-- | Creates functions to, for each type (T a_1 ... a_n), create a nondeterministic value.
-- Each a_1 ... a_n has an associated function, allowing the caller to decide how to instantiate
-- these values. 
createInstFuncs :: [Name] -- ^ Which types do we need instantiation functions for?
                -> LHStateM ()
createInstFuncs ns = do
    tenv <- typeEnv
    let tenv' = M.filterWithKey (\n _ -> n `elem` ns) tenv
    func_names <- assignInstFuncNames tenv'
    bf <- mapM (uncurry (createInstFunc func_names)) (M.toList tenv')
    setInstFuncs (M.fromList bf)

-- | Creates a mapping of type names to instantatiation function names 
assignInstFuncNames :: ExState s m => TypeEnv -> m InstFuncs
assignInstFuncNames tenv =
    return . M.fromList
        =<< mapM
            (\(tn@(Name n m _ _), adt) -> do
                let bi = bound_ids adt
                fn <- freshSeededNameN (Name (n `T.append` "_inst_") m 0 Nothing)
                tUnit <- tyUnitT

                let adt_i = mkFullAppedTyCon tn (map TyVar bi) TYPE
                let t = foldr (\ntb -> TyForAll (NamedTyBndr ntb)) 
                            (foldr (\i -> TyFun (TyFun tUnit (TyVar i))) adt_i bi) bi

                return (tn, Id fn t)
            )(M.toList tenv)

createInstFunc :: InstFuncs -> Name -> AlgDataTy -> LHStateM (Name, Id)
createInstFunc func_names tn adt
    | Just fn <- M.lookup tn func_names = do
        bi <- freshIdsN $ map (const TYPE) (bound_ids adt)
        tUnit <- tyUnitT
        inst_funcs <- freshIdsN $ map (\i -> TyFun tUnit (TyVar i)) bi

        cse <- createInstFunc' func_names (zip bi inst_funcs) adt
        let e = mkLams (map (TypeL,) bi) $ mkLams (map (TermL,) inst_funcs) cse

        insertE (idName fn) e
        return (tn, fn)
    | otherwise = error "createInstFunc: type not found"

createInstFunc' :: InstFuncs -> [(Id, Id)] -> AlgDataTy -> LHStateM Expr
createInstFunc' func_names is_fs (DataTyCon { bound_ids = bi
                                            , data_cons = dcs }) = do
    dUnit <- mkUnitE
    dc' <- mapM (\dc -> do
            let apped_dc = foldr App (Data dc) (map (Type . TyVar . fst) is_fs)
                ars_ty = anonArgumentTypes dc
            ars <- mapM (instTyVarCall func_names is_fs) ars_ty
            bnds <- mapM freshIdN ars_ty
            let vrs = map Var bnds
            return $ Let (zip bnds ars) (foldr App apped_dc vrs)) dcs
    return (NonDet dc')
createInstFunc' _ _ _ = error "createInstFunc': unhandled datatype"

-- | Creates an instTyVarCall function call to create an expression of type t with appropriate TyVars
instTyVarCall :: ExState s m =>
                 InstFuncs
              -> [(Id, Id)] -- ^ Mapping of TyVar Ids to Functions to create those TyVars
              -> Type
              -> m Expr
instTyVarCall func_names is_fs t 
    | TyVar i <- t
    , Just f <- lookup i is_fs = do
        dUnit <- mkUnitE
        return (App (Var f) dUnit)
    | TyCon n tc_t:ts <- unTyApp t
    , Just fn <- M.lookup n func_names = do
        let tyc_is = anonArgumentTypes (PresType tc_t)
            ty_ts = take (length tyc_is) ts

            ty_ars = map Type ty_ts
        func_ars <- mapM (\t' -> case t' of
                                    TyVar i
                                        | Just i' <- lookup i is_fs -> return (Var i')
                                    _ -> instTyVarCall func_names is_fs t') ty_ts

        return . mkApp $ Var fn:ty_ars ++ func_ars
    | otherwise =
        let
            tfa = leadingTyForAllBindings $ PresType t
            tfa_is = zipWith (\i1 (i2, _) -> (i1, TyVar i2)) tfa is_fs

            rt = foldr (uncurry retype) (returnType $ PresType t) tfa_is
        in
        return (SymGen rt)
