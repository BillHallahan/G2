-- This module creates IR functions to extract an arbitrary (non-deterministic)
-- value of type a_i from a type of the form T a_1 ... a_n.  If there are no
-- values with type a_i, the function calls `Assume False`.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.TyVarBags ( TyVarBags
                           , InstFuncs
                           , createBagAndInstFuncs

                           , extractTyVarCall
                           , wrapExtractCalls
                           , instTyVarCall) where

import G2.Language
import G2.Language.Monad
import G2.Liquid.Types

import qualified Data.HashSet as S
import qualified Data.Map.Lazy as M
import qualified Data.Text as T

import Debug.Trace

-- | The bag and instantiation functions rely on each other, so we have to make them together
createBagAndInstFuncs :: [Name] -- ^ Which types do we need bag functions for?
                      -> [Name] -- ^ Which types do we need instantiation functions for?
                      -> LHStateM ()
createBagAndInstFuncs bag_func_ns inst_func_ns = do
    tenv <- typeEnv
    
    let bag_func_ns' = relNames tenv S.empty bag_func_ns
        bag_tenv = M.filterWithKey (\n _ -> n `S.member` bag_func_ns') tenv
    bag_names <- assignBagFuncNames bag_tenv
    setTyVarBags bag_names

    let inst_func_ns' = relNames tenv S.empty inst_func_ns
        inst_tenv = M.filterWithKey (\n _ -> n `S.member` inst_func_ns') tenv
    inst_names <- assignInstFuncNames inst_tenv
    setInstFuncs inst_names

    createBagFuncs bag_names bag_tenv
    createInstFuncs inst_names inst_tenv

relNames :: TypeEnv -> S.HashSet Name -> [Name] -> S.HashSet Name
relNames _ rel [] = rel
relNames tenv rel (n:ns) =
    if S.member n rel
      then relNames tenv rel ns
      else relNames tenv (S.insert n rel) ns'
  where
    ns' = case M.lookup n tenv of
        Nothing -> ns
        Just r -> names r ++ ns

createBagFuncs :: TyVarBags -- ^ Which types do we need bag functions for?
               -> TypeEnv
               -> LHStateM ()
createBagFuncs func_names tenv = do
    mapM_ (uncurry (createBagFunc func_names)) (M.toList tenv)

-- | Creates a mapping of type names to bag creation function names 
assignBagFuncNames :: ExState s m => TypeEnv -> m TyVarBags
assignBagFuncNames tenv =
    return . M.fromList
        =<< mapM
            (\(n@(Name n' m _ _), adt) -> do
                let dc = head (dataCon adt)
                    bi = bound_ids adt
                    mkName i = Name (n' `T.append` "_create_bag_" `T.append` (T.pack . show $ i)) m 0 Nothing

                fn <- mapM
                        (\(i, tbi) -> do
                            n_fn <- freshSeededNameN (mkName i)
                            let t = foldr (\ntb -> TyForAll (NamedTyBndr ntb))
                                    (TyFun (returnType dc) (TyVar tbi)) bi
                            return $ Id n_fn t)
                        $ zip [0 :: Int ..] bi
                return (n, fn)
            )(M.toList tenv)

createBagFunc :: TyVarBags -> Name -> AlgDataTy -> LHStateM ()
createBagFunc func_names tn adt
    | Just fs <- M.lookup tn func_names =
        mapM_ (uncurry (createBagFunc' func_names tn adt)) $ zip fs (bound_ids adt)
    | otherwise = error "createBagFunc: type not found"

createBagFunc' :: TyVarBags
               -> Name
               -> AlgDataTy
               -> Id -- ^ The Id of the function to create
               -> Id -- ^ The Id of the TyVar to extract
               -> LHStateM ()
createBagFunc' func_names tn adt fn tyvar_id = do
    bi <- freshIdsN $ map (const TYPE) (bound_ids adt)
    adt_i <- freshIdN $ mkFullAppedTyCon tn (map TyVar bi) TYPE

    cse <- createBagFuncCase func_names adt_i tyvar_id bi adt
    let e = mkLams (map (TypeL,) bi) $ Lam TermL adt_i cse

    insertE (idName fn) e

-- | Examines the passed `Id` adt_i, which is the ADT to extract the tyvar tyvar_id from,
-- and constructs an expression to actually nondeterministically extract a tyvar_id.
createBagFuncCase :: TyVarBags
                  -> Id
                  -> Id
                  -> [Id]
                  -> AlgDataTy
                  -> LHStateM Expr
createBagFuncCase func_names adt_i tyvar_id _ (DataTyCon { data_cons = dc }) = do
    bindee <- freshIdN (typeOf adt_i)
    alts <- mapM (createBagFuncCaseAlt func_names tyvar_id) dc

    return $ Case (Var adt_i) bindee alts
createBagFuncCase func_names adt_i tyvar_id bi (NewTyCon { bound_ids = adt_bi
                                                         , rep_type = rt }) = do
    let rt' = foldr (uncurry retype) rt $ zip adt_bi (map TyVar bi)
        cst = Cast (Var adt_i) (typeOf adt_i :~ rt')
    clls <- extractTyVarCall func_names todo_emp tyvar_id cst
    wrapExtractCalls tyvar_id clls
createBagFuncCase _ _ _ _ (TypeSynonym {}) =
    error "creatBagFuncCase: TypeSynonyms unsupported"

createBagFuncCaseAlt :: TyVarBags -> Id -> DataCon -> LHStateM Alt
createBagFuncCaseAlt func_names tyvar_id dc = do
    let at = anonArgumentTypes dc
    is <- freshIdsN at
    es <- return . concat =<< mapM (extractTyVarCall func_names todo_emp tyvar_id . Var) is
    case null es of
        True -> do 
            flse <- mkFalseE
            return $ Alt (DataAlt dc is) 
                         (Assume Nothing flse (Prim Undefined (TyVar tyvar_id)))
        False -> return $ Alt (DataAlt dc is) (NonDet es)

todo_emp :: [a]
todo_emp = []

-- | Creates a set of expressions to get all TyVars i out of an
-- expression e. 
extractTyVarCall :: TyVarBags
                 -> [(Id, Id)]  -- ^ Mapping of TyVar Ids to Functions to create those TyVars
                 -> Id 
                 -> Expr 
                 -> LHStateM [Expr]
extractTyVarCall func_names is_fs i e 
    | TyVar i' <- t
    , i == i' = return [e]
    | TyCon n tc_t:ts <- unTyApp t
    , Just fn <- M.lookup n func_names = do
        let is = anonArgumentTypes (PresType tc_t)
            ty_ars = map Type $ take (length is) ts
            nds = map (\f -> App (mkApp (Var f:ty_ars)) e) fn
        nds' <- mapM (extractTyVarCall func_names is_fs i) nds
        return (concat nds')
    | TyFun _ _ <- t = do
        let is_ars = leadingTyForAllBindings $ PresType t
            ars_ty = anonArgumentTypes $ PresType t
            tvs = tyVarIds . returnType $ PresType t

        inst_funcs <- getInstFuncs
        inst_ars <- mapM (instTyVarCall' inst_funcs is_fs) ars_ty
        let call_f = mkApp $ e:inst_ars

        cll <- if i `elem` tvs then extractTyVarCall func_names is_fs i call_f else return []
        return cll
    | otherwise = return []
    where
        t = typeOf e

wrapExtractCalls :: ExState s m => Id -> [Expr] -> m Expr
wrapExtractCalls i clls = do
    case null clls of
        True -> do
            flse <- mkFalseE
            return $ Assume Nothing flse (Prim Undefined (TyVar i))
        False -> return $ NonDet clls

-- | Creates functions to, for each type (T a_1 ... a_n), create a nondeterministic value.
-- Each a_1 ... a_n has an associated function, allowing the caller to decide how to instantiate
-- these values. 
createInstFuncs :: InstFuncs -- ^ Which types do we need instantiation functions for?
                -> TypeEnv
                -> LHStateM ()
createInstFuncs func_names tenv = do
    mapM_ (uncurry (createInstFunc func_names)) (M.toList tenv)

-- | Creates a mapping of type names to instantatiation function names 
assignInstFuncNames :: ExState s m => TypeEnv -> m InstFuncs
assignInstFuncNames tenv =
    return . M.fromList
        =<< mapM
            (\(tn@(Name n m _ _), adt) -> do
                let bi = bound_ids adt
                fn <- freshSeededNameN (Name (n `T.append` "_inst_") m 0 Nothing)

                let adt_i = mkFullAppedTyCon tn (map TyVar bi) TYPE
                let t = foldr (\ntb -> TyForAll (NamedTyBndr ntb)) 
                            (foldr (\i -> TyFun (TyVar i)) adt_i bi) bi

                return (tn, Id fn t)
            )(M.toList tenv)

createInstFunc :: InstFuncs -> Name -> AlgDataTy -> LHStateM ()
createInstFunc func_names tn adt
    | Just fn <- M.lookup tn func_names = do
        bi <- freshIdsN $ map (const TYPE) (bound_ids adt)
        inst_funcs <- freshIdsN $ map TyVar bi

        cse <- createInstFunc' func_names (zip bi inst_funcs) adt
        let e = mkLams (map (TypeL,) bi) $ mkLams (map (TermL,) inst_funcs) cse

        insertE (idName fn) e
    | otherwise = error "createInstFunc: type not found"

createInstFunc' :: InstFuncs -> [(Id, Id)] -> AlgDataTy -> LHStateM Expr
createInstFunc' func_names is_fs (DataTyCon { bound_ids = bi
                                            , data_cons = dcs }) = do
    dc' <- mapM (\dc -> do
            let apped_dc = mkApp (Data dc:map (Type . TyVar . fst) is_fs)
                ars_ty = anonArgumentTypes dc

                is_fs' = zipWith (\i (_, f) -> (i, f)) (leadingTyForAllBindings dc) is_fs

            ars <- mapM (instTyVarCall' func_names is_fs') ars_ty
            bnds <- mapM freshIdN ars_ty
            let vrs = map Var bnds
            return $ Let (zip bnds ars) (mkApp $ apped_dc:vrs)) dcs
    return (NonDet dc')
createInstFunc' _ _ _ = error "createInstFunc': unhandled datatype"

-- | Creates an instTyVarCall function call to create an expression of type t with appropriate TyVars
instTyVarCall :: ExState s m =>
                 InstFuncs
              -> [(Id, Id)] -- ^ Mapping of TyVar Ids to Functions to create those TyVars
              -> Type
              -> m Expr
instTyVarCall func_names is_fs t = do
    tUnit <- tyUnitT
    ui <- freshIdN tUnit
    cll <- instTyVarCall' func_names is_fs t 
    return $ Lam TermL ui cll

instTyVarCall' :: ExState s m =>
                 InstFuncs
              -> [(Id, Id)] -- ^ Mapping of TyVar Ids to Functions to create those TyVars
              -> Type
              -> m Expr
instTyVarCall' func_names is_fs t 
    | TyVar i <- t
    , Just f <- lookup i is_fs = do
        return $ Var f
    | TyVar i <- t = do
        flse <- mkFalseE
        return . Assume Nothing flse . Prim Undefined $ TyVar i

    | TyCon n tc_t:ts <- unTyApp t
    , Just fn <- M.lookup n func_names = do
        let tyc_is = anonArgumentTypes (PresType tc_t)
            ty_ts = take (length tyc_is) ts

            ty_ars = map Type ty_ts
        func_ars <- mapM (\t' -> case t' of
                                    TyVar i
                                        | Just i' <- lookup i is_fs -> return (Var i')
                                    _ -> do
                                        cll <- instTyVarCall' func_names is_fs t'
                                        return cll) ty_ts
        let_ids <- freshIdsN $ map typeOf func_ars
        let bnds = zip let_ids func_ars

        return . Let bnds . mkApp $ Var fn:ty_ars ++ map Var let_ids
    | otherwise = do
        let tfa = leadingTyForAllBindings $ PresType t
            tfa_is = zipWith (\i1 (i2, _) -> (i1, TyVar i2)) tfa is_fs

            rt = foldr (uncurry retype) (returnType $ PresType t) tfa_is
        return $ SymGen rt
