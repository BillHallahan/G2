-- This module creates IR functions to extract an arbitrary (non-deterministic)
-- value of type a_i from a type of the form T a_1 ... a_n.  If there are no
-- values with type a_i, the function calls `Assume False`.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.TyVarBags ( TyVarBags
                           , createBagFuncs) where

import G2.Language
import G2.Language.Monad
import G2.Liquid.Types

import qualified Data.Map.Lazy as M
import qualified Data.Text as T

type FuncNames = M.Map Name [Id]

createBagFuncs :: [Name] -- ^ Which types do we need bag functions for?
               -> LHStateM ()
createBagFuncs ns = do
    tenv <- typeEnv
    let tenv' = M.filterWithKey (\n _ -> n `elem` ns) tenv
    func_names <- assignBagFuncNames tenv'
    bf <- mapM (uncurry (createBagFunc func_names)) (M.toList tenv')
    setTyVarBags (M.fromList bf)

-- | Creates a mapping of type names to bag creation function names 
assignBagFuncNames :: ExState s m => TypeEnv -> m FuncNames
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

createBagFunc :: FuncNames -> Name -> AlgDataTy -> LHStateM (Name, [Id])
createBagFunc func_names tn adt
    | Just fs <- M.lookup tn func_names = do
        is <- mapM (uncurry (createBagFunc' func_names tn adt)) $ zip fs (bound_ids adt)
        return (tn, is) 
    | otherwise = error "createBagFunc: type not found"

createBagFunc' :: ExState s m =>
                  FuncNames
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
                     FuncNames
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

createBagFuncCaseAlt :: ExState s m => FuncNames -> Id -> DataCon -> m Alt
createBagFuncCaseAlt func_names tyvar_id dc = do
    let at = anonArgumentTypes dc
    is <- freshIdsN at
    es <- mapM (extractTyVarCall func_names tyvar_id . Var) is
    return $ Alt (DataAlt dc is) (NonDet es)

-- | Creates an extractTyVarBag function call to get all TyVars i out of an
-- expression e. 
extractTyVarCall :: ExState s m => FuncNames -> Id -> Expr -> m Expr
extractTyVarCall func_names i e 
    | TyVar i' <- t
    , i == i' = return e
    | TyCon n tc_t:ts <- unTyApp t
    , Just fn <- M.lookup n func_names = do
        let is = leadingTyForAllBindings tc_t
            ty_ars = map Type $ take (length is) ts
        
        return . NonDet $ map (\f -> App (mkApp (Var f:ty_ars)) e) fn
    | otherwise = do 
        flse <- mkFalseE
        return $ Assume Nothing flse (Prim Undefined (TyVar i))
    where
        t = typeOf e
