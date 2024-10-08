{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module G2.Liquid.Inference.UnionPoly (UnionedTypes, sharedTyConsEE, lookupUT) where

import qualified G2.Data.UFMap as UF
import qualified G2.Data.UnionFind as UFind
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.Monad.AST
import G2.Language.Monad.Naming
import G2.Language.Monad.Support

import Control.Monad
import qualified Data.HashMap.Lazy as HM
import Data.Maybe
import qualified Data.Text as T

newtype UnionedTypes = UT (HM.HashMap Name Type) deriving Show

lookupUT :: Name -> UnionedTypes -> Maybe Type
lookupUT (Name n m _ l) (UT ut) = HM.lookup (Name n m 0 l) ut

sharedTyConsEE :: [Name] -> ExprEnv -> UnionedTypes
sharedTyConsEE ns eenv = fst $ runNamingM (sharedTyConsEE' ns eenv) (mkNameGen eenv)

sharedTyConsEE' :: [Name] -> ExprEnv -> NameGenM UnionedTypes
sharedTyConsEE' ns eenv = do
    let f_eenv = E.filterWithKey (\n _ -> n `elem` ns) eenv
        typeOf_eenv = E.map' typeOf f_eenv
    tys <- mapM assignTyConNames typeOf_eenv

    let rep_eenv = E.map (repVars tys) f_eenv
        rep_eenv' = elimTypes rep_eenv
    -- We want to try and be clever with passed in functions/lamdas to unify types when required,
    -- but we can do too much if we unify non-function types or inner lambdas.
    -- This is very much a heuristic.
    rep_eenv'' <-   E.mapM (scrambleNonFuncLams >=> scrambleNonFuncLets)
                  . substLams
                  . adjustLetTypes
                =<< E.mapM (assignTyConNames >=> elimTyForAll) rep_eenv'

    let union_poly = mconcat . map UF.joinedKeys . HM.elems
                   . E.map' (fromMaybe UF.empty . checkType)
                   $ rep_eenv''

        union_tys = fmap (renameFromUnion union_poly) tys

    return . UT $ HM.mapKeys (\(Name n m _ l) -> Name n m 0 l) union_tys


checkType :: Expr -> Maybe (UF.UFMap Name Type)
checkType = check' UF.empty

check' :: UF.UFMap Name Type -> Expr -> Maybe (UF.UFMap Name Type)
check' uf (Var (Id _ _)) = Just uf
check' uf (Lit _) = Just uf
check' uf (Prim _ _) = Just uf
check' uf (Data _) = Just uf
check' uf (App e1 e2) =
    let
        t1 = case typeOf e1 of
                TyFun t _ -> t
                TyForAll (Id _ t) _ -> t
                _ -> error "check: Unexpected type in App"
        t2 = typeOf e2
    in
    unify' uf t1 t2 >>= flip check' e1 >>= flip check' e2
check' uf (Lam _ _ e) = check' uf e
check' uf (Let b e) = foldM check' uf (map snd b) >>= flip check' e
check' uf (Case e _ _ alts) = foldM check' uf (map altExpr alts) >>= flip check' e
check' uf (Type _) = Just uf
check' uf (Cast e (t :~ _)) = unify' uf (typeOf e) t >>= flip check' e
check' uf (Coercion (_ :~ _)) = Just uf
check' uf (Tick _ t) = check' uf t
check' uf (NonDet es) = foldM check' uf es
check' uf (SymGen _ _) = Just uf
check' uf (Assert _ e1 e2) = check' uf e1 >>= flip check' e2
check' uf (Assume _ e1 e2) = check' uf e1 >>= flip check' e2

g2UnionNameText :: T.Text
g2UnionNameText = "__G2__UNION__NAME__"

freshG2UnionName :: NameGenM Name
freshG2UnionName = freshSeededStringN g2UnionNameText

isG2UnionName :: Name -> Bool
isG2UnionName (Name n Nothing _ Nothing) = n == g2UnionNameText
isG2UnionName _ = False

assignTyConNames :: ASTContainerM m Type => m -> NameGenM m
assignTyConNames = modifyASTsM assignTyConNames'

assignTyConNames' :: Type -> NameGenM Type
assignTyConNames' (TyCon _ k) = do
    n <- freshG2UnionName
    return (TyVar (Id n k))
assignTyConNames' t = return t 

repVars :: HM.HashMap Name Type -> Expr -> Expr
repVars tys = modifyASTs (repVars' tys)
 
repVars' :: HM.HashMap Name Type -> Expr -> Expr
repVars' tys (Var (Id n _)) | Just t <- HM.lookup n tys = Var (Id n t)
repVars' _ e = e

elimTyForAll :: ASTContainerM m Type => m -> NameGenM m
elimTyForAll = modifyASTsM elimTyForAll'

elimTyForAll' :: Type -> NameGenM Type
elimTyForAll' (TyForAll (Id n _) t) = do
    n' <- freshSeededNameN n
    elimTyForAll' (rename n n' t)
elimTyForAll' t = return t

elimTypes :: ASTContainer m Expr => m -> m
elimTypes = modifyASTs elimTypes'

elimTypes' :: Expr -> Expr
elimTypes' (Lam TypeL _ e) = elimTypes' e
elimTypes' (App e (Type _)) = elimTypes' e
elimTypes' e = e

adjustLetTypes :: ASTContainer m Expr => m -> m
adjustLetTypes = modifyASTs adjustLetTypes'

adjustLetTypes' :: Expr -> Expr
adjustLetTypes' (Let ie e) =
    let
        ie' = map (\(Id n _, le) -> (Id n (typeOf le), le)) ie
        f ((i_old, _), (i_new, _)) fe = modifyASTs (repVar (idName i_old) (Var i_new)) fe
    in
    foldr f (Let ie' e) (zip ie ie')
adjustLetTypes' e = e

substLams :: ASTContainer m Expr => m -> m
substLams = modifyASTs substLams'

substLams' :: Expr -> Expr
substLams' (Lam use i e) = Lam use i $ modifyASTs (repVar (idName i) (Var i)) e
substLams' e = e

scrambleNonFuncLams :: Expr -> NameGenM Expr
scrambleNonFuncLams (Lam u i@(Id n t) e) | not $ isTyFun t = do
    Lam u i <$> (scrambleNonFuncLamLetIds n =<< scrambleNonFuncLams e)
scrambleNonFuncLams (Lam u i e) = Lam u i <$> scrambleNonFuncLams e
scrambleNonFuncLams e = return e

scrambleNonFuncLets :: ASTContainerM m Expr => m -> NameGenM m
scrambleNonFuncLets = modifyASTsM scrambleNonFuncLets'

scrambleNonFuncLets' :: Expr -> NameGenM Expr
scrambleNonFuncLets' (Let b e) = do
    let b' = map idName . filter (not . isTyFun . typeOf) . map fst $ b
    foldM (flip scrambleNonFuncLamLetIds) (Let b e) b'
scrambleNonFuncLets' e = return e

scrambleNonFuncLamLetIds :: Name -> Expr -> NameGenM Expr
scrambleNonFuncLamLetIds n = modifyASTsM (scrambleNonFuncLamLetIds' n)

scrambleNonFuncLamLetIds' :: Name -> Expr -> NameGenM Expr
scrambleNonFuncLamLetIds' n (Var (Id vn t)) | n == vn = Var . Id n <$> scrambleNonFuncLamLetsType t
scrambleNonFuncLamLetIds' _ e = return e

scrambleNonFuncLamLetsType :: Type -> NameGenM Type
scrambleNonFuncLamLetsType = modifyASTsM scrambleNonFuncLamLetsType'

scrambleNonFuncLamLetsType' :: Type -> NameGenM Type
scrambleNonFuncLamLetsType' (TyVar (Id n t)) | isG2UnionName n = do
    new_n <- freshG2UnionName
    return . TyVar $ Id new_n t
scrambleNonFuncLamLetsType' t = return t


repVar :: Name -> Expr -> Expr -> Expr
repVar old new (Var (Id n _)) | n == old = new
repVar _ _ re = re

renameFromUnion :: UFind.UnionFind Name -> Type -> Type
renameFromUnion uf = modifyASTs (renameFromUnion' uf )

renameFromUnion' :: UFind.UnionFind Name -> Type -> Type
renameFromUnion' uf (TyVar (Id n k)) = TyVar (Id (UFind.find n uf) k)
renameFromUnion' _ t = t
