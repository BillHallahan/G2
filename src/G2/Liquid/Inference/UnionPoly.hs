{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module G2.Liquid.Inference.UnionPoly (UnionedTypes, sharedTyConsEE, lookupUT) where

import qualified G2.Data.UFMap as UF
import qualified G2.Data.UnionFind as UFind
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.Monad.AST
import G2.Language.Monad.Naming
import G2.Language.Monad.Support

import qualified Data.HashMap.Lazy as HM
import Data.Maybe

newtype UnionedTypes = UT (HM.HashMap Name Type) deriving Show

lookupUT :: Name -> UnionedTypes -> Maybe Type
lookupUT (Name n m _ l) (UT ut) = HM.lookup (Name n m 0 l) ut

sharedTyConsEE :: [Name] -> ExprEnv -> UnionedTypes
sharedTyConsEE ns eenv =
    let
        f_eenv = E.filterWithKey (\n _ -> n `elem` ns) eenv
        tys = fst $ runNamingM (mapM assignTyConNames (E.map' typeOf f_eenv)) (mkNameGen f_eenv)

        rep_eenv =  E.map (repVars tys) f_eenv
        rep_eenv' = elimTyForAll . elimTypes $ rep_eenv

        union_poly = mconcat . map UF.joinedKeys . HM.elems $ E.map' (fromMaybe UF.empty . checkType) rep_eenv'

        union_tys = fmap (renameFromUnion union_poly) tys
    in
    UT $ HM.mapKeys (\(Name n m _ l) -> Name n m 0 l) union_tys

assignTyConNames :: Type -> NameGenM Type
assignTyConNames = modifyASTsM assignTyConNames'

assignTyConNames' :: Type -> NameGenM Type
assignTyConNames' (TyCon _ k) = do
    n <- freshSeededStringN "__G2__UNION__NAME__"
    return (TyVar (Id n k))
assignTyConNames' t = return t 

repVars :: HM.HashMap Name Type -> Expr -> Expr
repVars tys = modifyASTs (repVars' tys)
 
repVars' :: HM.HashMap Name Type -> Expr -> Expr
repVars' tys (Var (Id n _)) | Just t <- HM.lookup n tys = Var (Id n t)
repVars' _ e = e

elimTyForAll :: ASTContainer m Type => m -> m
elimTyForAll = modifyASTs elimTyForAll'

elimTyForAll' :: Type -> Type
elimTyForAll' (TyForAll _ t) = elimTyForAll' t
elimTyForAll' t = t

elimTypes :: ASTContainer m Expr => m -> m
elimTypes = modifyASTs elimTypes'

elimTypes' :: Expr -> Expr
elimTypes' (App e (Type _)) = elimTypes' e
elimTypes' e = e

renameFromUnion :: UFind.UnionFind Name -> Type -> Type
renameFromUnion uf = modifyASTs (renameFromUnion' uf )

renameFromUnion' :: UFind.UnionFind Name -> Type -> Type
renameFromUnion' uf (TyVar (Id n k)) = TyVar (Id (UFind.find n uf) k)
renameFromUnion' _ t = t