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

newtype UnionedTypes = UT (HM.HashMap Name Type) deriving Show

lookupUT :: Name -> UnionedTypes -> Maybe Type
lookupUT (Name n m _ l) (UT ut) = HM.lookup (Name n m 0 l) ut

sharedTyConsEE :: [Name] -> ExprEnv -> UnionedTypes
sharedTyConsEE ns eenv =
    let
        f_eenv = E.filterWithKey (\n _ -> n `elem` ns) eenv
        tys = fst $ runNamingM (mapM assignTyConNames (E.map' typeOf f_eenv)) (mkNameGen f_eenv)

        rep_eenv =  E.map (repVars tys) f_eenv
        rep_eenv' = elimTypes $ rep_eenv
        rep_eenv'' = substLams
                   . adjustLetTypes
                   . fst
                   $ runNamingM (E.mapM (assignTyConNames >=> elimTyForAll) rep_eenv') (mkNameGen rep_eenv')

        union_poly = mconcat . map UF.joinedKeys . HM.elems
                   . E.map' (fromMaybe UF.empty . checkType)
                   $ rep_eenv''

        union_tys = fmap (renameFromUnion union_poly) tys
    in
    UT $ HM.mapKeys (\(Name n m _ l) -> Name n m 0 l) union_tys

assignTyConNames :: ASTContainerM m Type => m -> NameGenM m
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

repVar :: Name -> Expr -> Expr -> Expr
repVar old new (Var (Id n _)) | n == old = new
repVar _ _ re = re

renameFromUnion :: UFind.UnionFind Name -> Type -> Type
renameFromUnion uf = modifyASTs (renameFromUnion' uf )

renameFromUnion' :: UFind.UnionFind Name -> Type -> Type
renameFromUnion' uf (TyVar (Id n k)) = TyVar (Id (UFind.find n uf) k)
renameFromUnion' _ t = t