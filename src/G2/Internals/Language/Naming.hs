module G2.Internals.Language.Naming
    ( NameGen
    , nameToStr
    , nameGen
    , freshName
    , freshNames
    , freshSeededName
    , freshSeededNames
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Syntax

import qualified Data.HashMap.Lazy as HM
import Data.List

newtype NameGen = NameGen (HM.HashMap (String, Maybe String) Int) deriving (Show, Eq, Read)

nameToStr :: Name -> String
nameToStr (Name n (Just m) i) = n ++ "_j_m_" ++ m ++ "_" ++ show i
nameToStr (Name n Nothing i) = n ++ "_j_a_" ++ show i

nameGen :: Program -> NameGen
nameGen = NameGen
        . foldr (\(Name n m i) hm -> HM.insertWith (max) (n, m) i hm) HM.empty
        . allNames

allNames :: Program -> [Name]
allNames prog = nub (binds ++ expr_names ++ type_names)
  where
        binds = concatMap (map (idName . fst)) prog
        expr_names = evalASTs exprTopNames prog
        type_names = evalASTs typeTopNames prog

        exprTopNames :: Expr -> [Name]
        exprTopNames (Var var) = [idName var]
        exprTopNames (Lam b _) = [idName b]
        exprTopNames (Let kvs _) = map (idName . fst) kvs
        exprTopNames (Case _ cvar as) = idName cvar :
                                        concatMap (\(Alt am _) -> altMatchNames am) as
        exprTopNames _ = []

        altMatchNames :: AltMatch -> [Name]
        altMatchNames (DataAlt dc i) = dataConName dc ++ (map idName i)
        altMatchNames _ = []

        dataConName :: DataCon -> [Name]
        dataConName (DataCon n _ _) = [n]
        dataConName _ = []

        typeTopNames :: Type -> [Name]
        typeTopNames (TyVar n _) = [n]
        typeTopNames (TyConApp n _) = [n]
        typeTopNames (TyForAll (NamedTyBndr n) _) = [n]
        typeTopNames _ = []

rename :: Name -> Name -> Program -> Program
rename old new = modifyASTs renameExpr . map renameBinds
    where
        renameBinds :: Binds -> Binds 
        renameBinds = map renameT

        renameId :: Id -> Id
        renameId i@(Id n t) = if n == old then Id new t else i

        renameT :: (Id, Expr) -> (Id, Expr)
        renameT (i@(Id n t), e) = (renameId i, e)

        renameExpr :: Expr -> Expr
        renameExpr (Var i) = Var (renameId i)
        renameExpr (Data d) = Data (renameDataCon d)
        renameExpr (Lam i e) = Lam (renameId i) e
        renameExpr (Let n e) = Let (renameBinds n) e
        renameExpr (Case e i a) = Case e (renameId i) (map renameAlt a)

        renameDataCon :: DataCon -> DataCon
        renameDataCon d@(DataCon n t ts) = if n == old then DataCon new t ts else d
        renameDataCon d = d

        renameAlt :: Alt -> Alt
        renameAlt (Alt am e) = Alt (renameAltMatch am) e

        renameAltMatch :: AltMatch -> AltMatch
        renameAltMatch (DataAlt dc i) = DataAlt (renameDataCon dc) (map renameId i)
        renameAltMatch am = am 

freshSeededName :: Name -> NameGen -> (Name, NameGen)
freshSeededName (Name n m _) (NameGen hm) =
    let
        i' = HM.lookupDefault 0 (n, m) hm
        hm' = HM.insert (n, m) (i' + 1) hm
    in
    (Name n m i', NameGen hm')

freshSeededNames :: [Name] -> NameGen -> ([Name], NameGen)
freshSeededNames [] r = ([], r)
freshSeededNames (name:ns) r =
    let
        (name', confs') = freshSeededName name r
        (ns', confs'') = freshSeededNames ns confs'
    in
    (name':ns', confs'') 

freshName :: NameGen -> (Name, NameGen)
freshName confs = freshSeededName seed confs
  where
    seed = Name "fs?" Nothing 0

freshNames :: Int -> NameGen -> ([Name], NameGen)
freshNames i confs = freshSeededNames (replicate i (Name "fs?" Nothing 0)) confs