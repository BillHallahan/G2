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

import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M

-- | Renamer
-- Allows consistent mapping of names to strings.
data Renamer = Renamer StrGen (M.Map Name String)

data GNameGen a b c = GNameGen (a -> b) (a -> Int -> c) (HM.HashMap b Int)
type NameGen = GNameGen Name (String, Maybe String) Name
type StrGen = GNameGen String String String

instance Eq b => Eq (GNameGen a b c) where
    (==) (GNameGen _ _ m) (GNameGen _ _ m') = m == m'

instance Show b => Show (GNameGen a b c) where
    show (GNameGen _ _ m) = show m

-- | nameToStr
-- Returns a unique String for a name,
-- and a new renamer that has that Name to String mapping stored.
-- You must keep using the same renamer "chain", there is no
-- guarentee that nameToStr n r1 == nameToStr n r2 otherwise
nameToStr :: Name -> Renamer -> (String, Renamer)
nameToStr n@(Name na mo i) r@(Renamer sg m) =
    let
        lookup_s = M.lookup n m
        s = case mo of
                Just mo' -> na ++ mo'
                Nothing -> na
        (new_s, new_sg) = freshSeededName s sg
        new_m = M.insert n new_s m
    in
    case lookup_s of
        Just s' -> (s', r)
        Nothing -> (new_s, Renamer new_sg new_m)

nameGen :: Program -> NameGen
nameGen = GNameGen (\(Name n m _) -> (n, m)) (\(Name n m _) i -> Name n m i)
        . foldr (\(Name n m i) hm -> HM.insertWith (max) (n, m) i hm) HM.empty
        . allNames

strGen :: StrGen
strGen = GNameGen id (\s i -> s ++ "_" ++ show i) HM.empty

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

freshSeededName :: (Ord a, Eq b, Hashable b) => a -> GNameGen a b c -> (c, GNameGen a b c)
freshSeededName n (GNameGen f g hm) =
    let
        k = f n
        i' = HM.lookupDefault 0 k hm
        hm' = HM.insert k (i' + 1) hm
    in
    (g n i', GNameGen f g hm')

freshSeededNames :: (Ord a, Eq b, Hashable b) => [a] -> GNameGen a b c -> ([c], GNameGen a b c)
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