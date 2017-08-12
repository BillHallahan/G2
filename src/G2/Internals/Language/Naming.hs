module G2.Internals.Language.Naming
    ( Renamer
    , nameToStr
    , allNames
    , freshStr
    , freshName
    , freshSeededName
    , freshSeededNames
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Support
import G2.Internals.Language.Syntax

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

newtype Renamer = Renamer [Name] deriving (Show, Eq, Read)

nameToStr :: Name -> String
nameToStr = undefined

allNames :: State -> Renamer
allNames state = Renamer $ L.nub (expr_names ++ type_names ++ eenv_keys ++ tenv_keys)
  where
        expr_names = evalASTs exprTopNames state
        type_names = evalASTs typeTopNames state
        eenv_keys = (M.keys . expr_env) state
        tenv_keys = (M.keys . type_env) state

        exprTopNames :: Expr -> [Name]
        exprTopNames (Var var) = [idName var]
        exprTopNames (Lam b _) = [idName b]
        exprTopNames (Let kvs _) = map (idName . fst) kvs
        exprTopNames (Case _ cvar as) = (idName cvar) :
                                        concatMap (\(Alt _ ps _) -> map idName ps) as
        exprTopNames _ = []

        typeTopNames :: Type -> [Name]
        typeTopNames (TyVar n) = [n]
        typeTopNames (TyConApp (TyCon n) _) = [n]
        typeTopNames (TyForAll (NamedTyBndr n) _) = [n]
        typeTopNames _ = []

nameOccStr :: Name -> String
nameOccStr (Name occ _ _) = occ

nameInt :: Name -> Int
nameInt (Name _ _ int) = int

freshStr :: Int -> String -> S.Set String -> String
freshStr rand seed confs = if S.member seed confs
    then freshStr (rand + 1) (seed ++ [pick]) confs else seed
  where
    pick = bank !! index
    index = raw_i `mod` (length bank)
    raw_i = (abs rand) * prime
    prime = 151  -- The original? :)
    bank = lower ++ upper ++ nums
    lower = "abcdefghijlkmnopqrstuvwxyz"
    upper = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    nums = "1234567890"

freshName :: Renamer -> (Name, Renamer)
freshName confs = freshSeededName seed confs
  where
    seed = Name "fs?" Nothing 0

freshSeededName :: Name -> Renamer -> (Name, Renamer)
freshSeededName seed (Renamer confs) = (new_n, Renamer (new_n:confs))
  where
    Name occ mdl unq = seed
    occ' = freshStr 1 occ (S.fromList alls)
    unq' = maxs + 1
    alls = map nameOccStr confs
    maxs = L.maximum (unq : map nameInt confs)
    new_n = Name occ' mdl unq'

freshNames :: [a] -> Renamer -> ([Name], Renamer)
freshNames as confs = freshSeededNames seeds confs
  where
    seeds = [Name ("fs" ++ show i ++ "?") Nothing 0 | i <- [1..(length as)]]

freshSeededNames :: [Name] -> Renamer -> ([Name], Renamer)
freshSeededNames (name:ns) r@(Renamer confs) =
    let
        (name', confs') = freshSeededName name r
        (ns', confs'') = freshSeededNames ns confs'
    in
    (name':ns', confs'') 
    
    -- confs' = Renamer (name' : confs)



