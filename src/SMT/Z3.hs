module G2.SMT.Z3 where

import G2.Core.Language
import G2.Core.Evaluator
import G2.Core.Utils

import qualified Data.List as L
import qualified Data.Map  as M

-- SMT internal representation

type Z3Name = String

data Stmt = ADecl Z3Name [Z3DCon]
          | CDecl Z3Name Z3Type
          | FDecl Z3Name [Z3Type] Z3Type
          | MAsrt Match Z3DCon
          deriving (Show, Eq)

data Z3DCon = Z3DC Z3Name [(Z3Name, Z3Type)]
            deriving (Show, Eq)

data Z3Type = Z3TyInt
            | Z3TyBool
            | Z3TyReal
            | Z3TyVar Z3Name -- Unfortunately seems like no function types :(
            deriving (Show, Eq)

data Match = MVar Z3Name
           | MFApp Z3Name [Z3Name]
           deriving (Show, Eq)

-- Core to SMT

forceMkZ3Type :: Type -> Z3Type
forceMkZ3Type (TyVar n) = Z3TyVar n
forceMkZ3Type TyInt     = Z3TyInt
forceMkZ3Type TyBool    = Z3TyBool
forceMkZ3Type TyReal    = Z3TyReal
forceMkZ3Type otherwise = error $ "Cannot convert G2 type {" ++
                                  show otherwise ++ "} to Z3 type"

-- We want forced conversions here as ADTs in Z3 can't have higher order args.
mkZ3DC :: DataCon -> Z3DCon
mkZ3DC (name, tag, typ, args) = Z3DC name nts
  where nts = map (\(i, t) -> (name ++ "_" ++ show i, forceMkZ3Type t)) nas
        nas = zip [1..] args

mkZ3ADT :: Type -> Stmt
mkZ3ADT (TyAlg n dcs) = ADecl n (map mkZ3DC dcs)
mkZ3ADT otherwise     = error "Not an ADT"

-- Flattened M.tolist t_env
mkDDecls :: [Type] -> [Stmt]
mkDDecls [] = []
mkDDecls ((TyAlg n dcs):tv) = mkZ3ADT (TyAlg n dcs) : mkDDecls tv
mkDDecls (t:tv) = mkDDecls tv

mkFDecls :: [Expr] -> [Stmt]
mkFDecls [] = []
mkFDecls ((Lam n e t):es) = undefined

mkSMTModels :: State -> [Stmt]
mkSMTModels (tv, ev, ex, pc) = undefined
  where ddecls = mkDDecls $ M.elems tv

-- SMT to String



