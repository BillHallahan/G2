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

mkZ3Type :: Type -> Z3Type
mkZ3Type (TyVar n) = Z3TyVar n
mkZ3Type TyInt     = Z3TyInt
-- mkZ3Type TyBool    = Z3TyBool
mkZ3Type TyReal    = Z3TyReal
mkZ3Type otherwise = error $ "Cannot convert type {" ++ show otherwise ++ "}"

-- We want forced conversions here as ADTs in Z3 can't have higher order args.
mkZ3DC :: DataCon -> Z3DCon
mkZ3DC (name, tag, typ, args) = Z3DC name nts
  where nts = map (\(i, t) -> (name ++ "?D?" ++ show i, mkZ3Type t)) nas
        nas = zip [1..] args

mkZ3ADT :: Type -> Stmt
mkZ3ADT (TyAlg n dcs) = ADecl n (map mkZ3DC dcs)
mkZ3ADT otherwise     = error "Not an ADT"

mkADecls :: [Type] -> [Stmt]
mkADecls [] = []
mkADecls ((TyAlg n dcs):tv) = mkZ3ADT (TyAlg n dcs) : mkADecls tv
mkADecls (t:tv) = mkADecls tv  -- Skip the non-ADTs

-- Now we want to handle the function declarations
unTyFun :: Type -> ([Type], Type)
unTyFun (TyFun l r) = let (as, t) = unTyFun r in (l:as ,t)
unTyFun otherwise   = ([], otherwise)

cfDeclared :: [Stmt] -> Name -> Bool
cfDeclared [] n = False
cfDeclared ((CDecl cn t):ds) n = if cn == n then True else cfDeclared ds n
cfDeclared ((FDecl fn as t):ds) n = if fn == n then True else cfDeclared ds n
cfDeclared (d:ds) n = cfDeclared ds n

mkCDecl :: Name -> Type -> Stmt
mkCDecl n t = CDecl n (mkZ3Type t)

mkFDecl :: Name -> Type -> Stmt
mkFDecl n t = FDecl n zas zr
  where (as, r) = unTyFun t
        zas     = map mkZ3Type as
        zr      = mkZ3Type r

mkAsrts :: PC -> [Stmt]
mkAsrts [] = []
mkAsrts ((exp, (dc, args)):pcs) = e_asrt ++ mkAsrts pcs
  where (h:args) = unapp exp
        e_asrt   = case h of
            Var n t   -> case args of
                [] -> let cdecl  = mkCDecl n t
                          cmatch = MVar n
                          z3dc   = mkZ3DC dc
                      in [cdecl, MAsrt cmatch z3dc]
                as -> let fdecl    = mkFDecl n (typeOf exp)
                          -- argdecls = map (\a -> mkCDecl (n ++ "?" ++ a) (typeOf a)) args
                          fmatch   = []
                      in undefined
            DCon dc   -> []  -- Driven by structure otherwise.
            otherwise -> []


{-
mkAsrts :: PC -> [Stmt]
mkAsrts [] = []
mkAsrts ((exp, alt):pcs) = e_asrt ++ mkAsrts pcs
  where (h:args) = unapp exp
        e_asrt   = case h of
            Var n t   -> []
            -- Var n t   -> let fname = n ++ "?F?" ++ (show $ length args)
            --              in 
            DCon dc t -> [] -- We rely on structure to drive execution.
            otherwise -> []
-}


{-
mkCFDecls :: [(Name, Expr)] -> [Stmt]
mkCFDecls [] = []
mkCFDecls ((n, (Lam b e t)):ev) = undefined
mkCFDecls ((n, e):ev) = CDecl n (mkZ3Type $ typeOf e) : mkCFDecls ev
-}

mkSMTModels :: State -> [Stmt]
mkSMTModels (tv, ev, ex, pc) = ddecls ++ fdecls
  where ddecls = mkADecls $ M.elems tv
        fdecls = undefined

-- SMT to String



