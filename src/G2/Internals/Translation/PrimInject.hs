-- | Primitive inejction into the environment
module G2.Internals.Translation.PrimInject
    ( primInject
    , dataInject
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Syntax

import Data.List
import Data.Maybe

import Debug.Trace

primInject :: (ASTContainer p Expr, ASTContainer p Type) => p -> p
primInject = modifyASTs primInjectE

primInjectE :: Expr -> Expr
primInjectE (Var (Id (Name "!" _ _) _)) = mkNot
primInjectE (Var (Id (Name "&&" _ _) _)) = mkAnd
primInjectE (Var (Id (Name "||" _ _) _)) = mkOr
primInjectE (Var (Id (Name ">=" _ _) _)) = mkGe
primInjectE (Var (Id (Name ">" _ _) _)) = mkGt
primInjectE (Var (Id (Name "==" _ _) _)) = mkEq
primInjectE (Var (Id (Name "/=" _ _) _)) = mkNeq
primInjectE (Var (Id (Name "<" _ _) _)) = mkLt
primInjectE (Var (Id (Name "<=" _ _) _)) = mkLe
primInjectE (Var (Id (Name "+" _ _) _)) = mkPlus
primInjectE (Var (Id (Name "-" _ _) _)) = mkMinus
primInjectE (Var (Id (Name "*" _ _) _)) = mkMult
primInjectE (Var (Id (Name "/" _ _) _)) = mkDiv

primInjectE (Var (Id (Name "I#" _ _) _)) = Data $ PrimCon I
primInjectE (Var (Id (Name "D#" _ _) _)) = Data $ PrimCon D
primInjectE (Var (Id (Name "F#" _ _) _)) = Data $ PrimCon F
primInjectE (Var (Id (Name "C#" _ _) _)) = Data $ PrimCon C
primInjectE e = e

dataInject :: Program -> [ProgramType] -> (Program, [ProgramType])
dataInject prog progTy = 
	let
		dcNames = catMaybes . concatMap (\(_, _, dc) -> map conName dc) $ progTy
	in
	(modifyASTs (dataInject' dcNames) prog, progTy)

-- TODO: Polymorphic types?
dataInject' :: [(Name, [Type])] -> Expr -> Expr
dataInject' ns v@(Var (Id (Name n m _) t)) = 
	case find (\(Name n' m' _, _) -> n == n' && m == m') ns of
		Just (n', ts) -> Data (DataCon n' t ts)
		Nothing -> v
dataInject' _ e = e

conName :: DataCon -> Maybe (Name, [Type])
conName (DataCon n _ ts) = Just (n, ts)
conName _ = Nothing

primTyInject :: Program -> [(Name, Type)] -> Program
primTyInject prog prims = undefined

primTyInject' :: Expr -> [(Name, Type)] -> Expr
primTyInject' (Prim p _) prims = mkTypedPrim p prims
primTyInject' expr _ = expr

mkTypedPrim :: Primitive -> [(Name, Type)] -> Expr
mkTypedPrim = undefined

