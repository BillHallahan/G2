-- | Primitive inejction into the environment
module G2.Internals.Translation.PrimInject
    ( primInject
    , dataInject
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Translation.Haskell

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

occFind :: Name -> [Name] -> Maybe Name
occFind _ [] = Nothing
occFind key (n:ns) = if (nameOccStr key == nameOccStr n)
                         then Just n
                         else occFind key ns

mergeProgs :: Program -> [(Name, Type)] -> Program
mergeProgs prog pdefs = injects : prog
  where
    prog_names = progNames prog
    used = filter (\n -> (nameOccStr n) `elem` prim_list) prog_names

    defs = map (\(n, t) -> (fromMaybe n $ occFind n used, t)) pdefs
    injects = map (\(n, t) -> (Id n t, mkPrim defs n)) defs

