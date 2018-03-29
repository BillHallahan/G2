{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Primitive inejction into the environment
module G2.Internals.Translation.PrimInject
    ( primInject
    , dataInject
    , addPrimsToBase
    , mergeProgs
    , mergeProgTys
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Language.TypeEnv

import Data.List
import qualified Data.Text as T

primInject :: (ASTContainer p Expr, ASTContainer p Type) => p -> p
primInject = modifyASTs primInjectT

primInjectT :: Type -> Type
primInjectT (TyConApp (Name "TYPE" (Just "GHC.Prim") _ _) _) = TYPE
primInjectT (TyConApp (Name "Int#" _ _ _) _) = TyLitInt
primInjectT (TyConApp (Name "Float#" _ _ _) _) = TyLitFloat
primInjectT (TyConApp (Name "Double#" _ _ _) _) = TyLitDouble
primInjectT (TyConApp (Name "Char#" _ _ _) _) = TyLitChar
primInjectT t = t

dataInject :: Program -> [ProgramType] -> (Program, [ProgramType])
dataInject prog progTy = 
    let
        dcNames = concatMap (\(_, dc) -> map conName (dataCon dc)) $ progTy
    in
    (modifyASTs (dataInject' dcNames) prog, progTy)

-- TODO: Polymorphic types?
dataInject' :: [(Name, [Type])] -> Expr -> Expr
dataInject' ns v@(Var (Id (Name n m _ _) t)) = 
    case find (\(Name n' m' _ _, _) -> n == n' && m == m') ns of
        Just (n', ts) -> Data (DataCon n' t ts)
        Nothing -> v
dataInject' _ e = e

conName :: DataCon -> (Name, [Type])
conName (DataCon n _ ts) = (n, ts)

primDefs :: [(T.Text, Expr)]
primDefs = [ ("==#", Prim Eq TyBottom)
           , ("/=#", Prim Neq TyBottom)
           , ("+#", Prim Plus TyBottom)
           , ("*#", Prim Mult TyBottom)
           , ("-#", Prim Minus TyBottom)
           , ("negateInt#", Prim Negate TyBottom)
           , ("<=#", Prim Le TyBottom)
           , ("<#", Prim Lt TyBottom)
           , (">#", Prim Gt TyBottom)
           , (">=#", Prim Ge TyBottom)
           , ("divInt#", Prim Quot TyBottom)
           , ("modInt#", Prim Mod TyBottom)
           , ("quotInt#", Prim Quot TyBottom)
           , ("remInt#", Prim Mod TyBottom)

           , ("==##", Prim Eq TyBottom)
           , ("/=##", Prim Neq TyBottom)
           , ("+##", Prim Plus TyBottom)
           , ("*##", Prim Mult TyBottom)
           , ("-##", Prim Minus TyBottom)
           , ("negateDouble#", Prim Negate TyBottom)
           , ("sqrtDouble#", Prim SqRt TyBottom)
           , ("<=##", Prim Le TyBottom)
           , ("<##", Prim Lt TyBottom)
           , (">##", Prim Gt TyBottom)
           , (">=##", Prim Ge TyBottom)

           , ("plusFloat#", Prim Plus TyBottom)
           , ("timesFloat#", Prim Mult TyBottom)
           , ("minusFloat#", Prim Minus TyBottom)
           , ("negateFloat#", Prim Negate TyBottom)
           , ("/##", Prim Div TyBottom)
           , ("divideFloat#", Prim Div TyBottom)
           , ("eqFloat#", Prim Eq TyBottom)
           , ("neqFloat#", Prim Neq TyBottom)
           , ("leFloat#", Prim Le TyBottom)
           , ("ltFloat#", Prim Lt TyBottom)
           , ("gtFloat#", Prim Gt TyBottom)
           , ("geFloat#", Prim Ge TyBottom)

           , ("quotInteger#", Prim Quot TyBottom)

           , ("fromIntToFloat", Prim IntToFloat TyBottom)
           , ("fromIntToDouble", Prim IntToDouble TyBottom)
           , ("error", Prim Error TyBottom)
           , ("errorWithoutStackTrace", Prim Error TyBottom)
           , ("divZeroError", Prim Error TyBottom)
           , ("patError", Prim Error TyBottom)
           , ("absentErr", Prim Error TyBottom)
           , ("undefined", Prim Error TyBottom)]

replaceFromPD :: Id -> Expr -> (Id, Expr)
replaceFromPD i@(Id n _) e =
    let
        e' = fmap snd $ find ((==) (nameOcc n) . fst) primDefs
    in
    (i, maybe e id e')


addPrimsToBase :: Program -> Program
addPrimsToBase prims = map (map (uncurry replaceFromPD)) prims

mergeProgs :: Program -> Program -> Program
mergeProgs prog prims = prog ++ prims

-- The prog is used to change the names of types in the prog' and primTys
mergeProgTys :: [ProgramType] -> [ProgramType] -> [ProgramType]
mergeProgTys progTys primTys =
    progTys ++ primTys