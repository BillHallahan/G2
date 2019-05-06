{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Primitive inejction into the environment
module G2.Translation.PrimInject
    ( primInject
    , dataInject
    , addPrimsToBase
    , mergeProgs
    , mergeProgTys
    ) where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax
import G2.Language.Typing
import G2.Language.TypeEnv

import Data.List
import qualified Data.Text as T

primInject :: ASTContainer p Type => p -> p
primInject = modifyASTs primInjectT

primInjectT :: Type -> Type
primInjectT (TyCon (Name "TYPE" (Just "GHC.Prim") _ _) _) = TYPE
primInjectT (TyCon (Name "Int#" _ _ _) _) = TyLitInt
primInjectT (TyCon (Name "Word#" _ _ _) _) = TyLitInt
primInjectT (TyCon (Name "Float#" _ _ _) _) = TyLitFloat
primInjectT (TyCon (Name "Double#" _ _ _) _) = TyLitDouble
primInjectT (TyCon (Name "Char#" _ _ _) _) = TyLitChar
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
        Just (n', _) -> Data (DataCon n' t)
        Nothing -> v
dataInject' _ e = e

conName :: DataCon -> (Name, [Type])
conName (DataCon n t) = (n, anonArgumentTypes $ t)

primDefs :: [ProgramType] -> [(T.Text, Expr)]
primDefs pt = case boolName pt of
                Just n -> primDefs' n
                Nothing -> error "Bool type not found"

primDefs' :: Name -> [(T.Text, Expr)]
primDefs' b = [ ("==#", Prim Eq $ tyIntIntBool b)
              , ("/=#", Prim Neq $ tyIntIntBool b)
              , ("+#", Prim Plus tyIntIntInt)
              , ("*#", Prim Mult tyIntIntInt)
              , ("-#", Prim Minus tyIntIntInt)
              , ("negateInt#", Prim Negate tyIntInt)
              , ("<=#", Prim Le $ tyIntIntBool b)
              , ("<#", Prim Lt $ tyIntIntBool b)
              , (">#", Prim Gt $ tyIntIntBool b)
              , (">=#", Prim Ge $ tyIntIntBool b)
              , ("divInt#", Prim Quot tyIntIntInt)
              , ("modInt#", Prim Mod tyIntIntInt)
              , ("quotInt#", Prim Quot tyIntIntInt)
              , ("remInt#", Prim Mod tyIntIntInt)

              , ("==##", Prim Eq $ tyDoubleDoubleBool b)
              , ("/=##", Prim Neq $ tyDoubleDoubleBool b)
              , ("+##", Prim Plus tyDoubleDoubleDouble)
              , ("*##", Prim Mult tyDoubleDoubleDouble)
              , ("-##", Prim Minus tyDoubleDoubleDouble)
              , ("negateDouble#", Prim Negate tyDoubleDouble)
              , ("sqrtDouble#", Prim SqRt tyDoubleDoubleDouble)
              , ("<=##", Prim Le $ tyDoubleDoubleBool b)
              , ("<##", Prim Lt $ tyDoubleDoubleBool b)
              , (">##", Prim Gt $ tyDoubleDoubleBool b)
              , (">=##", Prim Ge $ tyDoubleDoubleBool b)

              , ("plusFloat#", Prim Plus tyFloatFloatFloat)
              , ("timesFloat#", Prim Mult tyFloatFloatFloat)
              , ("minusFloat#", Prim Minus tyFloatFloatFloat)
              , ("negateFloat#", Prim Negate tyFloatFloat)
              , ("sqrtFloat#", Prim SqRt tyFloatFloatFloat)
              , ("/##", Prim Div tyFloatFloatFloat)
              , ("divideFloat#", Prim Div tyFloatFloatFloat)
              , ("eqFloat#", Prim Eq $ tyFloatFloatBool b)
              , ("neqFloat#", Prim Neq $ tyFloatFloatBool b)
              , ("leFloat#", Prim Le $ tyFloatFloatBool b)
              , ("ltFloat#", Prim Lt $ tyFloatFloatBool b)
              , ("gtFloat#", Prim Gt $ tyFloatFloatBool b)
              , ("geFloat#", Prim Ge $ tyFloatFloatBool b)

              , ("quotInteger#", Prim Quot tyIntIntInt)

              , ("float2Int#", Prim ToInt (TyFun TyLitFloat TyLitInt))
              , ("int2Float#", Prim IntToFloat (TyFun TyLitInt TyLitFloat))
              , ("fromIntToFloat", Prim IntToFloat (TyFun TyLitInt TyLitFloat))
              , ("double2Int#", Prim ToInt (TyFun TyLitDouble TyLitInt))
              , ("int2Double#", Prim IntToDouble (TyFun TyLitInt TyLitDouble))
              , ("fromIntToDouble", Prim IntToDouble (TyFun TyLitInt TyLitDouble))

              , ("absentErr", Prim Error TyBottom)
              , ("error", Prim Error TyBottom)
              , ("errorWithoutStackTrace", Prim Error TyBottom)
              , ("divZeroError", Prim Error TyBottom)
              , ("patError", Prim Error TyBottom)
              , ("succError", Prim Error TyBottom)
              , ("toEnumError", Prim Error TyBottom)
              , ("undefined", Prim Error TyBottom)]

tyIntInt :: Type
tyIntInt = TyFun TyLitInt TyLitInt

tyIntIntBool :: Name -> Type
tyIntIntBool n = TyFun TyLitInt $ TyFun TyLitInt (TyCon n TYPE)

tyIntIntInt :: Type
tyIntIntInt = TyFun TyLitInt $ TyFun TyLitInt TyLitInt

tyDoubleDouble :: Type
tyDoubleDouble = TyFun TyLitDouble TyLitDouble

tyDoubleDoubleBool :: Name -> Type
tyDoubleDoubleBool n = TyFun TyLitDouble $ TyFun TyLitDouble (TyCon n TYPE)

tyDoubleDoubleDouble :: Type
tyDoubleDoubleDouble = TyFun TyLitDouble $ TyFun TyLitDouble TyLitDouble

tyFloatFloat :: Type
tyFloatFloat = TyFun TyLitFloat TyLitFloat

tyFloatFloatBool :: Name -> Type
tyFloatFloatBool n = TyFun TyLitFloat $ TyFun TyLitFloat (TyCon n TYPE)

tyFloatFloatFloat :: Type
tyFloatFloatFloat = TyFun TyLitFloat $ TyFun TyLitFloat TyLitFloat

boolName :: [ProgramType] -> Maybe Name
boolName = find ((==) "Bool" . nameOcc) . map fst

replaceFromPD :: [ProgramType] -> Id -> Expr -> (Id, Expr)
replaceFromPD pt i@(Id n _) e =
    let
        e' = fmap snd $ find ((==) (nameOcc n) . fst) (primDefs pt)
    in
    (i, maybe e id e')


addPrimsToBase :: [ProgramType] -> Program -> Program
addPrimsToBase pt prims = map (map (uncurry (replaceFromPD pt))) prims

mergeProgs :: Program -> Program -> Program
mergeProgs prog prims = prog ++ prims

-- The prog is used to change the names of types in the prog' and primTys
mergeProgTys :: [ProgramType] -> [ProgramType] -> [ProgramType]
mergeProgTys progTys primTys =
    progTys ++ primTys  
