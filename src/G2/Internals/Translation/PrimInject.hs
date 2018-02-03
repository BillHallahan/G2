{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Primitive inejction into the environment
module G2.Internals.Translation.PrimInject
    ( primInject
    , dataInject
    , addPrimsToBase
    , mergeProgs
    , mergeProgTys
    , mergeTCs
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Naming
import G2.Internals.Language.Primitives
import G2.Internals.Language.Syntax
import G2.Internals.Language.TypeEnv
import G2.Internals.Translation.Haskell

import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Text as T

primInject :: (ASTContainer p Expr, ASTContainer p Type) => p -> p
primInject = modifyASTs primInjectT

primInjectT :: Type -> Type
primInjectT (TyConApp (Name "TYPE" (Just "GHC.Prim") _) _) = TYPE
primInjectT (TyConApp (Name "Int#" _ _) _) = TyLitInt
primInjectT (TyConApp (Name "Float#" _ _) _) = TyLitFloat
primInjectT (TyConApp (Name "Double#" _ _) _) = TyLitDouble
primInjectT (TyConApp (Name "Char#" _ _) _) = TyLitChar
primInjectT t = t

dataInject :: Program -> [ProgramType] -> (Program, [ProgramType])
dataInject prog progTy = 
    let
        dcNames = catMaybes . concatMap (\(_, dc) -> map conName (dataCon dc)) $ progTy
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
           , ("quotInt#", Prim Div TyBottom)
           , ("remInt#", Prim Mod TyBottom)

           , ("==##", Prim Eq TyBottom)
           , ("/=##", Prim Neq TyBottom)
           , ("+##", Prim Plus TyBottom)
           , ("*##", Prim Mult TyBottom)
           , ("-##", Prim Minus TyBottom)
           , ("negateDouble#", Prim Negate TyBottom)
           , ("<=##", Prim Le TyBottom)
           , ("<##", Prim Lt TyBottom)
           , (">##", Prim Gt TyBottom)
           , (">=##", Prim Ge TyBottom)

           , ("plusFloat#", Prim Plus TyBottom)
           , ("timesFloat#", Prim Mult TyBottom)
           , ("minusFloat#", Prim Minus TyBottom)
           , ("negateFloat#", Prim Negate TyBottom)
           , ("/##", Prim Div TyBottom)
           , ("divFloat#", Prim Div TyBottom)
           , ("eqFloat#", Prim Eq TyBottom)
           , ("neqFloat#", Prim Neq TyBottom)
           , ("leFloat#", Prim Le TyBottom)
           , ("ltFloat#", Prim Lt TyBottom)
           , ("gtFloat#", Prim Gt TyBottom)
           , ("geFloat#", Prim Ge TyBottom)

           , ("fromIntToFloat", Prim IntToReal TyBottom)
           , ("fromIntToDouble", Prim IntToReal TyBottom)
           , ("error", Prim Error TyBottom)
           , ("errorWithoutStackTrace", Prim Error TyBottom)
           , ("undefined", Prim Error TyBottom)]


{-
primDefs = [ (".+#", Prim Plus TyBottom)
           , (".*#", Prim Mult TyBottom)
           , (".-#", Prim Minus TyBottom)
           , ("negateInt##", Prim Negate TyBottom)
           , (".+##", Prim Plus TyBottom)
           , (".*##", Prim Mult TyBottom)
           , (".-##", Prim Minus TyBottom)
           , ("negateDouble##", Prim Negate TyBottom)
           , ("plusFloat##", Prim Plus TyBottom)
           , ("timesFloat##", Prim Mult TyBottom)
           , ("minusFloat##", Prim Minus TyBottom)
           , ("negateFloat##", Prim Negate TyBottom)
           , ("./##", Prim Div TyBottom)
           , ("divFloat##", Prim Div TyBottom)
           , (".==#", Prim Eq TyBottom)
           , ("./=#", Prim Neq TyBottom)
           , (".==##", Prim Eq TyBottom)
           , ("./=##", Prim Neq TyBottom)
           , ("eqFloat'#", Prim Eq TyBottom)
           , ("neqFloat'#", Prim Neq TyBottom)
           , (".<=#", Prim Le TyBottom)
           , (".<#", Prim Lt TyBottom)
           , (".>#", Prim Gt TyBottom)
           , (".>=#", Prim Ge TyBottom)
           , (".<=##", Prim Le TyBottom)
           , (".<##", Prim Lt TyBottom)
           , (".>##", Prim Gt TyBottom)
           , (".>=##", Prim Ge TyBottom)
           , ("leFloat'#", Prim Le TyBottom)
           , ("ltFloat'#", Prim Lt TyBottom)
           , ("gtFloat'#", Prim Gt TyBottom)
           , ("geFloat'#", Prim Ge TyBottom)
           , ("error", Prim Error TyBottom)
           , ("undefined", Prim Error TyBottom)]
-}

equivMods :: [(T.Text, T.Text)]
equivMods = [ ("GHC.Classes", "GHC.Classes2")
            , ("GHC.Types", "GHC.Types2")
            , ("GHC.Integer", "GHC.Integer2")
            , ("GHC.Integer.Type", "GHC.Integer.Type2")
            , ("GHC.Prim", "GHC.Prim2")
            , ("GHC.Tuple", "GHC.Tuple2")
            , ("GHC.Magic", "GHC.Magic2")
            , ("GHC.CString", "GHC.CString2")
            , ("Data.Map", "Data.Map.Base")

            , ("PrimDefs", "GHC.Classes")
            , ("PrimDefs", "GHC.Types")
            , ("PrimDefs", "GHC.Integer")
            , ("PrimDefs", "GHC.Integer.Type")
            , ("PrimDefs", "GHC.Prim")
            , ("PrimDefs", "GHC.Tuple")
            , ("PrimDefs", "GHC.Magic")
            , ("PrimDefs", "GHC.CString")
            , ("PrimDefs", "GHC.Base")
            , ("PrimDefs", "GHC.Num")
            , ("PrimDefs", "GHC.Int")
            , ("PrimDefs", "GHC.Float")
            , ("PrimDefs", "GHC.Real")
            , ("PrimDefs", "GHC.Rational")
            , ("PrimDefs", "GHC.Err")
            -- , "PrimDefs"
            -- , "GHC.Tuple"
            -- , "Data.Map.Base"
            ]

nameStrEq :: Name -> Name -> Bool
nameStrEq (Name n m _) (Name n' m' _) =
  n == n' && (any id [ m == m'
                     , m `elem` (map (Just . snd) $ filter ((== m') . Just . fst) equivMods)
                     , m' `elem` (map (Just . snd) $ filter ((== m) . Just . fst) equivMods)
                     ])

replaceFromPD :: Id -> Expr -> (Id, Expr)
replaceFromPD i@(Id n t) e =
    let
        e' = fmap snd $ find ((==) (nameOccStr n) . fst) primDefs
    in
    (i, maybe e id e')


addPrimsToBase :: Program -> Program
addPrimsToBase prims = map (map (uncurry replaceFromPD)) prims

mergeProgs :: Program -> Program -> Program
mergeProgs prog prims = prog ++ prims

-- The prog is used to change the names of types in the prog' and primTys
mergeProgTys :: Program -> Program -> [ProgramType] -> [ProgramType] -> (Program, [ProgramType])
mergeProgTys prog prog' progTys primTys =
    (prog', progTys ++ primTys)

mergeTCs :: [(Name, Id, [Id])] -> Program -> ([(Name, Id, [Id])])
mergeTCs tc prog =
  let
    nsp = names prog
    nstc = names tc

    rep = mapMaybe (\n -> fmap ((,) n) $ find (nameStrEq n) nsp) nstc 
  in
  foldr (uncurry rename) tc rep
