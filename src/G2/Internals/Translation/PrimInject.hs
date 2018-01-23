{-# LANGUAGE FlexibleContexts #-}

-- | Primitive inejction into the environment
module G2.Internals.Translation.PrimInject
    ( primInject
    , dataInject
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

primDefs :: [(String, Expr)]
{-
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
           , ("negateDouble##", Prim Negate TyBottom)
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

           , ("fromIntToReal", Prim IntToReal TyBottom)
           , ("error", Prim Error TyBottom)
           , ("undefined", Prim Error TyBottom)]
-}

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

nameStrEq :: Name -> Name -> Bool
nameStrEq (Name n _ _) (Name n' _ _) = n == n'

replaceFromPD :: [Name] -> Id -> Expr -> (Id, Expr)
replaceFromPD ns (Id n t) e =
    let
        n' = maybe n id $ find (nameStrEq n) ns

        e' = fmap snd $ find ((==) (nameOccStr n) . fst) primDefs
    in
    (Id n' t, maybe e id e')

mergeProgs :: Program -> Program -> Program
mergeProgs prog prims =
    let
        ns = names prog ++ names prims

        prims' = map (map (uncurry (replaceFromPD ns))) prims

        n_pairs = nub [ (y, x) | x <- names $ concat prog
                               , y <- names $ map fst $ concat prims
                               , nameStrEq x y]
    in
    foldr (uncurry rename) (prog ++ prims') n_pairs 

-- The prog is used to change the names of types in the prog' and primTys
mergeProgTys :: Program -> Program -> [ProgramType] -> [ProgramType] -> (Program, [ProgramType])
mergeProgTys prog prog' progTys primTys =
    let
        dcNT = nub $ filter (isUpper . head . strName) $ dataNames prog ++ (mapMaybe dataConName $ concatMap (dataCon . snd) primTys)
        dcNE = nub $ filter (isUpper . head . strName) $ dataNames prog
        dcL = mapMaybe (\n -> fmap ((,) n) $ find (nameStrEq n) dcNE) dcNT

        tn = nub $ filter (isUpper . head . strName) $ map fst primTys
        tne = nub $ filter (isUpper . head . strName) $ concatMap tyNames prog
        tL = mapMaybe (\n -> fmap ((,) n) $ find (nameStrEq n) tne) tn
    in
    foldr (uncurry rename) (prog', progTys ++ primTys) (dcL ++ tL)

mergeTCs :: [(Name, Id)] -> Program -> ([(Name, Id)])
mergeTCs tc prog =
  let
    nsp = names prog
    nstc = names tc

    rep = mapMaybe (\n -> fmap ((,) n) $ find (nameStrEq n) nsp) nstc 
  in
  foldr (uncurry rename) tc rep

dataConName :: DataCon -> Maybe Name
dataConName (DataCon n _ _) = Just n
dataConName _ = Nothing

dataNames :: ASTContainer m Expr => m -> [Name]
dataNames = evalASTs dataNames'

dataNames' :: Expr -> [Name]
dataNames' (Var (Id n _)) = [n]
dataNames' (Case _ _ as) = mapMaybe dataNames'' as
dataNames' _ = []

dataNames'' :: Alt -> Maybe Name
dataNames'' (Alt (DataAlt (DataCon n _ _) _) _) = Just n
dataNames'' _ = Nothing

tyNames :: ASTContainer m Type => m -> [Name]
tyNames = evalASTs tyNames'

tyNames' :: Type -> [Name]
tyNames' (TyConApp n _) = [n]
tyNames' _ = []

strName :: Name -> String
strName (Name n _ _) = n
