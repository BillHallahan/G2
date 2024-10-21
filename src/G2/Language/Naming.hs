{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Language.Naming
    ( nameOcc
    , nameModule
    , nameUnique
    , nameTuple
    , nameLoc
    , NameGen
    , Named (..)
    , namesList
    , doRename
    , doRenames
    , renameAll
    , nameToStr
    , nameToBuilder
    , strToName
    , maybe_StrToName
    , builderToName

    , mkNameGen
    , varIds
    , varNames
    , exprNames
    , typeNames

    , renameExprs
    , renamesExprs
    , renameExpr
    , renameVars

    , freshSeededString
    , freshSeededStrings

    , freshName
    , freshNames
    , freshSeededName
    , freshSeededNames

    , freshId
    , freshSeededId
    , freshIds
    , freshVar

    , mapNG
    ) where

import qualified G2.Data.UFMap as UF
import G2.Language.AST
import G2.Language.KnownValues
import G2.Language.Syntax
import G2.Language.TypeEnv

import Data.Data (Data, Typeable)
import Data.Foldable
import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.List.Utils
import qualified Data.Map as M
import qualified Data.Sequence as S
import qualified Data.Text as T
import Data.Tuple
import qualified Text.Builder as TB

-- | Extract the "occurence" from a `Name`.
--
-- >>> nameOcc (Name "x" (Just "mod") 100 Nothing)
-- "x"
nameOcc :: Name -> T.Text
nameOcc (Name occ _ _ _) = occ

-- | Extract the module from a `Name`.
--
-- >>> nameModule (Name "x" (Just "mod") 100 Nothing)
-- Just "mod"
nameModule :: Name -> Maybe T.Text
nameModule (Name _ mb _ _) = mb

-- | Extract the "unique" from a `Name`.
--
-- >>> nameUnique (Name "x" (Just "mod") 100 Nothing)
-- 100
nameUnique :: Name -> Int
nameUnique (Name _ _ i _) = i

-- | Get a tuple with the "occurence" and module of a `Name`.
--
-- >>> nameTuple (Name "x" (Just "mod") 100 Nothing)
-- ("x", Just "mod")
nameTuple :: Name -> (T.Text, Maybe T.Text)
nameTuple n = (nameOcc n, nameModule n)

-- | Get the location of a `Name`.
nameLoc :: Name -> Maybe Span
nameLoc (Name _ _ _ s) = s

-- | Allows the creation of fresh `Name`s.
newtype NameGen = NameGen (HM.HashMap (T.Text, Maybe T.Text) Int)
                deriving (Show, Eq, Read, Typeable, Data)

-- nameToStr relies on NameCleaner eliminating all '_', to preserve uniqueness
-- | Converts a `Name` to a string, which is useful to interact with solvers.
nameToStr :: Name -> String
nameToStr (Name n (Just m) i _) = T.unpack n ++ "_m_" ++ T.unpack m ++ "_" ++ show i
nameToStr (Name n Nothing i _) = T.unpack n ++ "_n__" ++ show i

-- | Similar to `nameToStr`, but converts a `Name` to a `TB.Builder`.
nameToBuilder :: Name -> TB.Builder
nameToBuilder (Name n (Just m) i _) = mconcat [TB.text n, TB.text "_m_", TB.text m, TB.text "_", TB.string $ show i]
nameToBuilder (Name n Nothing i _) = mconcat [TB.text n, TB.text "_n__", TB.string $ show i]

-- | Converts a `String` generated by `nameToStr` to a `Name`.
-- Loses location information
strToName :: String -> Name
strToName str =
    case maybe_StrToName str of
        Just n -> n
        Nothing -> error "strToName: Bad conversion"

maybe_StrToName :: String -> Maybe Name
maybe_StrToName str
    | (n, _:q:_:mi) <- breakList (\s -> isPrefixOf "_m_" s || isPrefixOf "_n_" s) str
    , (m, _:i) <- break ((==) '_') mi =
    let
        m' = if q == 'm' then Just m else Nothing
    in
    Just $ Name (T.pack n) (fmap T.pack m') (read i :: Int) Nothing
    | otherwise = Nothing

-- | Converts a `TB.Builder` generated by `nameToBuilder` to a `Name`.
-- Loses location information
builderToName :: TB.Builder -> Name
builderToName txt = strToName $ show txt

-- | Initializes a `NameGen`.  The returned `NameGen` is guarenteed to not give any `Name`
-- in the given `Named` type.
mkNameGen :: Named n => n -> NameGen
mkNameGen nmd =
    let
        allNames = toList $ names nmd
    in
    NameGen (HM.fromListWith max $ map (\(Name n m i _) -> ((n, m), i + 1)) allNames)

-- | Returns all @Var@ Ids in an ASTContainer
varIds :: (ASTContainer m Expr) => m -> [Id]
varIds = evalASTs varIds'

varIds' :: Expr -> [Id]
varIds' (Var i) = [i]
varIds' _ = []

varNames :: (ASTContainer m Expr) => m -> [Name]
varNames = map idName . varIds

-- Returns every `Name` that appears in an `Expr`, but ignores those only in `Type`s.
exprNames :: (ASTContainer m Expr) => m -> [Name]
exprNames = evalASTs exprTopNames

exprTopNames :: Expr -> [Name]
exprTopNames (Var var) = [idName var]
exprTopNames (Prim (MutVar mv) _) = [mv]
exprTopNames (Data dc) = dataConName dc
exprTopNames (Lam _ b _) = [idName b]
exprTopNames (Let kvs _) = map (idName . fst) kvs
exprTopNames (Case _ cvar _ as) = idName cvar :
                                concatMap (\(Alt am _) -> altMatchNames am)
                                          as
exprTopNames (Assume (Just is) _ _) = [funcName is]
exprTopNames (Assert (Just is) _ _) = [funcName is]
exprTopNames _ = []

altMatchNames :: AltMatch -> [Name]
altMatchNames (DataAlt dc i) = dataConName dc ++ (map idName i)
altMatchNames _ = []

dataConName :: DataCon -> [Name]
dataConName (DataCon n _ _ _) = [n]

typeNames :: (ASTContainer m Type) => m -> [Name]
typeNames = evalASTs typeTopNames

typeTopNames :: Type -> [Name]
typeTopNames (TyVar i) = [idName i]
typeTopNames (TyCon n _) = [n]
typeTopNames (TyForAll v _) = [idName v]
typeTopNames _ = []

doRename :: Named a => Name -> NameGen -> a -> (a, NameGen)
doRename n ngen x = (rename n n' x, ngen')
  where (n', ngen') = freshSeededName n ngen

doRenames :: Named a => [Name] -> NameGen -> a -> (a, NameGen)
doRenames ns ng e =
    let
        (ns', ng') = freshSeededNames ns ng
        hm = HM.fromList $ zip ns ns'
    in
    (renames hm e, ng')

renameAll :: (Named a) => a -> NameGen -> (a, NameGen)
renameAll x ng =
    let
        old = nub . toList $ names x
    in
    doRenames old ng x

namesList :: Named a => a -> [Name]
namesList = toList . names

-- | Types that contain `Name`@s@
class Named a where
    names :: a -> S.Seq Name
    rename :: Name -> Name -> a -> a
    renames :: HM.HashMap Name Name -> a -> a

    renames hm e = HM.foldrWithKey (\k v -> rename k v) e hm

instance Named Name where
    {-# INLINE names #-}
    names n = S.singleton n
    {-# INLINE rename #-}
    rename old (Name nn nm ni _) n@(Name _ _ _ l) = if old == n then Name nn nm ni l else n
    {-# INLINE renames #-}
    renames hm n@(Name _ _ _ l) =
        case HM.lookupDefault n n hm of
            Name n' m' i _ -> Name n' m' i l

instance Named Id where
    {-# INLINE names #-}
    names (Id n t) = n S.<| names t
    {-# INLINE rename #-}
    rename old new (Id n t) = Id (rename old new n) (rename old new t)
    {-# INLINE renames #-}
    renames hm (Id n t) = Id (renames hm n) (renames hm t)

instance Named Expr where
    names = eval go
        where
            go :: Expr -> S.Seq Name
            go (Var i) = names i
            go (Prim p t) = names p <> names t
            go (Data d) = names d
            go (Lam _ i _) = names i
            go (Let b _) = foldr (<>) S.empty $ map (names . fst) b
            go (Case _ i t a) = names i <> names t <> (foldr (<>) S.empty $ map (names . altMatch) a)
            go (Type t) = names t
            go (Cast _ c) = names c
            go (Coercion c) = names c
            go (Tick t _) = names t
            go (SymGen _ t) = names t
            go (Assume is _ _) = names is
            go (Assert is _ _) = names is
            go _ = S.empty

    rename old new = modify go
      where
        go :: Expr -> Expr
        go (Var i) = Var (rename old new i)
        go (Data d) = Data (rename old new d)
        go (Lam u i e) = Lam u (rename old new i) e
        go (Let b e) =
            let b' = map (\(n, e') -> (rename old new n, e')) b
            in Let b' e
        go (Case e i t a) =
            Case e (rename old new i) (rename old new t) (map goAlt a)
        go (Type t) = Type (rename old new t)
        go (Cast e c) = Cast e (rename old new c)
        go (Coercion c) = Coercion (rename old new c)
        go (Tick t e) = Tick (rename old new t) e
        go (SymGen sl t) = SymGen sl (rename old new t)
        go (Assume is e e') = Assume (rename old new is) e e'
        go (Assert is e e') = Assert (rename old new is) e e'
        go e = e

        goAlt :: Alt -> Alt
        goAlt (Alt am e) = Alt (rename old new am) e

    renames hm = modify go
        where
            go :: Expr -> Expr
            go (Var i) = Var (renames hm i)
            go (Data d) = Data (renames hm d)
            go (Lam u i e) = Lam u (renames hm i) e
            go (Let b e) = 
                let b' = map (\(n, e') -> (renames hm n, e')) b
                in Let b' e
            go (Case e i t a) = Case e (renames hm i) (renames hm t) (map goAlt a)
            go (Type t) = Type (renames hm t)
            go (Cast e c) = Cast e (renames hm c)
            go (Coercion c) = Coercion (renames hm c)
            go (Tick t e) = Tick (renames hm t) e
            go (SymGen sl t) = SymGen sl (renames hm t)
            go (Assume is e e') = Assume (renames hm is) e e'
            go (Assert is e e') = Assert (renames hm is) e e'
            go e = e

            goAlt :: Alt -> Alt
            goAlt (Alt am e) = Alt (renames hm am) e

renameExprs :: ASTContainer m Expr => [(Name, Name)] -> m -> m
renameExprs n = renamesExprs (HM.fromList n)

-- | Rename only the names in an `Expr` that are the `Name` of an `Id`/`Let`/`Data`/`Case` Binding.
-- Does not change Types.
renameExpr :: ASTContainer m Expr => Name -> Name -> m -> m
renameExpr old new = modifyASTs (renameExpr' old new)

renameExpr' :: Name -> Name -> Expr -> Expr
renameExpr' old new (Var i) = Var (renameExprId old new i)
renameExpr' old new (Prim (MutVar mv) t) = (Prim (MutVar $ rename old new mv) t)
renameExpr' old new (Data d) = Data (renameExprDataCon old new d)
renameExpr' old new (Lam u i e) = Lam u (renameExprId old new i) e
renameExpr' old new (Let b e) = Let (map (\(b', e') -> (renameExprId old new b', e')) b) e
renameExpr' old new (Case e i t a) = Case e (renameExprId old new i) t $ map (renameExprAlt old new) a
renameExpr' old new (Assume is e e') = Assume (fmap (rename old new) is) e e'
renameExpr' old new (Assert is e e') = Assert (fmap (rename old new) is) e e'
renameExpr' _ _ e = e

-- | Renames only the @Vars@ in an `Expr`.
renameVars :: ASTContainer m Expr => Name -> Name -> m -> m
renameVars old new = modifyASTs (renameVars' old new)

renameVars' :: Name -> Name -> Expr -> Expr
renameVars' old new (Var i) = Var (renameExprId old new i)
renameVars' old new (Lam u i e) = Lam u (renameExprId old new i) e
renameVars' old new (Let b e) = Let (map (\(b', e') -> (renameExprId old new b', e')) b) e
renameVars' old new (Case e i t a) = Case e (renameExprId old new i) t $ map (renameExprAltIds old new) a
renameVars' old new (Assert is e e') = Assert (fmap (rename old new) is) e e'
renameVars' _ _ e = e


renameExprId :: Name -> Name -> Id -> Id
renameExprId old new (Id n t) = Id (rename old new n) t

renameExprDataCon :: Name -> Name -> DataCon -> DataCon
renameExprDataCon old new (DataCon n t u e) = DataCon (rename old new n) t u e

renameExprAlt :: Name -> Name -> Alt -> Alt
renameExprAlt old new (Alt (DataAlt dc is) e) =
    let
        dc' = renameExprDataCon old new dc
        is' = map (renameExprId old new) is
    in
    Alt (DataAlt dc' is') e
renameExprAlt _ _ a = a

renameExprAltIds :: Name -> Name -> Alt -> Alt
renameExprAltIds old new (Alt (DataAlt dc is) e) =
    let
        is' = map (renameExprId old new) is
    in
    Alt (DataAlt dc is') e
renameExprAltIds _ _ a = a

renamesExprs :: ASTContainer m Expr => HM.HashMap Name Name -> m -> m
renamesExprs hm = modifyASTs (renamesExprs' hm)

renamesExprs' :: HM.HashMap Name Name -> Expr -> Expr
renamesExprs' hm (Var i) = Var (renamesExprId hm i)
renamesExprs' hm (Prim (MutVar mv) t) = (Prim (MutVar $ renames hm mv) t)
renamesExprs' hm (Data d) = Data (renamesExprDataCon hm d)
renamesExprs' hm (Lam u i e) = Lam u (renamesExprId hm i) e
renamesExprs' hm (Let b e) = Let (map (\(b', e') -> (renamesExprId hm b', e')) b) e
renamesExprs' hm (Case e i t a) = Case e (renamesExprId hm i) t $ map (renamesExprAlt hm) a
renamesExprs' hm (Assume is e e') = Assume (fmap (renames hm) is) e e'
renamesExprs' hm (Assert is e e') = Assert (fmap (renames hm) is) e e'
renamesExprs' _ e = e

renamesExprId :: HM.HashMap Name Name -> Id -> Id
renamesExprId hm (Id n t) = Id (renames hm n) t

renamesExprDataCon :: HM.HashMap Name Name -> DataCon -> DataCon
renamesExprDataCon hm (DataCon n t u e) = DataCon (renames hm n) t u e

renamesExprAlt :: HM.HashMap Name Name -> Alt -> Alt
renamesExprAlt hm (Alt (DataAlt dc is) e) =
    let
        dc' = renamesExprDataCon hm dc
        is' = map (renamesExprId hm) is
    in
    Alt (DataAlt dc' is') e
renamesExprAlt _ a = a

instance Named Type where
    names = eval go
        where
            go (TyVar i) = idNamesInType i
            go (TyCon n _) = S.singleton n
            go (TyForAll b _) = idNamesInType b
            go _ = S.empty

    rename old new = modify go
      where
        go :: Type -> Type
        go (TyVar i) = TyVar (renameIdInType old new i)
        go (TyCon n ts) = TyCon (rename old new n) ts
        go (TyForAll tb t) = TyForAll (renameIdInType old new tb) t
        go t = t

    renames hm = modify go
      where
        go :: Type -> Type
        go (TyVar i) = TyVar (renamesIdInType hm i)
        go (TyCon n ts) = TyCon (renames hm n) ts
        go (TyForAll tb t) = TyForAll (renamesIdInType hm tb) t
        go t = t

-- We don't want both modify and go to recurse on the Type's in Ids
-- so we introduce functions to collect or rename only the Names directly in those types
idNamesInType :: Id -> S.Seq Name
idNamesInType (Id n _) = S.singleton n

renameIdInType :: Name -> Name -> Id -> Id
renameIdInType old new (Id n t) = Id (rename old new n) t

renamesIdInType :: HM.HashMap Name Name -> Id -> Id
renamesIdInType hm (Id n t) = Id (renames hm n) t

instance Named Alt where
    {-# INLINE names #-}
    names (Alt am e) = names am <> names e

    {-# INLINE rename #-}
    rename old new (Alt am e) = Alt (rename old new am) (rename old new e)

    {-# INLINE renames #-}
    renames hm (Alt am e) = Alt (renames hm am) (renames hm e)

instance Named DataCon where
    {-# INLINE names #-}
    names (DataCon n t u e) = n S.<| names t S.>< names u S.>< names e

    {-# INLINE rename #-}
    rename old new (DataCon n t u e) =
        DataCon (rename old new n) (rename old new t) (rename old new u) (rename old new e)

    {-# INLINE renames #-}
    renames hm (DataCon n t u e) =
        DataCon (renames hm n) (renames hm t) (renames hm u) (renames hm e)

instance Named AltMatch where
    {-# INLINE names #-}
    names (DataAlt dc i) = names dc <> names i
    names _ = S.empty

    {-# INLINE rename #-}
    rename old new (DataAlt dc i) =
        DataAlt (rename old new dc) (rename old new i)
    rename _ _ am = am

    {-# INLINE renames #-}
    renames hm (DataAlt dc i) =
        DataAlt (renames hm dc) (renames hm i)
    renames _ am = am

instance Named Coercion where
    names (t1 :~ t2) = names t1 <> names t2
    rename old new (t1 :~ t2) = rename old new t1 :~ rename old new t2
    renames hm (t1 :~ t2) = renames hm t1 :~ renames hm t2

instance Named Tickish where
    names (Breakpoint _) = S.empty
    names (HpcTick _ _) = S.empty
    names (NamedLoc n) = S.singleton n

    rename _ _ bp@(Breakpoint _) = bp
    rename _ _ hpc@(HpcTick _ _) = hpc
    rename old new (NamedLoc n) = NamedLoc $ rename old new n

    renames _ bp@(Breakpoint _) = bp
    renames _ hpc@(HpcTick _ _) = hpc
    renames hm (NamedLoc n) = NamedLoc $ renames hm n

instance Named Primitive where
    names (MutVar n) = S.singleton n
    names _ = S.empty

    rename old new (MutVar n) = MutVar (rename old new n)
    rename _ _ p = p

    renames m (MutVar n) = MutVar (renames m n)
    renames _ p = p

instance Named RewriteRule where
    names (RewriteRule { ru_head = h
                       , ru_rough = rs
                       , ru_bndrs = b
                       , ru_args = as
                       , ru_rhs = rhs}) =
        h S.<| names rs <> names b <> names as <> names rhs

    rename old new (RewriteRule { ru_name = n
                                , ru_module = mdl
                                , ru_head = h
                                , ru_rough = rs
                                , ru_bndrs = b
                                , ru_args = as
                                , ru_rhs = rhs}) =
        RewriteRule { ru_name = n
                    , ru_module = mdl
                    , ru_head = rename old new h
                    , ru_rough = rename old new rs
                    , ru_bndrs = rename old new b
                    , ru_args = rename old new as
                    , ru_rhs = rename old new rhs}

    renames hm (RewriteRule { ru_name = n
                            , ru_module = mdl
                            , ru_head = h
                            , ru_rough = rs
                            , ru_bndrs = b
                            , ru_args = as
                            , ru_rhs = rhs}) =
        RewriteRule { ru_name = n
                    , ru_module = mdl
                    , ru_head = renames hm h
                    , ru_rough = renames hm rs
                    , ru_bndrs = renames hm b
                    , ru_args = renames hm as
                    , ru_rhs = renames hm rhs}

instance Named FuncCall where
    names (FuncCall {funcName = n, arguments = as, returns = r}) = n S.<| names as <> names r
    rename old new (FuncCall {funcName = n, arguments = as, returns = r}) = 
        FuncCall {funcName = rename old new n, arguments = rename old new as, returns = rename old new r}
    renames hm (FuncCall {funcName = n, arguments = as, returns = r} ) =
        FuncCall {funcName = renames hm n, arguments = renames hm as, returns = renames hm r}


instance Named AlgDataTy where
    names (DataTyCon ns dc _) = names ns <> names dc
    names (NewTyCon ns dc rt _) = names ns <> names dc <> names rt
    names (TypeSynonym is st _) = names is <> names st

    rename old new (DataTyCon n dc adts) = DataTyCon (rename old new n) (rename old new dc) adts
    rename old new (NewTyCon n dc rt adts) = NewTyCon (rename old new n) (rename old new dc) (rename old new rt) adts
    rename old new (TypeSynonym is st adts) = (TypeSynonym (rename old new is) (rename old new st) adts)

    renames hm (DataTyCon n dc adts) = DataTyCon (renames hm n) (renames hm dc) adts
    renames hm (NewTyCon n dc rt adts) = NewTyCon (renames hm n) (renames hm dc) (renames hm rt) adts
    renames hm (TypeSynonym is st adts) = TypeSynonym (renames hm is) (renames hm st) adts

instance Named KnownValues where
    names (KnownValues {
              dcInt = dI
            , dcFloat = dF
            , dcDouble = dD
            , dcInteger = dI2
            , dcChar = dcCh

            , tyInt = tI
            , tyFloat = tF
            , tyDouble = tD
            , tyInteger = tI2
            , tyChar = tCh

            , tyBool = tB
            , dcTrue = dcT
            , dcFalse = dcF

            , tyRational = tR

            , tyList = tList
            , dcCons = tCons
            , dcEmpty = tEmp

            , tyMaybe = tMaybe
            , dcJust = dJust
            , dcNothing = dNothing

            , tyUnit = tUnit
            , dcUnit = dUnit

            , tyMutVar = tMV
            , dcMutVar = dMV
            , tyState = tSt
            , dcState = dSt
            , tyRealWorld = tRW
            , dcRealWorld = dRW

            , eqTC = eqT
            , numTC = numT
            , ordTC = ordT
            , integralTC = integralT
            , realTC = realT
            , fractionalTC = fractionalT

            , integralExtactReal = integralEReal
            , realExtractNum = realENum
            , realExtractOrd = realEOrd
            , ordExtractEq = ordEEq

            , eqFunc = eqF
            , neqFunc = neqF

            , plusFunc = plF
            , minusFunc = minusF
            , timesFunc = tmsF
            , divFunc = divF
            , negateFunc = negF
            , modFunc = modF

            , fromIntegerFunc = fromIntegerF
            , toIntegerFunc = toIntegerF

            , toRatioFunc = toRatioF
            , fromRationalFunc = fromRationalF

            , geFunc = geF
            , gtFunc = gtF
            , ltFunc = ltF
            , leFunc = leF

            , impliesFunc = impF
            , iffFunc = iffF

            , andFunc = andF
            , orFunc = orF
            , notFunc = notF

            , errorFunc = errF
            , errorEmptyListFunc = errEmpListF
            , errorWithoutStackTraceFunc = errWOST
            , patErrorFunc = patE
            }) =
            S.fromList
                [dI, dF, dD, dI2, dcCh, tI, tI2, tF, tD, tCh, tB, dcT, dcF, tR
                , tList, tCons, tEmp
                , tMaybe, dJust, dNothing
                , tUnit, dUnit
                , tMV, dMV, tSt, dSt, tRW, dRW
                , eqT, numT, ordT, integralT, realT, fractionalT
                , integralEReal, realENum, realEOrd, ordEEq
                , eqF, neqF, plF, minusF, tmsF, divF, negF, modF
                , fromIntegerF, toIntegerF
                , toRatioF, fromRationalF
                , geF, gtF, ltF, leF
                , impF, iffF
                , andF, orF, notF
                , errF, errEmpListF, errWOST, patE]

    rename old new (KnownValues {
                     dcCoercion = dcC
                   , dcInt = dI
                   , dcFloat = dF
                   , dcDouble = dD
                   , dcInteger = dI2
                   , dcChar = dcCh
                    
                   , tyCoercion = tyC 
                   , tyInt = tI
                   , tyFloat = tF
                   , tyDouble = tD
                   , tyInteger = tI2
                   , tyChar = tCh

                   , tyBool = tB
                   , dcTrue = dcT
                   , dcFalse = dcF

                   , tyRational = tR

                   , tyList = tList
                   , dcCons = tCons
                   , dcEmpty = tEmp

                   , tyMaybe = tMaybe
                   , dcJust = dJust
                   , dcNothing = dNothing

                   , tyUnit = tUnit
                   , dcUnit = dUnit

                   , tyMutVar = tMV
                   , dcMutVar = dMV
                   , tyState = tSt
                   , dcState = dSt
                   , tyRealWorld = tRW
                   , dcRealWorld = dRW

                   , eqTC = eqT
                   , numTC = numT
                   , ordTC = ordT
                   , integralTC = integralT
                   , realTC = realT
                   , fractionalTC = fractionalT

                   , integralExtactReal = integralEReal
                   , realExtractNum = realENum
                   , realExtractOrd = realEOrd
                   , ordExtractEq = ordEEq

                   , eqFunc = eqF
                   , neqFunc = neqF

                   , plusFunc = plF
                   , minusFunc = minusF
                   , timesFunc = tmsF
                   , divFunc = divF
                   , negateFunc = negF
                   , modFunc = modF

                   , fromIntegerFunc = fromIntegerF
                   , toIntegerFunc = toIntegerF

                   , toRatioFunc = toRatioF
                   , fromRationalFunc = fromRationalF

                   , geFunc = geF
                   , gtFunc = gtF
                   , ltFunc = ltF
                   , leFunc = leF

                   , impliesFunc = impF
                   , iffFunc = iffF

                   , andFunc = andF
                   , orFunc = orF
                   , notFunc = notF

                   , errorFunc = errF
                   , errorEmptyListFunc = errEmpListF
                   , errorWithoutStackTraceFunc = errWOST
                   , patErrorFunc = patE
                   }) =
                    (KnownValues {
                          dcCoercion = rename old new dcC
                        , dcInt = rename old new dI
                        , dcFloat = rename old new dF
                        , dcDouble = rename old new dD
                        , dcInteger = rename old new dI2
                        , dcChar = rename old new dcCh

                        , tyCoercion = rename old new tyC
                        , tyInt = rename old new tI
                        , tyFloat = rename old new tF
                        , tyDouble = rename old new tD
                        , tyInteger = rename old new tI2
                        , tyChar = rename old new tCh

                        , tyBool = rename old new tB
                        , dcTrue = rename old new dcT
                        , dcFalse = rename old new dcF

                        , tyRational = rename old new tR
                        
                        , tyList = rename old new tList
                        , dcCons = rename old new tCons
                        , dcEmpty = rename old new tEmp

                        , tyMaybe = rename old new tMaybe
                        , dcJust = rename old new dJust
                        , dcNothing = rename old new dNothing

                        , tyUnit = rename old new tUnit
                        , dcUnit = rename old new dUnit

                        , tyState = rename old new tSt
                        , dcState = rename old new dSt
                        , tyMutVar = rename old new tMV
                        , dcMutVar = rename old new dMV
                        , tyRealWorld = rename old new tRW
                        , dcRealWorld = rename old new dRW

                        , eqTC = rename old new eqT
                        , numTC = rename old new numT
                        , ordTC = rename old new ordT
                        , integralTC = rename old new integralT
                        , realTC = rename old new realT
                        , fractionalTC = rename old new fractionalT

                        , integralExtactReal = rename old new integralEReal
                        , realExtractNum = rename old new realENum
                        , realExtractOrd = rename old new realEOrd
                        , ordExtractEq = rename old new ordEEq

                        , eqFunc = rename old new eqF
                        , neqFunc = rename old new neqF

                        , plusFunc = rename old new plF
                        , minusFunc = rename old new minusF
                        , timesFunc = rename old new tmsF
                        , divFunc = rename old new divF
                        , negateFunc = rename old new negF
                        , modFunc = rename old new modF

                        , fromIntegerFunc = rename old new fromIntegerF
                        , toIntegerFunc = rename old new toIntegerF

                        , toRatioFunc = rename old new toRatioF
                        , fromRationalFunc = rename old new fromRationalF

                        , geFunc = rename old new geF
                        , gtFunc = rename old new gtF
                        , ltFunc = rename old new ltF
                        , leFunc = rename old new leF
          
                        , impliesFunc = rename old new impF
                        , iffFunc = rename old new iffF

                        , andFunc = rename old new andF
                        , orFunc = rename old new orF
                        , notFunc = rename old new notF

                        , errorFunc = rename old new errF
                        , errorEmptyListFunc = rename old new errEmpListF
                        , errorWithoutStackTraceFunc = rename old new errWOST
                        , patErrorFunc = rename old new patE
                        })

instance Named a => Named [a] where
    {-# INLINE names #-}
    names = foldMap names
    {-# INLINE rename #-}
    rename old new = fmap (rename old new)
    {-# INLINE renames #-}
    renames hm = fmap (renames hm)

instance Named a => Named (S.Seq a) where
    {-# INLINE names #-}
    names = foldMap names
    {-# INLINE rename #-}
    rename old new = fmap (rename old new)
    {-# INLINE renames #-}
    renames hm = fmap (renames hm)


instance Named a => Named (Maybe a) where
    {-# INLINE names #-}
    names = foldMap names
    {-# INLINE rename #-}
    rename old new = fmap (rename old new)
    {-# INLINE renames #-}
    renames hm = fmap (renames hm)

instance Named a => Named (M.Map k a) where
    {-# INLINE names #-}
    names = foldMap names
    {-# INLINE rename #-}
    rename old new = fmap (rename old new)
    {-# INLINE renames #-}
    renames hm = fmap (renames hm)

instance Named a => Named (HM.HashMap k a) where
    {-# INLINE names #-}
    names = foldMap names
    {-# INLINE rename #-}
    rename old new = fmap (rename old new)
    {-# INLINE renames #-}
    renames hm = fmap (renames hm)

instance Named () where
    {-# INLINE names #-}
    names _ = S.empty
    {-# INLINE rename #-}
    rename _ _ = id
    {-# INLINE renames #-}
    renames _ = id

instance (Named s, Hashable s, Eq s) => Named (HS.HashSet s) where
    {-# INLINE names #-}
    names = names . HS.toList
    {-# INLINE rename #-}
    rename old new = HS.map (rename old new)
    {-# INLINE renames #-}
    renames hm = HS.map (renames hm)

instance (Named a, Named b) => Named (a, b) where
    names (a, b) = names a <> names b
    rename old new (a, b) = (rename old new a, rename old new b)
    renames hm (a, b) = (renames hm a, renames hm b)

instance (Named a, Named b, Named c) => Named (a, b, c) where
    names (a, b, c) = names a <> names b <> names c
    rename old new (a, b, c) = (rename old new a, rename old new b, rename old new c)
    renames hm (a, b, c) = (renames hm a, renames hm b, renames hm c)

instance (Named a, Named b, Named c, Named d) => Named (a, b, c, d) where
    names (a, b, c, d) = names a <> names b <> names c <> names d
    rename old new (a, b, c, d) = (rename old new a, rename old new b, rename old new c, rename old new d)
    renames hm (a, b, c, d) = (renames hm a, renames hm b, renames hm c, renames hm d)

instance (Named a, Named b, Named c, Named d, Named e) => Named (a, b, c, d, e) where
    names (a, b, c, d, e) = names a <> names b <> names c <> names d <> names e
    rename old new (a, b, c, d, e) = (rename old new a, rename old new b, rename old new c, rename old new d, rename old new e)
    renames hm (a, b, c, d, e) = (renames hm a, renames hm b, renames hm c, renames hm d, renames hm e)

instance Named Bool where
    {-# INLINE names #-}
    names _ = S.empty
    {-# INLINE rename #-}
    rename _ _ = id

instance Named Int where
    {-# INLINE names #-}
    names _ = S.empty
    {-# INLINE rename #-}
    rename _ _ = id

instance Named Integer where
    {-# INLINE names #-}
    names _ = S.empty
    {-# INLINE rename #-}
    rename _ _ = id

instance Named T.Text where
    {-# INLINE names #-}
    names _ = S.empty
    {-# INLINE rename #-}
    rename _ _ = id

instance (Named k, Named v, Eq k, Hashable k) => Named (UF.UFMap k v) where
    names = names . UF.toList
    rename old new = UF.fromList . rename old new . UF.toList
    renames hm = UF.fromList . renames hm . UF.toList


freshSeededString :: T.Text -> NameGen -> (Name, NameGen)
freshSeededString t = freshSeededName (Name t Nothing 0 Nothing)

freshSeededStrings :: [T.Text] -> NameGen -> ([Name], NameGen)
freshSeededStrings t = freshSeededNames (map (\t' -> Name t' Nothing 0 Nothing) t)

freshSeededName :: Name -> NameGen -> (Name, NameGen)
freshSeededName (Name n m _ l) (NameGen hm) =
    (Name n m i' l, NameGen hm')
    where 
        i' = HM.lookupDefault 0 (n, m) hm
        hm' = HM.insert (n, m) (i' + 1) hm

freshSeededNames :: [Name] -> NameGen -> ([Name], NameGen)
freshSeededNames ns ng = swap $ mapAccumR (\ng' n -> swap $ freshSeededName n ng') ng ns

freshName :: NameGen -> (Name, NameGen)
freshName ngen = freshSeededName seed ngen
  where
    seed = Name "fs" Nothing 0 Nothing

freshNames :: Int -> NameGen -> ([Name], NameGen)
freshNames i ngen = freshSeededNames (replicate i (Name "fs" Nothing 0 Nothing)) ngen

freshId :: Type -> NameGen -> (Id, NameGen)
freshId = freshSeededId (Name "fs" Nothing 0 Nothing)

freshIds :: [Type] -> NameGen -> ([Id], NameGen)
freshIds ts ngen = 
    let
        (ns, ngen') = freshNames (length ts) ngen
    in
    (map (uncurry Id) (zip ns ts), ngen')
    
freshSeededId :: Named a => a -> Type -> NameGen -> (Id, NameGen)
freshSeededId x t ngen =
    let
        (n, ngen') = case S.viewl (names x) of
                            S.EmptyL -> error "freshSeededId: no names available"
                            x' S.:< _ -> freshSeededName x' ngen
    in
    (Id n t, ngen')

freshVar :: Type -> NameGen -> (Expr, NameGen)
freshVar t ngen =
    let
        (i, ngen') = freshId t ngen
    in
    (Var i, ngen')

-- | Allows mapping, while passing a NameGen along
mapNG :: (a -> NameGen -> (b, NameGen)) -> [a] -> NameGen -> ([b], NameGen)
mapNG f xs ng = swap $ mapAccumR (\xs' ng' -> swap $ f ng' xs') ng xs
{-# INLINE mapNG #-}
