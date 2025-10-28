{-# LANGUAGE OverloadedStrings, TupleSections #-}

-- | `Arbitrary` typeclasses, to write QuickCheck tests involving types from "G2.Language.Syntax" and "G2.Language.Support".

module G2.Language.Arbitrary ( StateBindingsPair (..)
                             , ArbSet (..)
                             , ArbTypeEnv (..)
                             , ArbUpperName (..)
                             , ArbName (..)
                             , ArbExpr (..)
                             , ArbType (..)
                             
                             , prettyArbSet

                             , arbExpr
                             , arbType
                             
                             , nameCall) where

import G2.Config
import qualified G2.Initialization.Types as IT
import G2.Interface
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues as KV
import G2.Lib.Printers

import Control.Monad
import Data.Bifunctor
import Data.Foldable
import Data.Function
import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import qualified Data.Text as T
import Test.Tasty.QuickCheck
import qualified G2.Language.TyVarEnv as TV 

data StateBindingsPair t = SB { sb_state :: State t, sb_bindings :: Bindings }

instance Show (StateBindingsPair t) where
    show (SB s _) =
        let
            pg = mkPrettyGuide (expr_env s, type_env s, curr_expr s)

            eenv_str = prettyEEnv (tyvar_env s) pg (curr_expr s) (exec_stack s) (expr_env s)
            tenv_str = prettyTypeEnv (tyvar_env s) pg (type_env s)
            e_str = printHaskellDirtyPG pg (getExpr s)
        in
        T.unpack $ "ExprEnv\n" <> eenv_str <> "\nTypeEnv\n" <> tenv_str <> "\nExpr\n" <> e_str

data ArbSimpleState = ArbSimple IT.SimpleState

instance Arbitrary t => Arbitrary (StateBindingsPair t) where
    arbitrary = do
        ArbSimple simple_s <- arbitrary
        let (s, b) = initStateFromSimpleState' simple_s "call" [Nothing] (mkConfigDirect "" [] M.empty)
        t <- arbitrary
        let s' = s { track = t }
        return $ SB s' b
    
    shrink (SB s b) =
        let
            eenvs = shrinkExprEnv (expr_env s)
        in
        map (\eenv -> SB (s { expr_env = eenv}) b) eenvs


shrinkExprEnv :: ExprEnv -> [ExprEnv]
shrinkExprEnv eenv =
    let
        ks = E.keys eenv
    in
    concatMap (\k -> case E.lookupConcOrSym k eenv of
                            Just (E.Conc e) -> map (\(AE e') -> E.insert k e' eenv) $ shrink (AE e)
                            _ -> []) ks

instance Arbitrary ArbSimpleState where
    arbitrary = do
        ArbSet { arb_type_env = tenv, arb_expr = e } <- arbitrary
        let simple_s = IT.SimpleState { IT.expr_env = E.singleton nameCall e
                                      , IT.type_env = tenv
                                      , IT.name_gen = mkNameGen (tenv, e)
                                      , IT.known_values = fakeKnownValues
                                      , IT.type_classes = initTypeClasses TV.empty []
                                      , IT.families = HM.empty
                                      , IT.rewrite_rules = []
                                      , IT.exports = []
                                      , IT.handles = HM.empty
                                      }
        return $ ArbSimple simple_s

nameCall :: Name
nameCall = Name "call" Nothing 0 ProvOther

data ArbSet = ArbSet { arb_type_env :: TypeEnv
                     , arb_expr :: Expr }
                     deriving Show

instance Arbitrary ArbSet where
    arbitrary = do
        ATE tenv <- arbitrary
        t <- arbFunType tenv
        let t' = case returnType t of
                        TyCon n _ | Just (DataTyCon {data_cons = dc }) <- HM.lookup n tenv
                                  , any isTyFun $ concatMap (argumentTypes . typeOf TV.empty) dc -> addTyLitInt t
                        _ -> t
        e <- arbExpr tenv t'
        return $ ArbSet { arb_type_env = tenv, arb_expr = e }
        where
            addTyLitInt (TyFun t t') = TyFun t $ addTyLitInt t'
            addTyLitInt t = TyFun t TyLitInt
    
    shrink (ArbSet { arb_type_env = tenv, arb_expr = e }) =
        map (\(AE e') -> ArbSet { arb_type_env = tenv, arb_expr = e'}) (shrink $ AE e)

instance Named ArbSet where
    names as = names (arb_type_env as) <> names (arb_expr as)
    rename old new as =
        ArbSet { arb_type_env = rename old new (arb_type_env as)
               , arb_expr = rename old new (arb_expr as)
               }

prettyArbSet :: ArbSet -> String
prettyArbSet as =
    let
        pg = mkPrettyGuide as

        tenv_str = prettyTypeEnv TV.empty pg (arb_type_env as)
        e_str = printHaskellDirtyPG pg (arb_expr as)
    in
    T.unpack $ "TypeEnv\n" <> tenv_str <> "\nExpr\n" <> e_str

newtype ArbTypeEnv = ATE { unATE :: TypeEnv} deriving Show
newtype ArbAlgDataTy = AADT { unAADT :: AlgDataTy} deriving Show

instance Arbitrary ArbTypeEnv where
    arbitrary = do
        tenv_size <- chooseInt (0, 10)
        tenv <- vectorOf tenv_size arbAlgDataTyEmpty
        tenv' <- zipWithM (arbInstDataCons HM.empty) [0..] tenv 
        return . ATE . HM.union basicTypeEnv . HM.fromList $ tenv' 

-- | A `TypeEnv` with `Int` and `Float` datatypes.
basicTypeEnv :: TypeEnv
basicTypeEnv =
    let
        int_dc = DataCon intDCName (TyFun TyLitInt (TyCon intTypeName TYPE)) [] []
        float_dc = DataCon floatDCName (TyFun TyLitFloat (TyCon floatTypeName TYPE)) [] []
    in
    HM.fromList [ (intTypeName, DataTyCon { bound_ids = [], data_cons = [int_dc], adt_source = ADTSourceCode })
                , (floatTypeName, DataTyCon { bound_ids = [], data_cons = [float_dc], adt_source = ADTSourceCode }) ]

-- | Creates `Name` and `AlgDataTy` mappings, with all `data_cons` fields set to the empty list.
-- The `arbInstDataCons` function can then be used to instantiate the `data_cons` fields.
-- This structure allows generating datatypes that are nested, recursive, or mutually recursive.
arbAlgDataTyEmpty :: Gen (Name, AlgDataTy)
arbAlgDataTyEmpty = do
    AU ty_n <- arbitrary
    return (ty_n, DataTyCon { bound_ids = [], data_cons = [], adt_source = ADTG2Generated })

arbInstDataCons :: TypeEnv -> Unique -> (Name, AlgDataTy) -> Gen (Name, AlgDataTy)
arbInstDataCons tenv unq (ty_n, adt@(DataTyCon { bound_ids = bi })) = do
    dc_c <- chooseInt (1, 10)
    dcs <- map (\(DataCon n t u e) -> DataCon n (foldr TyForAll t bi) u e) <$> vectorOf dc_c (arbDataCon tenv unq (TyCon ty_n TYPE))
    let dcs' = nubBy (\(DataCon n _ _ _) (DataCon n' _ _ _) -> n == n') dcs
    return (ty_n, adt { data_cons = dcs' })
arbInstDataCons _ _ _ = error "arbInstDataCons: Unsupported AlgDataTy"

arbDataCon :: TypeEnv -> Unique -> Type -> Gen DataCon
arbDataCon tenv unq ret_ty = do
    n <- chooseEnum ('A', 'Z')
    ar_c <- chooseInt (0, 5)
    ar_ty <- vectorOf ar_c (sized $ \k -> arbType tenv (k `div` ar_c))
    return $ DataCon (Name (T.singleton n) Nothing unq ProvOther) (mkTyFun $ ar_ty ++ [ret_ty]) [] []

newtype ArbExpr = AE { unAE :: Expr} deriving Show
newtype ArbType = AT { unAT :: Type} deriving Show

-- | Via `arbitrary`, allows generating type and data constructor `Name`s (with an uppercase first letter.)
newtype ArbUpperName = AU { unAU :: Name} deriving Show

-- | Via `arbitrary`, allows generating function and variable `Name`s (with a lowercase first letter.)
newtype ArbName = AN { unAN :: Name} deriving Show

-- | Via `arbitrary`, allows generating function and variable `Id`s (with a lowercase first letter.)
newtype ArbId = AI { unAI :: Id} deriving Show

instance Arbitrary ArbExpr where
    arbitrary = AE <$> (arbExpr HM.empty =<< arbType HM.empty 1)

    shrink (AE e) = map AE (shrinkExpr e)

instance Arbitrary ArbType where
    arbitrary = fmap AT $ sized (arbType HM.empty)

instance Arbitrary ArbUpperName where
    arbitrary = do
        n1 <- chooseEnum ('A', 'Z')
        n2 <- chooseEnum ('A', 'Z')
        let n = T.pack [n1, n2]
            n' = if n `elem` ["IO"] then n <> "'" else n
        return . AU $ Name n' Nothing 0 ProvOther

instance Arbitrary ArbName where
    arbitrary = do
        n1 <- chooseEnum ('a', 'z')
        n2 <- chooseEnum ('a', 'z')
        let n = T.pack [n1, n2]
            n' = if n `elem` ["do", "if", "in", "of"] then n <> "'" else n
        return . AN $ Name n' Nothing 0 ProvOther

instance Arbitrary ArbId where
    arbitrary = do
        AN n <- arbitrary
        t <- sized (arbType HM.empty)
        return $ AI (Id n t)

type TypeMap = HM.HashMap Name Type

-- | Generates an arbitrary `Expr` of a given `Type`.
arbExpr :: TypeEnv
        -> Type -- ^ A type @t@  
        -> Gen Expr -- ^ A generated expression @e@, satisfying @e :: t@
arbExpr tenv init_t = sized $ \k -> arbExpr' k HM.empty init_t
    where
        arbExpr' :: Int -> TypeMap -> Type -> Gen Expr
        arbExpr' k tm (TyFun t1 t2) = do
            AN nm <- arbitrary
            let tm' = HM.insert nm t1 tm
            fmap (Lam TermL (Id nm t1)) (arbExpr' k tm' t2)
        arbExpr' k tm t | k <= 0 = arbExprBase k tm t
                        | otherwise = oneof [arbExprApp k tm t, arbExprLet k tm t, arbExprCase k tm t, arbExprBase k tm t]

        arbExprBase :: Int -> TypeMap -> Type -> Gen Expr
        arbExprBase k tm t =
            let
                vrs = case typeMapToVars $ HM.filter (t ==) tm of
                            [] -> []
                            vs -> [(8, elements vs)]
                vals = case t of
                        TyLitInt -> [(2, Lit . LitInt <$> arbitrary)]
                        TyLitFloat -> [(2, Lit . LitFloat <$> arbitrary)]
                        TyCon n _ | Just adt <- HM.lookup n tenv ->
                            map (\dc -> (2, arbWrap k tm $ Data dc)) (data_cons adt)
                        _ -> []
            in
            frequency (vrs ++ vals) 

        -- Apply arbitrary arguments to eliminate all function arrows
        arbWrap :: Int -> TypeMap -> Expr -> Gen Expr
        arbWrap k tm e = do
            let ts = anonArgumentTypes $ typeOf TV.empty e
            es <- mapM (arbExpr' (k `div` length ts) tm) ts
            return $ mkApp (e:es)

        arbExprApp :: Int -> TypeMap -> Type -> Gen Expr
        arbExprApp k tm ret_t = do
            ar_t <- arbType tenv (k - 1)
            liftM2 App
                (arbExpr' (k `div` 2) tm (TyFun ar_t  ret_t))
                (arbExpr' (k `div` 2) tm ar_t)

        arbExprLet :: Int -> TypeMap -> Type -> Gen Expr
        arbExprLet k tm ret_t = do
            bnd_c <- chooseInt (1, 10)
            bnd_is <- map unAI <$> vectorOf bnd_c arbitrary
            let bnd_is' = nubBy ((==) `on` idName) bnd_is
            let tm' = foldr HM.delete tm $ map idName bnd_is'
            bnd_is_es <- mapM (\i@(Id _ t) -> (i,) <$> arbExpr' (k `div` bnd_c) tm' t) bnd_is'
            let tm'' = foldr (\(Id n t) -> HM.insert n t) tm' bnd_is'
            e <- arbExpr' (k `div` bnd_c) tm'' ret_t
            return $ Let bnd_is_es e
        
        arbExprCase :: Int -> TypeMap -> Type -> Gen Expr
        arbExprCase k tm t = do
            scrut_t <- arbDCType tenv
            scrut_e <- arbExpr' (k - 1) tm scrut_t
            AN bindee_n <- arbitrary
            let tm' = HM.insert bindee_n scrut_t tm
            alts <- arbAlts k tm' scrut_t t
            return (Case scrut_e (Id bindee_n scrut_t) t alts)
        
        arbAlts :: Int
                -> TypeMap
                -> Type -- ^ Scrutinee type
                -> Type -- ^ Return type
                -> Gen [Alt]
        arbAlts k tm (TyCon n _) t | Just (DataTyCon { data_cons = dcs }) <- HM.lookup n tenv = do
            mapM (arbAltDC (k `div` length dcs) tm t) dcs 
        arbAlts k tm _ t = do
            e <- arbExpr' (k - 1) tm t
            return [Alt Default e]

        arbAltDC :: Int -> TypeMap -> Type -> DataCon -> Gen Alt
        arbAltDC k tm t dc = do
            AN (Name p _ _ _) <- arbitrary
            let ts = anonArgumentTypes $ typeOf TV.empty dc
                ps = map (\i -> Name p Nothing i ProvOther) [1..fromIntegral (length ts)]
                is = zipWith Id ps ts
                tm' = foldl' (\tm_ (p_, t_) -> HM.insert p_ t_ tm_) tm $ zip ps ts
            e <- arbExpr' k tm' t
            return (Alt (DataAlt dc is) e) 

typeMapToVars :: TypeMap -> [Expr]
typeMapToVars = map (\(n, t') -> Var (Id n t')) . HM.toList

arbFunType :: TypeEnv -> Gen Type
arbFunType tenv = sized $ \n -> liftM2 TyFun (arbType tenv $ n `div` 2) (arbType tenv $ n `div` 2)

-- Generates an arbitrary `Type`.
arbType :: TypeEnv -> Int -> Gen Type
arbType tenv n | n <= 0 = arbNonFunType tenv
               | otherwise = oneof [ arbNonFunType tenv
                                   , liftM2 TyFun (arbType tenv $ n `div` 2) (arbType tenv $ n `div` 2)]

arbNonFunType :: TypeEnv -> Gen Type
arbNonFunType tenv = elements $ [TyLitInt, TyLitFloat] ++ map (flip TyCon TYPE) (HM.keys tenv)

arbDCType :: TypeEnv -> Gen Type
arbDCType tenv = elements $ map (flip TyCon TYPE) (HM.keys tenv)

shrinkExpr :: Expr -> [Expr]
shrinkExpr (Case e i t alts) =
    let
        opt1 = case alts of
                Alt (DataAlt _ _) _:Alt (DataAlt _ _) _:_ ->
                    map (\a@(Alt am _) -> Case e i t (a:if am == Default then [] else [errorAlt t])) alts
                _ -> []
        opt2 = [Case e' i t alts' | (AE e', alts') <- liftShrink2 shrink shrinkAlts (AE e, alts)]
        opt3 = map altExpr $ filter (varsNotUsed (idName i)) alts
    in
    opt1 ++ opt2 ++ opt3

shrinkExpr (Lam u i e) = map (Lam u i . unAE) (shrink $ AE e)

shrinkExpr (App e1 e2) =
    let
        lam_elim = case e1 of
                        Lam _ i e1' | idName i `notElem` names e1' -> [e1']
                                    | e1' == Var i -> [e2]
                        _ -> []
    in
    lam_elim ++ [ App e1' e2' | (AE e1', AE e2') <- shrink (AE e1, AE e2) ]

shrinkExpr (Lit (LitInt x)) = [Lit (LitInt x') | x' <- shrink x]
shrinkExpr (Lit (LitFloat x)) = [Lit (LitFloat x') | x' <- shrink x]

shrinkExpr (Var i) | typeOf TV.empty i == TyLitInt = [Lit (LitInt 0)]
                   | typeOf TV.empty i == TyLitFloat = [Lit (LitFloat 0)]

shrinkExpr (Let [] e) = [e] ++ [Let [] e' | AE e' <- shrink (AE e)]
shrinkExpr (Let es e) = [Let es e' | AE e' <- shrink (AE e)]
                     ++ [Let es' e | es' <- removeUnused (map idName $ freeVars E.empty e) es]
                     ++ [Let (map (bimap unAI unAE) es') e | es' <- shrinkElem (map (bimap AI AE) es)]

shrinkExpr _ = []

shrinkElem :: Arbitrary a => [a] -> [[a]]
shrinkElem [] = []
shrinkElem (x:xs) = [x':xs | x' <- shrink x] ++ map (x:) (shrink xs)

removeUnused :: [Name] -> [(Id, Expr)] -> [[(Id, Expr)]]
removeUnused _ [] = []
removeUnused ns (ie@(Id n _, _):es) =
    if n `notElem` ns then es:map (ie:) (removeUnused ns es) else  map (ie:) (removeUnused ns es)

shrinkAlts :: [Alt] -> [[Alt]]
shrinkAlts [] = []
shrinkAlts (Alt am a:as) = [Alt am a':as | AE a' <- shrink (AE a)] ++ map (Alt am a:) (shrinkAlts as)

varsNotUsed :: Name -> Alt -> Bool
varsNotUsed scrut_n (Alt (DataAlt _ ps) e) = let ns = map idName ps in all (\n -> n `notElem` names e) (scrut_n:ns)
varsNotUsed scrut_n (Alt (LitAlt _) e) = scrut_n `notElem` names e 
varsNotUsed scrut_n (Alt Default e) = scrut_n `notElem` names e 

errorAlt :: Type -> Alt
errorAlt = Alt Default . Prim Undefined

fakeKnownValues :: KnownValues
fakeKnownValues =
    KnownValues {
      KV.tyCoercion = Name "" Nothing 0 ProvOther
    , dcCoercion = Name "" Nothing 0 ProvOther
    , KV.tyInt = intTypeName
    , dcInt = intDCName
    , KV.tyFloat = floatTypeName
    , dcFloat = floatDCName
    , KV.tyDouble = Name "" Nothing 0 ProvOther
    , dcDouble = Name "" Nothing 0 ProvOther
    , KV.tyInteger = Name "" Nothing 0 ProvOther
    , dcInteger = Name "" Nothing 0 ProvOther
    , KV.tyChar  = Name "" Nothing 0 ProvOther
    , dcChar = Name "" Nothing 0 ProvOther
    , KV.tyBool = Name "" Nothing 0 ProvOther
    , dcTrue = Name "" Nothing 0 ProvOther
    , dcFalse = Name "" Nothing 0 ProvOther
    , KV.tyRational = Name "" Nothing 0 ProvOther
    , KV.tyList = Name "" Nothing 0 ProvOther
    , dcCons = Name "" Nothing 0 ProvOther
    , dcEmpty = Name "" Nothing 0 ProvOther
    , KV.tyMaybe = Name "" Nothing 0 ProvOther
    , dcJust = Name "" Nothing 0 ProvOther
    , dcNothing = Name "" Nothing 0 ProvOther
    , KV.tyUnit = Name "" Nothing 0 ProvOther
    , dcUnit = Name "" Nothing 0 ProvOther
    , KV.tyPrimTuple = Name "" Nothing 0 ProvOther
    , dcPrimTuple = Name "" Nothing 0 ProvOther
    , tyMutVar = Name "" Nothing 0 ProvOther
    , dcMutVar = Name "" Nothing 0 ProvOther
    , tyState = Name "" Nothing 0 ProvOther
    , dcState = Name "" Nothing 0 ProvOther
    , tyRealWorld = Name "" Nothing 0 ProvOther
    , dcRealWorld = Name "" Nothing 0 ProvOther
    , tyHandle = Name "" Nothing 0 ProvOther
    , eqTC = Name "" Nothing 0 ProvOther
    , numTC = Name "" Nothing 0 ProvOther
    , ordTC = Name "" Nothing 0 ProvOther
    , integralTC = Name "" Nothing 0 ProvOther
    , realTC = Name "" Nothing 0 ProvOther
    , fractionalTC = Name "" Nothing 0 ProvOther
    , integralExtactReal = Name "" Nothing 0 ProvOther
    , realExtractNum = Name "" Nothing 0 ProvOther
    , realExtractOrd = Name "" Nothing 0 ProvOther
    , ordExtractEq = Name "" Nothing 0 ProvOther
    , eqFunc = Name "" Nothing 0 ProvOther
    , neqFunc = Name "" Nothing 0 ProvOther
    , plusFunc = Name "" Nothing 0 ProvOther
    , minusFunc = Name "" Nothing 0 ProvOther
    , KV.timesFunc = Name "" Nothing 0 ProvOther
    , divFunc = Name "" Nothing 0 ProvOther
    , negateFunc = Name "" Nothing 0 ProvOther
    , modFunc = Name "" Nothing 0 ProvOther
    , fromIntegerFunc = Name "" Nothing 0 ProvOther
    , toIntegerFunc = Name "" Nothing 0 ProvOther
    , toRatioFunc = Name "" Nothing 0 ProvOther
    , fromRationalFunc = Name "" Nothing 0 ProvOther

    , geFunc = Name "" Nothing 0 ProvOther
    , gtFunc = Name "" Nothing 0 ProvOther
    , ltFunc = Name "" Nothing 0 ProvOther
    , leFunc = Name "" Nothing 0 ProvOther

    , impliesFunc = Name "" Nothing 0 ProvOther
    , iffFunc = Name "" Nothing 0 ProvOther

    , andFunc = Name "" Nothing 0 ProvOther
    , orFunc = Name "" Nothing 0 ProvOther
    , notFunc = Name "" Nothing 0 ProvOther

    , typeIndex = Name "" Nothing 0 ProvOther
    , adjStr = Name "" Nothing 0 ProvOther
    , strQuantifiers = Name "" Nothing 0 ProvOther

    , errorFunc = Name "" Nothing 0 ProvOther
    , errorWithoutStackTraceFunc = Name "" Nothing 0 ProvOther
    , errorEmptyListFunc = Name "" Nothing 0 ProvOther
    , patErrorFunc = Name "" Nothing 0 ProvOther
    }

intDCName :: Name
intDCName = Name "I#" Nothing 0 ProvOther

intTypeName :: Name
intTypeName = Name "Int" Nothing 0 ProvOther

floatDCName :: Name
floatDCName = Name "F#" Nothing 0 ProvOther

floatTypeName :: Name
floatTypeName = Name "Float" Nothing 0 ProvOther