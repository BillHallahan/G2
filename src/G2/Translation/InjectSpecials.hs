{-# LANGUAGE BangPatterns, CPP, OverloadedStrings #-}

module G2.Translation.InjectSpecials
  ( specialTypes
  , specialTypeNames
  , specialConstructors
  ) where

import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T
import Data.Tuple.Extra

import G2.Config
import G2.Language
import qualified G2.Language.TyVarEnv as TV 

_MAX_TUPLE :: Int
_MAX_TUPLE = 62

specialTypes :: UseSMTDC -> HM.HashMap Name AlgDataTy
specialTypes use_smt_tuple = HM.fromList $ map (uncurry3 specialTypes') (specials use_smt_tuple) ++ mkPrimTuples _MAX_TUPLE

specialTypes' :: (Name, [Name]) -> [(Name, [Type])] -> Bool -> (Name, AlgDataTy)
specialTypes' (tn, ns) dcn to_s = 
    let
        dc = map (specialDC ns tn) dcn
    in
    (tn, DataTyCon {bound_ids = map (flip Id TYPE) ns, data_cons = dc, adt_source = ADTSourceCode, to_smt = to_s})

specialDC :: [Name] -> Name -> (Name, [Type]) -> DataCon
specialDC ns tn (dc_n, ts) = 
    let
        tv = map (TyVar . flip Id TYPE) ns

        t = foldr TyFun (mkFullAppedTyCon TV.empty tn tv TYPE) ts
        is = map (flip Id TYPE) ns
        t' = foldr TyForAll t is
    in
    DataCon { dc_name = dc_n, dc_type = t', dc_univ_tyvars = is, dc_exist_tyvars = [] }

specialTypeNames :: HM.HashMap (T.Text, Maybe T.Text) Name
specialTypeNames =
    -- We only care about the names, so not important whether we pass UseSMTDC or NoSMTDC
    HM.fromList . map (\nm@(Name n m _ _) -> ((n, m), nm)) $ HM.keys (specialTypes UseSMTDC)

specialConstructors :: HM.HashMap (T.Text, Maybe T.Text) Name
specialConstructors =
    -- GHC 9.4 on use different constructors than our base for Integers, so we add a special mapping
    -- for those constructor (via `integerConstructor` to adjust Names accordingly)
    HM.fromList $ integerConstructor:map (\(DataCon nm@(Name n m _ _) _ _ _)-> ((n, m), nm)) specialConstructors'

integerConstructor :: ((T.Text, Maybe T.Text), Name)
integerConstructor = (("IS", Just "GHC.Num.Integer"), Name "Z#" (Just "GHC.Num.Integer") 0 Nothing)

specialConstructors' :: [DataCon]
specialConstructors' =
    -- We only care about the constructors, so not important whether we pass UseSMTDC or NoSMTDC
    concatMap data_cons $ HM.elems (specialTypes UseSMTDC)

aName :: Name
aName = Name "a" Nothing 0 Nothing

aTyVar :: Type
aTyVar = TyVar (Id aName TYPE)

listTypeStr :: T.Text
#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
listTypeStr = "List"
#else
listTypeStr = "[]"
#endif

listName :: Name
listName = Name listTypeStr (Just "GHC.Types") 0 Nothing

specials :: UseSMTDC -> [((Name, [Name]), [(Name, [Type])], Bool)]
specials use_smt_tuples =
           [ (( Name listTypeStr (Just "GHC.Types") 0 Nothing, [aName])
              , [ (Name "[]" (Just "GHC.Types") 1 Nothing, [])
                , (Name ":" (Just "GHC.Types") 2 Nothing, [aTyVar, mkFullAppedTyCon TV.empty listName [aTyVar] TYPE])]
              , False
             )

           , ((Name "Bool" (Just "GHC.Types") 3 Nothing, [])
             , [ (Name "False" (Just "GHC.Types") 4 Nothing, [])
               , (Name "True" (Just "GHC.Types") 5 Nothing, [])]
             , False)
           ]
           ++
#if MIN_VERSION_GLASGOW_HASKELL(9,10,0,0)
           mkTuples 6 use_smt_tuples "(" ")" (Just "GHC.Tuple") _MAX_TUPLE
#elif MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
           mkTuples 6 use_smt_tuples "(" ")" (Just "GHC.Tuple.Prim") _MAX_TUPLE
#else
           mkTuples 6 use_smt_tuples "(" ")" (Just "GHC.Tuple") _MAX_TUPLE
#endif
           -- ++
           -- mkTuples "(#" "#)" (Just "GHC.Prim") _MAX_TUPLE


mkTuples :: Unique -> UseSMTDC -> T.Text -> T.Text -> Maybe T.Text -> Int -> [((Name, [Name]), [(Name, [Type])], Bool)]
mkTuples !unq use_smt_dc ls rs m n
                   | n < 0 = []
                   | otherwise =
                        let
                            cons_n = ls `T.append` T.pack (replicate n ',') `T.append` rs

#if MIN_VERSION_GLASGOW_HASKELL(9,8,0,0)
                            -- Need to add one here to avoid an off-by-one error between type name
                            -- and number of parentheses in constructor.
                            -- I.e. Tuple2 has the constructor (,)
                            ty_n = if n == 0 then "Unit" else "Tuple" <> T.pack (show (n + 1))
#else
                            ty_n = cons_n
#endif
                            ns = if n == 0 then [] else map (\i -> Name "a" m i Nothing) [0..fromIntegral n]
                            tv = map (TyVar . flip Id TYPE) ns
                        in
                        -- ((s, m, []), [(s, m, [])]) : mkTuples (n - 1)
                        ((Name ty_n m unq Nothing, ns), [(Name cons_n m (unq + 1) Nothing, tv)], use_smt_dc == UseSMTDC) : mkTuples (unq + 2) use_smt_dc ls rs m (n - 1)

mkPrimTuples :: Int -> [(Name, AlgDataTy)]
mkPrimTuples k =
    let
        dcn = mkPrimTuples' k
    in
    map (\(n, m, ns, dc) -> 
            let
                tn = Name n m 0 Nothing
            in
            (tn, DataTyCon {bound_ids = map (flip Id TYPE) ns, data_cons = [dc], adt_source = ADTSourceCode, to_smt = False})) dcn

mkPrimTuples' :: Int -> [(T.Text, Maybe T.Text, [Name], DataCon)]
mkPrimTuples' n | n < 0 = []
                | otherwise =
                        let
                            s = "(#" `T.append` T.pack (replicate n ',') `T.append` "#)"
#if MIN_VERSION_GLASGOW_HASKELL(9,10,0,0)
                            m = Just "GHC.Types"
#else
                            m = Just "GHC.Prim"
#endif
                            tn = Name s m 0 Nothing

                            ns = if n == 0 then [] else map (\i -> Name "a" m i Nothing) [0..fromIntegral n]
                            rt_ns = if n == 0 then [] else map (\i -> Name "rt_" m i Nothing) [0..fromIntegral n]
                            tv = map (TyVar . flip Id TYPE) ns

                            t = foldr (TyFun) (mkFullAppedTyCon TV.empty tn tv TYPE) tv
                            is = map (flip Id TYPE) ns
                            rt_is =  map (flip Id TYPE) rt_ns
                            t' = foldr TyForAll t is
                            t'' = foldr TyForAll t' rt_is
                            
                            dc = DataCon (Name s m 0 Nothing) t'' (rt_is ++ is) []
                        in
                        -- ((s, m, []), [(s, m, [])]) : mkTuples (n - 1)
                        (s, m, rt_ns ++ ns, dc) : mkPrimTuples' (n - 1)
