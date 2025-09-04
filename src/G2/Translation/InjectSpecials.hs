{-# LANGUAGE CPP, OverloadedStrings #-}

module G2.Translation.InjectSpecials
  ( specialTypes
  , specialTypeNames
  , specialConstructors
  ) where

import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T

import G2.Language
import qualified G2.Language.TyVarEnv as TV 

_MAX_TUPLE :: Int
_MAX_TUPLE = 62

specialTypes :: HM.HashMap Name AlgDataTy
specialTypes = HM.fromList $ map (uncurry specialTypes') specials ++ mkPrimTuples _MAX_TUPLE

specialTypes' :: (T.Text, Maybe T.Text, [Name]) -> [(T.Text, Maybe T.Text, [Type])] -> (Name, AlgDataTy)
specialTypes' (n, m, ns) dcn = 
    let
        tn = Name n m 0 Nothing
        dc = map (specialDC ns tn) dcn
    in
    (tn, DataTyCon {bound_ids = map (flip Id TYPE) ns, data_cons = dc, adt_source = ADTSourceCode})

specialDC :: [Name] -> Name -> (T.Text, Maybe T.Text, [Type]) -> DataCon
specialDC ns tn (n, m, ts) = 
    let
        tv = map (TyVar . flip Id TYPE) ns

        t = foldr TyFun (mkFullAppedTyCon TV.empty tn tv TYPE) ts
        is = map (flip Id TYPE) ns
        t' = foldr TyForAll t is
    in
    DataCon (Name n m 0 Nothing) t' is []

specialTypeNames :: HM.HashMap (T.Text, Maybe T.Text) Name
specialTypeNames = -- HM.fromList $ map (\(n, m, _) -> ((n, m), Name n m 0 Nothing)) specialTypeNames'
      HM.fromList . map (\nm@(Name n m _ _) -> ((n, m), nm)) $ HM.keys specialTypes

specialConstructors :: HM.HashMap (T.Text, Maybe T.Text) Name
specialConstructors =
    -- GHC 9.4 on use different constructors than our base for Integers, so we add a special mapping
    -- for those constructor (via `integerConstructor` to adjust Names accordingly)
    HM.fromList $ integerConstructor:map (\(DataCon nm@(Name n m _ _) _ _ _)-> ((n, m), nm)) specialConstructors'

integerConstructor :: ((T.Text, Maybe T.Text), Name)
integerConstructor = (("IS", Just "GHC.Num.Integer"), Name "Z#" (Just "GHC.Num.Integer") 0 Nothing)

specialConstructors' :: [DataCon]
specialConstructors' = concatMap data_cons $ HM.elems specialTypes -- map (\(n, m, _) -> (n, m)) $ concatMap snd specials

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

specials :: [((T.Text, Maybe T.Text, [Name]), [(T.Text, Maybe T.Text, [Type])])]
specials =
           [ (( listTypeStr
              , Just "GHC.Types", [aName])
              , [ ("[]", Just "GHC.Types", [])
                , (":", Just "GHC.Types", [aTyVar, mkFullAppedTyCon TV.empty listName [aTyVar] TYPE])]
             )
           -- , (("Int", Just "GHC.Types"), [("I#", Just "GHC.Types", [TyLitInt])])
           -- , (("Float", Just "GHC.Types"), [("F#", Just "GHC.Types", [TyLitFloat])])
           -- , (("Double", Just "GHC.Types"), [("D#", Just "GHC.Types", [TyLitDouble])])
           -- , (("Char", Just "GHC.Types"), [("C#", Just "GHC.Types", [TyLitChar])])
           -- , (("String", Just "GHC.Types"), [])

           , (("Bool", Just "GHC.Types", []), [ ("False", Just "GHC.Types", [])
                                              , ("True", Just "GHC.Types", [])])

           -- , (("Ordering", Just "GHC.Types"), [ ("EQ", Just "GHC.Types", [])
           --                                    , ("LT", Just "GHC.Types", [])
           --                                    , ("GT", Just "GHC.Types", [])])
           ]
           ++
#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
           mkTuples "(" ")" (Just "GHC.Tuple.Prim") _MAX_TUPLE
#else
           mkTuples "(" ")" (Just "GHC.Tuple") _MAX_TUPLE
#endif
           -- ++
           -- mkTuples "(#" "#)" (Just "GHC.Prim") _MAX_TUPLE


mkTuples :: T.Text -> T.Text -> Maybe T.Text -> Int -> [((T.Text, Maybe  T.Text, [Name]), [(T.Text, Maybe T.Text, [Type])])]
mkTuples ls rs m n | n < 0 = []
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
                            ns = if n == 0 then [] else map (\i -> Name "a" m i Nothing) [0..n]
                            tv = map (TyVar . flip Id TYPE) ns
                        in
                        -- ((s, m, []), [(s, m, [])]) : mkTuples (n - 1)
                        ((ty_n, m, ns), [(cons_n, m, tv)]) : mkTuples ls rs m (n - 1)

mkPrimTuples :: Int -> [(Name, AlgDataTy)]
mkPrimTuples k =
    let
        dcn = mkPrimTuples' k
    in
    map (\(n, m, ns, dc) -> 
            let
                tn = Name n m 0 Nothing
            in
            (tn, DataTyCon {bound_ids = map (flip Id TYPE) ns, data_cons = [dc], adt_source = ADTSourceCode})) dcn

mkPrimTuples' :: Int -> [(T.Text, Maybe T.Text, [Name], DataCon)]
mkPrimTuples' n | n < 0 = []
                | otherwise =
                        let
                            s = "(#" `T.append` T.pack (replicate n ',') `T.append` "#)"
                            m = Just "GHC.Prim"
                            tn = Name s m 0 Nothing

                            ns = if n == 0 then [] else map (\i -> Name "a" m i Nothing) [0..n]
                            rt_ns = if n == 0 then [] else map (\i -> Name "rt_" m i Nothing) [0..n]
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
