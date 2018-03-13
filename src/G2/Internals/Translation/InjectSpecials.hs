{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Translation.InjectSpecials
  ( specialTypes
  , specialTypeNames
  , specialConstructors
  ) where

import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T

import G2.Internals.Language

_MAX_TUPLE :: Int
_MAX_TUPLE = 62

specialTypes :: [ProgramType]
specialTypes = map (uncurry specialTypes') specials

specialTypes' :: (T.Text, Maybe T.Text, [Name]) -> [(T.Text, Maybe T.Text, [Type])] -> (Name, AlgDataTy)
specialTypes' (n, m, ns) dcn = 
    let
        tn = Name n m 0
        dc = map (specialDC ns tn) dcn
    in
    (tn, DataTyCon {bound_names = ns, data_cons = dc})

specialDC :: [Name] -> Name -> (T.Text, Maybe T.Text, [Type]) -> DataCon
specialDC ns tn (n, m, ts) = 
    let
        tv = map (TyVar . flip Id TYPE) ns

        t = foldr (TyFun) (TyConApp tn tv) ts
        t' = foldr (\n' -> TyForAll (NamedTyBndr (Id n' TYPE))) t ns
    in
    DataCon (Name n m 0) t' ts

specialTypeNames :: HM.HashMap (T.Text, Maybe T.Text) Name
specialTypeNames = HM.fromList $ map (\(n, m, _) -> ((n, m), Name n m 0)) specialTypeNames'

specialConstructors :: HM.HashMap (T.Text, Maybe T.Text) Name
specialConstructors =
    HM.fromList $ map (\nm@(n, m) -> (nm, Name n m 0)) specialConstructors'

specialTypeNames' :: [(T.Text, Maybe T.Text, [Name])]
specialTypeNames' = map fst specials

specialConstructors' :: [(T.Text, Maybe T.Text)]
specialConstructors' = map (\(n, m, _) -> (n, m)) $ concatMap snd specials

aName :: Name
aName = Name "a" Nothing 0

aTyVar :: Type
aTyVar = TyVar (Id aName TYPE)

listName :: Name
listName = Name "[]" (Just "GHC.Types") 0

specials :: [((T.Text, Maybe T.Text, [Name]), [(T.Text, Maybe T.Text, [Type])])]
specials = [ (( "[]"
              , Just "GHC.Types", [aName])
              , [ ("[]", Just "GHC.Types", [])
                , (":", Just "GHC.Types", [aTyVar, TyConApp listName [aTyVar]])]
             )

           -- , (("Int", Just "GHC.Types"), [("I#", Just "GHC.Types", [TyLitInt])])
           -- , (("Float", Just "GHC.Types"), [("F#", Just "GHC.Types", [TyLitFloat])])
           -- , (("Double", Just "GHC.Types"), [("D#", Just "GHC.Types", [TyLitDouble])])
           -- , (("Char", Just "GHC.Types"), [("C#", Just "GHC.Types", [TyLitChar])])
           -- , (("String", Just "GHC.Types"), [])

           , (("Bool", Just "GHC.Types", []), [ ("True", Just "GHC.Types", [])
                                              , ("False", Just "GHC.Types", [])])

           -- , (("Ordering", Just "GHC.Types"), [ ("EQ", Just "GHC.Types", [])
           --                                    , ("LT", Just "GHC.Types", [])
           --                                    , ("GT", Just "GHC.Types", [])])
           ]
           ++
           mkTuples "(" ")" (Just "GHC.Tuple") _MAX_TUPLE
           ++
           mkTuples "(#" "#)" (Just "GHC.Prim") _MAX_TUPLE


mkTuples :: T.Text -> T.Text -> Maybe T.Text -> Int -> [((T.Text, Maybe  T.Text, [Name]), [(T.Text, Maybe T.Text, [Type])])]
mkTuples ls rs m n | n < 0 = []
                   | otherwise =
                        let
                            s = ls `T.append` T.pack (replicate n ',') `T.append` rs

                            ns = if n == 0 then [] else map (Name "a" m) [0..n]
                            tv = map (TyVar . flip Id TYPE) ns
                        in
                        -- ((s, m, []), [(s, m, [])]) : mkTuples (n - 1)
                        ((s, m, ns), [(s, m, tv)]) : mkTuples ls rs m (n - 1)