{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Translation.InjectSpecials
  ( specialTypes
  , specialTypeNames
  , specialConstructors
  , injectSpecials
  ) where

import Data.Foldable
import qualified Data.HashMap.Lazy as HM
import qualified Data.List as L
import qualified Data.Map as M
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
           mkTuples _MAX_TUPLE

-- specialTypes' :: [(T.Text, Maybe T.Text)]
-- specialTypes' = [ ("[]", Just "GHC.Types")
--                 , ("Int", Just "GHC.Types")
--                 , ("Float", Just "GHC.Types")
--                 , ("Double", Just "GHC.Types")
--                 , ("Char", Just "GHC.Types")
--                 , ("String", Just "GHC.Types")
--                 , ("Bool", Just "GHC.Types")
--                 , ("Ordering", Just "GHC.Types")]
--                 ++
--                 mkTuples _MAX_TUPLE

-- specialConstructors' :: [(T.Text, Maybe T.Text)]
-- specialConstructors' = [ ("[]", Just "GHC.Types")
--                        , (":", Just "GHC.Types")

--                        , ("I#", Just "GHC.Types")
--                        , ("F#", Just "GHC.Types")
--                        , ("D#", Just "GHC.Types")
--                        , ("C#", Just "GHC.Types")

--                        , ("True", Just "GHC.Types")
--                        , ("False", Just "GHC.Types")

--                        , ("EQ", Just "GHC.Types")
--                        , ("LT", Just "GHC.Types")
--                        , ("GT", Just "GHC.Types")]
--                        ++
--                        mkTuples _MAX_TUPLE

specials' :: [(T.Text, [T.Text])]
specials' = [ ("[]", ["[]", ":"])
           , ("~", [])
           , ("~~", [])]
           ++
           [ ("Int", ["I#"])
           , ("Float", ["F#"])
           , ("Double", ["D#"])
           , ("Char", ["C#"])
           , ("String", [])
           , ("Bool", ["True", "False"])
           , ("Ordering", ["EQ", "LT", "GT"]) ]
           ++
           (map (\t -> (t, [t])) $ mkTuples' _MAX_TUPLE)

mkTuples :: Int -> [((T.Text, Maybe  T.Text, [Name]), [(T.Text, Maybe T.Text, [Type])])]
mkTuples n | n < 0    = []
           | otherwise =
                let
                    s = "(" `T.append` T.pack (replicate n ',') `T.append` ")"
                in
                ((s, Just s, []), [(s, Just s, [])]) : mkTuples (n - 1)

mkTuples' :: Int -> [T.Text]
mkTuples' n | n < 0    = []
           | otherwise =
                "(" `T.append` T.pack (replicate n ',') `T.append` ")" : mkTuples' (n - 1)


isNameSpecial :: Name -> Bool
isNameSpecial name = nameOccStr name `elem` flattened
  where
    flattened = concatMap (\s -> fst s : snd s) specials'

isTypeSpecial :: Type -> Bool
isTypeSpecial (TyConApp n _) = isNameSpecial n
isTypeSpecial _ = False

isDataConSpecial :: DataCon -> Bool
isDataConSpecial (DataCon n _ _) = isNameSpecial n
isDataConSpecial _ = False

altDataCons :: Alt -> [DataCon]
altDataCons (Alt (DataAlt dc _) _) = [dc]
altDataCons _ = []

mkEntry :: [DataCon] -> Name -> (Name, AlgDataTy)
mkEntry samples name = (name, adt)
  where
    adt = DataTyCon { bound_names = binders
                    , data_cons = dcs }
    targets = case L.find ((== (nameOccStr name)) . fst) specials' of
                  Nothing -> []
                  Just (t, ns) -> ns
    dcs = concatMap (\dc -> case dc of
              DataCon n t ts -> if nameOccStr n `elem` targets then [dc] else []
              _ -> [])
            samples
    binders = L.nub $ evalASTs go dcs

    go :: Type -> [Name]
    go (TyForAll (NamedTyBndr (Id n _)) _ ) = [n]
    go _ = []


injectSpecials :: [ProgramType] -> Program -> (Program, [ProgramType])
injectSpecials tenv eenv = (eenv', L.nub $ entries ++ tenv)
  where
    eenv' = foldr (uncurry rename) eenv renameList
    -- eenv' = eenv

    renameList = concatMap (\(n:ns ) -> map (flip (,) n) ns) $
                           map (map dcName) $ filter (not . null) groups

    entries = map (mkEntry dcs) tys

    -- The pairs we end up using
    tys = evalASTs go1 eenv
    go2res = L.sortOn (\(DataCon n _ _) -> n) $ evalASTs go2 eenv
    groups = L.groupBy (\(DataCon (Name o1 m1 _) _ _)
                         (DataCon (Name o2 m2 _) _ _) -> o1 == o2 && m1 == m2)
                       go2res

    dcs = concatMap (\g -> case g of { [] -> []; (x:_) -> [x] }) groups

    -- dcs = L.nubBy (\(DataCon (Name o1 m1 _) _ _)
    --                 (DataCon (Name o2 m2 _) _ _) -> o1 == o2 && m1 == m2) $ evalASTs go2 eenv

    -- The special ones.
    -- Function for getting the right types out of the tenv.
    go1 :: Type -> [Name]
    go1 (TyConApp n _) = if isNameSpecial n then [n] else []
    go1 _ = []

    -- Function for getting the right constructors out of the eenv.
    go2 :: Expr -> [DataCon]
    go2 (Var (Id n t)) = if isNameSpecial n then [DataCon n t (nonTyForAllArgumentTypes t)] else []
    go2 (Data dc) = if isDataConSpecial dc then [dc] else []
    go2 (Case _ _ as) = filter isDataConSpecial $ concatMap altDataCons as
    go2 _ = []

