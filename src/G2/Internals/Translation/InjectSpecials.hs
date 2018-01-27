module G2.Internals.Translation.InjectSpecials
  ( injectSpecials
  ) where

import qualified Data.List as L
import qualified Data.Map as M

import G2.Internals.Language

specials :: [(String, [String])]
specials = [ ("[]", ["[]", ":"])
           , ("~", [])
           , ("~~", [])] ++
           [ ("Int", ["I#"])
           , ("Float", ["F#"])
           , ("Double", ["D#"])
           , ("Char", ["C#"])
           , ("String", [])
           , ("Bool", ["True", "False"])
           , ("Ordering", ["EQ", "LT", "GT"]) ]

isNameSpecial :: Name -> Bool
isNameSpecial name = nameOccStr name `elem` flattened
  where
    flattened = concatMap (\s -> fst s : snd s) specials

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
    targets = case L.find ((== (nameOccStr name)) . fst) specials of
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

-- mkEntry :: Name -> [DataCon] -> (Name, AlgDataTy)
-- mkEntry name samples = (name, adt)
--   where
--     adt = DataTyCon { bound_names = binders
--                     , data_cons = dcs }
--     targets = case L.find ((== (nameOccStr name)) . fst) specials of
--                   Nothing -> []
--                   Just (t, ns) -> ns
--     dcs = concatMap (\dc -> case dc of
--               DataCon n _ _ -> if nameOccStr n `elem` targets then [dc] else []
--               _ -> [])
--             samples
--     binders = evalASTs go dcs

--     go :: Type -> [Name]
--     go (TyForAll (NamedTyBndr (Id n _)) _ ) = [n]
--     go _ = []

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
    go2 (Var (Id n t)) = if isNameSpecial n then [DataCon n t (argumentTypes t)] else []
    go2 (Data dc) = if isDataConSpecial dc then [dc] else []
    go2 (Case _ _ as) = filter isDataConSpecial $ concatMap altDataCons as
    go2 _ = []

-- injectSpecials :: TypeEnv -> ExprEnv -> TypeEnv
-- injectSpecials tenv eenv = foldr (\(n, dcs) m -> M.insert n dcs m) tenv entries
--   where
--     entries = map ((flip mkEntry) dcs) tys

--     -- The pairs we end up using
--     tys = L.nub $ evalASTs go1 eenv --Anton, you had the tenv here- it seems like it should be the eenv?  But I'mm not sure, maybe I'm missing something..,
--     dcs = L.nub $ evalASTs go2 eenv

--     -- The special ones.
--     -- Function for getting the right types out of the tenv.
--     go1 :: Type -> [Name]
--     go1 (TyConApp n _) = if isNameSpecial n then [n] else []
--     go1 _ = []

--     -- Function for getting the right constructors out of the eenv.
--     go2 :: Expr -> [DataCon]
--     go2 (Data dc) = if isDataConSpecial dc then [dc] else []
--     go2 (Case _ _ as) = filter isDataConSpecial $ concatMap altDataCons as
--     go2 _ = []

