-- This module generates functions in the expr_env that walk over the whole structure of an ADT.
-- This forces evaluation of the ADT
module G2.Internals.Initialization.DeepSeqWalks (createDeepSeqWalks) where

import G2.Internals.Language

import Data.List
import qualified Data.Map as M

import Debug.Trace

data TyTracker = Ty Name | TyV Name

createDeepSeqWalks :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, NameGen, Walkers)
createDeepSeqWalks eenv tenv ng =
    let
        tenv' = M.toList tenv
    in
    createFuncs eenv ng tenv' M.empty (createDeepSeqName . fst) createDeepSeqStore createDeepSeqExpr

createDeepSeqName ::  Name -> Name
createDeepSeqName (Name n _ _) = Name ("walk" ++ n) Nothing 0

createDeepSeqStore :: (Name, AlgDataTy) -> Name -> Walkers -> Walkers
createDeepSeqStore (n, adt) n' w =
    let
        t = TyFun (TyConApp n []) (TyConApp n [])
        i = Id n' t
    in
    M.insert n i w

createDeepSeqExpr :: Walkers -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
createDeepSeqExpr w (n, adt) ng =
    let
        bn = bound_names adt

        lamTy = concatMap (\b -> [(Ty b, TYPE)
                                 , (TyV b, TyFun (TyVar (Id b TYPE)) (TyVar (Id b TYPE)))]) bn
    in
    mkMappedLamBindings ng lamTy (createDeepSeqExpr' w n adt)

createDeepSeqExpr' :: Walkers -> Name -> AlgDataTy -> NameGen -> [(TyTracker, Id)] -> (Expr, NameGen)
createDeepSeqExpr' w n adt ng is =
    let
        bn = bound_names adt

        (i, ng2) = freshId (TyConApp n $ map (TyVar . flip Id TYPE) bn) ng
        (bind, ng3) = freshId (TyConApp n $ map (TyVar . flip Id TYPE) bn) ng2

        (am, ng4) = createDeepSeqAlts w n adt ng3 is bind

        c = Case (Var i) bind am
    in
    (Lam i c, ng4)

createDeepSeqAlts :: Walkers -> Name -> AlgDataTy -> NameGen -> [(TyTracker, Id)] -> Id -> ([Alt], NameGen)
createDeepSeqAlts w n (DataTyCon { data_cons = dc }) ng is i =
    createDeepSeqDataCon w n dc ng is i
createDeepSeqAlts w n (NewTyCon { data_con = dc, rep_type = t}) ng is i =
    createDeepSeqNewTyCon w n dc t ng is i

createDeepSeqDataCon :: Walkers -> Name -> [DataCon] -> NameGen -> [(TyTracker, Id)] -> Id -> ([Alt], NameGen)
createDeepSeqDataCon w n (dc@(DataCon n' t ts):dcs) ng is i =
    let
        (binds, ng2) = freshIds ts ng

        (e, ng3) = deepSeqCase w binds (Data dc) ng2 [] -- foldl' (\f i -> App f (idCase (deepSeqFuncCall w (Var i))))

        alt = Alt (DataAlt dc binds) e

        (alts, ng4) = createDeepSeqDataCon w n dcs ng3 is i
    in
    (alt:alts, ng4)
createDeepSeqDataCon _ _ _ ng _ _ = ([], ng)

createDeepSeqNewTyCon :: Walkers -> Name -> DataCon -> Type -> NameGen -> [(TyTracker, Id)] -> Id -> ([Alt], NameGen)
createDeepSeqNewTyCon w n (DataCon n' t ts) t'@(TyConApp tn _) ng is i =
    let
        innerT = returnType t

        innerCast = Cast (Var i) (innerT :~ t')
        innerDeepSeq = deepSeqFuncCall w innerCast  --TODO: What if f needs other function arguments?

        outerCast = Cast innerDeepSeq (t' :~ innerT)
    in
    ([Alt Default outerCast], ng)
createDeepSeqNewTyCon w n dc t ng is i = ([Alt Default (Var (Id (Name "A" Nothing 0) TyBottom))], ng) --  error $ "dc = " ++ show dc ++ " t = " ++ show t

deepSeqCase :: Walkers -> [Id] -> Expr -> NameGen -> [Expr] -> (Expr, NameGen)
deepSeqCase _ [] e ng es = (mkApp (e:reverse es), ng)
deepSeqCase w (i:is) e ng es = 
    let
        (i', ng2) = freshId (typeOf i) ng

        b = deepSeqFuncCall w (Var i)

        (ae, ng3) = deepSeqCase w is e ng2 ((Var i'):es)
    in
    (Case b i' [Alt Default ae], ng3)

deepSeqFuncCall :: Walkers -> Expr -> Expr
deepSeqFuncCall w e =
    let
        t = case typeOf e of
            (TyConApp n _) -> Just n
            _ -> Nothing
    in
    case fmap (\t' -> M.lookup t' w) t of
        Just (Just f) -> App (Var f) e
        _ -> e

idCase :: Expr -> Expr
idCase e = 
    let
        i = Id (Name "n" Nothing 0) (typeOf e)
    in
    Case e i [Alt Default (Var i)]

-- module G2.Internals.Initialization.CreateFuncs ( createDeepSeqWalks
--                                                , createPolyPredWalks
--                                                , createHigherOrderWrappers ) where

-- import G2.Internals.Language
-- import qualified G2.Internals.Language.ExprEnv as E

-- import Data.List
-- import qualified Data.Map as M
-- import Data.Maybe

-- storeWalkerFunc :: Walkers -> Name -> AlgDataTy -> Name -> Expr -> Walkers
-- storeWalkerFunc w tn _ fn e =
--     let
--          i = Id fn (typeOf e)-- walkFunc tn fn
--     in
--     M.insert tn i w

-- -- | createDeepSeqWalks
-- -- This generates functions that walk over the whole structure of an ADT.
-- -- This forces evaluation of the ADT
-- createDeepSeqWalks :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, NameGen, Walkers)
-- createDeepSeqWalks eenv tenv ng =
--     createAlgDataTyWalks eenv tenv ng createDeepSeqWalkArgs "walk" 
--         (\dc adt nna ng' _ is pfs -> createDeepSeqExpr dc adt nna ng' is pfs)
--         (\_ _ ng' i _ -> (Var i, ng'))
--         storeWalkerFunc

-- -- | createDeepSeqWalkArgs
-- -- For each type parameter of type a, we create an argument of type (a -> a),
-- -- which should be passed the deep seq walk for that type
-- createDeepSeqWalkArgs :: AlgDataTy -> [(Name, Maybe Name, Type)]
-- createDeepSeqWalkArgs dc = 
--        map (\n -> (n, Just n, TYPE)) (bound_names dc)
--     ++ map (\n -> (tyFunName n, Just (tyFunName n), (TyFun (TyVar (Id n TYPE)) (TyVar (Id n TYPE))))) (bound_names dc)

-- -- The (Name, Name, AlgDataTy) tuples are the type name, the walking function
-- -- name, and the AlgDataTyName
-- createDeepSeqExpr :: DataCon  -> AlgDataTy -> [(Name, Name, AlgDataTy)] -> NameGen -> [Id] -> [(Name, Id)] -> (Maybe Expr, NameGen)
-- createDeepSeqExpr dc@(DataCon _ _ _) adt ns ng arg_ids pfs =
--     let
--         (e, ng2) = createDeepSeqExpr' (Data dc) adt ns ng arg_ids pfs
--     in
--     (Just e, ng2)
-- createDeepSeqExpr _ _ _ ng _ _ = (Nothing, ng)

-- createDeepSeqExpr' :: Expr -> AlgDataTy -> [(Name, Name, AlgDataTy)] -> NameGen -> [Id] -> [(Name, Id)] -> (Expr, NameGen)
-- createDeepSeqExpr' dc _ _ ng [] _ = (dc, ng)
-- createDeepSeqExpr' dc adt@(DataTyCon _ _) ns ng (i@(Id _ t):xs) pfs =
--     let
--         (b_id, ng') = freshId t ng

--         case_e = createDeepSeqCase t ns i b_id pfs
--         -- case_e = case t of
--         --             TyConApp n ts ->
--         --                 let
--         --                     (t', w, _) = fromJust $ find (\(t'', _, _) -> t'' == n) ns
--         --                     f = walkFunc t' w

--         --                     typeV = map (\(TyVar (Id n' _)) ->  Var . fromJust $ lookup n' pfs) ts
--         --                     typeF = mapMaybe (typeWalker pfs) ts

--         --                     app = mkApp $ Var f : typeV ++ typeF ++ [Var i]
--         --                 in
--         --                 Case app b_id
--         --             TyVar (Id n _) ->
--         --                 let
--         --                     w = fromJust $ lookup (tyFunName n) pfs
--         --                 in
--         --                 Case (App (Var w) (Var i)) b_id
--         --             _ -> Case (Var i) b_id

--         dc' = App dc (Var b_id)

--         (e, ng'') = createDeepSeqExpr' dc' adt ns ng' xs pfs

--         am = [Alt Default e]
--     in
--     (case_e am, ng'')
-- createDeepSeqExpr' dc (NewTyCon _ _ t) ns ng (i:_) pfs =
--     let
--         retT = returnType . typeOf $ dc

--         dc' = Cast (Var i) (retT :~ t)
--         e' = Cast dc' (t :~ retT)
--     in
--     (e', ng)

-- createDeepSeqCase :: Type -> [(Name, Name, AlgDataTy)] -> Id -> Id -> [(Name, Id)] -> ([Alt] -> Expr)
-- createDeepSeqCase (TyConApp n ts) ns i b_id pfs =
--     let
--         (t', w, _) = fromJust $ find (\(t'', _, _) -> t'' == n) ns
--         f = walkFunc t' w

--         typeV = mapMaybe (tyvarFunc pfs) ts
--         typeF = mapMaybe (typeWalker pfs) ts

--         app = mkApp $ Var f : typeV ++ typeF ++ [Var i]
--     in
--     Case app b_id
-- createDeepSeqCase (TyVar (Id n _)) ns i b_id pfs =
--     let
--         w = fromJust $ lookup (tyFunName n) pfs
--     in
--     Case (App (Var w) (Var i)) b_id
-- createDeepSeqCase _ _ i b_id _ = Case (Var i) b_id

-- tyvarFunc :: [(Name, Id)] -> Type -> Maybe Expr
-- tyvarFunc pfs (TyVar (Id n' _)) = fmap Var $ lookup n' pfs
-- tyvarFunc _ _ = Nothing

-- typeWalker :: [(Name, Id)] -> Type -> Maybe Expr
-- typeWalker pfs (TyVar (Id n _)) = fmap Var $ lookup (tyFunName n) pfs
-- typeWalker _ _ = Nothing

-- tyFunName :: Name -> Name
-- tyFunName (Name n m i) = Name (n ++ "TyFun") m i

-- -- Type Name -> Walk function name -> Walk Function Id
-- walkFunc :: Name -> Name -> Id
-- walkFunc t w = Id w (TyFun (TyConApp t []) (TyConApp t []))



-- -- | createPolyPredWalks
-- -- Creates functions that walk over a polymorphic ADT D t_1 ... t_n, with type:
-- --      f :: (t_1 -> Bool) -> ... -> (t_n -> Bool) -> d -> Bool 
-- --      f p_1 ... p_n d
-- -- The predicate p_i is run on every value of type t_i, and the conjunction is returned
-- createPolyPredWalks :: ExprEnv -> TypeEnv -> NameGen -> KnownValues -> (ExprEnv, NameGen, Walkers)
-- createPolyPredWalks eenv tenv ng kv =
--     let
--         poly_tenv = M.filter isPolyAlgDataTy tenv
--     in
--     createAlgDataTyWalks eenv poly_tenv ng
--         (createPolyPredArgs kv)
--         "polyPred"
--         (createPolyPredAlt eenv tenv kv)
--         (\_ _ ng' i _ -> (Var i, ng'))
--         storeWalkerFunc

-- createPolyPredArgs :: KnownValues -> AlgDataTy -> [(Maybe Name, Maybe Name, Type)]
-- createPolyPredArgs kv dc =
--     map (\n -> (Nothing, Just n, TYPE)) (bound_names dc) 
--     ++ map (\n -> (Just n, Nothing, TyFun (TyVar $ Id n TYPE) (tyBool kv))) (bound_names dc)

-- createPolyPredAlt :: ExprEnv -> TypeEnv -> KnownValues -> DataCon -> AlgDataTy -> [(Name, Name, AlgDataTy)] -> NameGen -> Id -> [Id] -> [(Maybe Name, Id)] -> (Maybe Expr, NameGen)
-- createPolyPredAlt eenv tenv kv (DataCon _ t _) _ _ ng _ dcs is = 
--     let
--         (e, ng2) = createPolyPredAlt' eenv tenv kv dcs ng is
--     in
--     case polyIds t of
--         [] -> (Nothing, ng)
--         _ -> (Just e, ng2)
-- createPolyPredAlt _ _ _ (PrimCon _) _ _ _ _ _ _ = error "PrimCon in createPolyPredAlt"

-- createPolyPredAlt' :: ExprEnv -> TypeEnv -> KnownValues -> [Id] -> NameGen -> [(Maybe Name, Id)] -> (Expr, NameGen)
-- createPolyPredAlt' eenv tenv kv dcpat ng is =
--     let
--         predApps = mapMaybe (createPolyPredAlt'' is) dcpat
--     in
--     (foldr (\e e' -> App (
--                             App (mkAnd eenv)
--                             e
--                         ) e') (mkTrue kv tenv) predApps, ng)

-- createPolyPredAlt'' :: [(Maybe Name, Id)] -> Id -> Maybe Expr
-- createPolyPredAlt'' typePreds i@(Id _ (TyVar (Id n _))) =
--     case lookup (Just n) typePreds of
--         Just f -> Just $ App (Var f) (Var i)
--         Nothing -> Nothing
-- createPolyPredAlt'' _ _ = Nothing



-- -- | createHigherOrderWrapper
-- -- This generates function to impose asserts on the input and output of higher
-- -- order functions.  For each function in a higher order function signature:
-- --      f :: (a_1 -> ... -> a_n -> b) -> ... -> c
-- -- we autogenerate a function:
-- --      wrapper :: (a_1 -> ... -> a_n -> b -> Bool)
-- --              -> (a_1 -> ... -> a_n -> b) -> a_1 -> ... -> a_n -> b
-- createHigherOrderWrappers :: ExprEnv -> TypeEnv -> NameGen -> KnownValues -> (ExprEnv, NameGen, Wrappers)
-- createHigherOrderWrappers eenv tenv ng kv =
--     let
--         types = nub $ argTypesTEnv tenv ++ E.higherOrderExprs eenv
--     in
--     createFuncs eenv ng (zip (repeat ()) types) []
--         (const $ Name "wrapper" Nothing 0)
--         (createHigherOrderWrapperExpr kv)
--         storeWrapper

-- createHigherOrderWrapperExpr :: KnownValues -> NameGen -> [((), Name, Type)] -> () -> Type -> (Expr, NameGen)
-- createHigherOrderWrapperExpr kv ng _ _ t =
--     let
--         predType = appendType t (tyBool kv)

--         wrapperT = [(Just "pred", Nothing, predType), (Just "higher", Nothing, t)]
--                    ++ zip3 (repeat Nothing) (repeat Nothing) (init $ splitTyFuns t)
--     in
--     mkLamBindings ng wrapperT $ \ng' wr -> createHigherOrderWrapperExpr' ng' wr

-- createHigherOrderWrapperExpr' :: NameGen -> [(Maybe String, Id)] -> (Expr, NameGen)
-- createHigherOrderWrapperExpr' ng ts' =
--     let
--         pre:higher:ts = map snd ts'

--         higherCall = mkApp . map Var $ higher:ts

--         (higherId, ng') = freshId (typeOf higherCall) ng

--         predCall = mkApp . map Var $ pre:ts ++ [higherId]

--         a = Assume predCall (Var higherId)

--         letExpr = Let [(higherId, higherCall)] a
--     in
--     (letExpr, ng')

-- storeWrapper :: Wrappers -> () -> Type -> Name -> Expr -> Wrappers
-- storeWrapper w _ t n e = (t, Id n (typeOf e)):w

