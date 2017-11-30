-- This module generates functions in the expr_env that walk over the whole structure of an ADT.
-- This forces evaluation of the ADT

module G2.Internals.Initialization.CreateFuncs ( createDeepSeqWalks
                                               , createPolyPredWalks
                                               , createHigherOrderWrappers ) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E

import Data.List
import qualified Data.Map as M
import Data.Maybe

import Debug.Trace

storeWalkerFunc :: Walkers -> Name -> AlgDataTy -> Name -> Expr -> Walkers
storeWalkerFunc w tn _ fn e =
    let
         i = Id fn (typeOf e)-- walkFunc tn fn
    in
    M.insert tn i w

-- | createDeepSeqWalks
-- This generates functions that walk over the whole structure of an ADT.
-- This forces evaluation of the ADT
createDeepSeqWalks :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, NameGen, Walkers)
createDeepSeqWalks eenv tenv ng =
    createAlgDataTyWalks eenv tenv ng createDeepSeqWalkArgs "walk" 
        (\dc nna ng' _ is pfs -> createDeepSeqExpr dc nna ng' is pfs)
        (\_ ng' i _ -> (Var i, ng'))
        storeWalkerFunc

-- | createDeepSeqWalkArgs
-- For each type parameter of type a, we create an argument of type (a -> a),
-- which should be passed the deep seq walk for that type
createDeepSeqWalkArgs :: AlgDataTy -> [(Name, Maybe Name, Type)]
createDeepSeqWalkArgs dc = 
       map (\n -> (n, Just n, TYPE)) (bound_names dc)
    ++ map (\n -> (tyFunName n, Just (tyFunName n), (TyFun (TyVar (Id n TYPE)) (TyVar (Id n TYPE))))) (bound_names dc)

-- The (Name, Name, AlgDataTy) tuples are the type name, the walking function
-- name, and the AlgDataTyName
createDeepSeqExpr :: DataCon -> [(Name, Name, AlgDataTy)] -> NameGen -> [Id] -> [(Name, Id)] -> (Maybe Expr, NameGen)
createDeepSeqExpr dc@(DataCon _ _ _) ns ng arg_ids pfs =
    let
        (e, ng2) = createDeepSeqExpr' (Data dc) ns ng arg_ids pfs
    in
    -- trace ("called with: " ++ show (dc, ns, ng, arg_ids, pfs)) $
    (Just e, ng2)
createDeepSeqExpr _ _ ng _ _ = (Nothing, ng)

createDeepSeqExpr' :: Expr -> [(Name, Name, AlgDataTy)] -> NameGen -> [Id] -> [(Name, Id)] -> (Expr, NameGen)
createDeepSeqExpr' dc _ ng [] _ = (dc, ng)
createDeepSeqExpr' dc ns ng (i@(Id _ t):xs) pfs =
    let
        ns_dull = filter (\(n, _, _) -> not $ isNameSpecial n) ns
        (b_id, ng') = freshId t ng

        case_e = if isTypeSpecial t
                  then Case (Var i) b_id
                  else case t of
                    TyConApp n ts ->
                        let
                            ts_dull = filter (not . isTypeSpecial) ts
                            (t', w, _) = fromJust $ find (\(t'', _, _) -> t'' == n) ns_dull
                            f = walkFunc t' w

                            typeV = map (\(TyVar (Id n' _)) ->  Var . fromJust $ lookup n' pfs) ts_dull
                            typeF = mapMaybe (typeWalker pfs) ts_dull

                            app = mkApp $ Var f : typeV ++ typeF ++ [Var i]
                        in
                        Case app b_id
                    TyVar (Id n _) ->
                        let
                            w = fromJust $ lookup (tyFunName n) pfs
                        in
                        Case (App (Var w) (Var i)) b_id
                    _ -> Case (Var i) b_id

        dc' = App dc (Var b_id)

        (e, ng'') = createDeepSeqExpr' dc' ns_dull ng' xs pfs

        am = [Alt Default e]
    in
    (case_e am, ng'')

typeWalker :: [(Name, Id)] -> Type -> Maybe Expr
typeWalker pfs (TyVar (Id n _)) = fmap Var $ lookup (tyFunName n) pfs
typeWalker _ _ = Nothing

tyFunName :: Name -> Name
tyFunName (Name n m i) = Name (n ++ "TyFun") m i

-- Type Name -> Walk function name -> Walk Function Id
walkFunc :: Name -> Name -> Id
walkFunc t w = Id w (TyFun (TyConApp t []) (TyConApp t []))



-- | createPolyPredWalks
-- Creates functions that walk over a polymorphic ADT D t_1 ... t_n, with type:
--      f :: (t_1 -> Bool) -> ... -> (t_n -> Bool) -> d -> Bool 
--      f p_1 ... p_n d
-- The predicate p_i is run on every value of type t_i, and the conjunction is returned
createPolyPredWalks :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, NameGen, Walkers)
createPolyPredWalks eenv tenv ng =
    let
        poly_tenv = M.filter isPolyAlgDataTy tenv
    in
    createAlgDataTyWalks eenv poly_tenv ng
        (createPolyPredArgs)
        "polyPred"
        (createPolyPredAlt eenv)
        (\_ ng' i _ -> (Var i, ng'))
        storeWalkerFunc

createPolyPredArgs :: AlgDataTy -> [(Maybe Name, Maybe Name, Type)]
createPolyPredArgs dc =
    map (\n -> (Nothing, Just n, TYPE)) (bound_names dc) 
    ++ map (\n -> (Just n, Nothing, TyFun (TyVar $ Id n TYPE) (TyBool))) (bound_names dc)

createPolyPredAlt :: ExprEnv -> DataCon -> [(Name, Name, AlgDataTy)] -> NameGen -> Id -> [Id] -> [(Maybe Name, Id)] -> (Maybe Expr, NameGen)
createPolyPredAlt eenv (DataCon _ t _) _ ng _ dcs is = 
    let
        (e, ng2) = createPolyPredAlt' eenv dcs ng is
    in
    case polyIds t of
        [] -> (Nothing, ng)
        _ -> (Just e, ng2)
createPolyPredAlt _ (PrimCon _) _ _ _ _ _ = error "PrimCon in createPolyPredAlt"

createPolyPredAlt' :: ExprEnv -> [Id] -> NameGen -> [(Maybe Name, Id)] -> (Expr, NameGen)
createPolyPredAlt' eenv dcpat ng is =
    let
        predApps = mapMaybe (createPolyPredAlt'' is) dcpat
    in
    (foldr (\e e' -> App (
                            App (mkAnd eenv)
                            e
                        ) e') (mkTrue) predApps, ng)

createPolyPredAlt'' :: [(Maybe Name, Id)] -> Id -> Maybe Expr
createPolyPredAlt'' typePreds i@(Id _ (TyVar (Id n _))) =
    case lookup (Just n) typePreds of
        Just f -> Just $ App (Var f) (Var i)
        Nothing -> Nothing
createPolyPredAlt'' _ _ = Nothing



-- | createHigherOrderWrapper
-- This generates function to impose asserts on the input and output of higher
-- order functions.  For each function in a higher order function signature:
--      f :: (a_1 -> ... -> a_n -> b) -> ... -> c
-- we autogenerate a function:
--      wrapper :: (a_1 -> ... -> a_n -> b -> Bool)
--              -> (a_1 -> ... -> a_n -> b) -> a_1 -> ... -> a_n -> b
createHigherOrderWrappers :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, NameGen, Wrappers)
createHigherOrderWrappers eenv tenv ng =
    let
        types = nub $ argTypesTEnv tenv ++ E.higherOrderExprs eenv
    in
    createFuncs eenv ng (zip (repeat ()) types) []
        (const $ Name "wrapper" Nothing 0)
        createHigherOrderWrapperExpr
        storeWrapper

createHigherOrderWrapperExpr :: NameGen -> [((), Name, Type)] -> () -> Type -> (Expr, NameGen)
createHigherOrderWrapperExpr ng _ _ t =
    let
        predType = appendType t TyBool

        wrapperT = [(Just "pred", Nothing, predType), (Just "higher", Nothing, t)]
                   ++ zip3 (repeat Nothing) (repeat Nothing) (init $ splitTyFuns t)
    in
    mkLamBindings ng wrapperT $ \ng' wr -> createHigherOrderWrapperExpr' ng' wr

createHigherOrderWrapperExpr' :: NameGen -> [(Maybe String, Id)] -> (Expr, NameGen)
createHigherOrderWrapperExpr' ng ts' =
    let
        pre:higher:ts = map snd ts'

        higherCall = mkApp . map Var $ higher:ts

        (higherId, ng') = freshId (typeOf higherCall) ng

        predCall = mkApp . map Var $ pre:ts ++ [higherId]

        a = Assume predCall (Var higherId)

        letExpr = Let [(higherId, higherCall)] a
    in
    (letExpr, ng')

storeWrapper :: Wrappers -> () -> Type -> Name -> Expr -> Wrappers
storeWrapper w _ t n e = (t, Id n (typeOf e)):w

isStringSpecial :: String -> Bool
isStringSpecial = (flip elem) special_names
  where
    special_names = ["[]", "~", "~~"]

isNameSpecial :: Name -> Bool
isNameSpecial (Name n _ _) = isStringSpecial n

isIdSpecial :: Id -> Bool
isIdSpecial (Id n _) = isNameSpecial n

isTypeSpecial :: Type -> Bool
isTypeSpecial (TyVar i) = isIdSpecial i
isTypeSpecial (TyConApp n _) = isNameSpecial n
isTypeSpecial _ = False
