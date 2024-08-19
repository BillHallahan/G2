{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
-- | This module generates functions in the expr_env that walk over the whole structure of an ADT,
-- thus forcing evaluation of the ADT. We call these functions "DeepSeq walkers", or just "walkers."

module G2.Initialization.DeepSeqWalks (createDeepSeqWalks) where

-- Note [Walker function code]
-- An algebraic data type of the form:
--
-- @ data T a1 .. ak = D_1 args1 | ... | D_N argsN @
--
-- Will generate a function of the form:
--
-- @
--   walkT = \a1 -> ... \an
--        -> \(walk_a1 :: a1 -> a1) ->
--           ...
--        -> \(walk_an :: an -> an)
--        -> \(e :: T a1 ... an) ->
--                          case e of { D_1 args1 -> evals1 ; ...; D_N argsN -> evalsN }
-- @
--
-- where each of evals1 to evalsN will recursively walk over args1 to argsN by forcing each argument
-- via a further walk function call, wrapped in a case statement.
-- In general, a walker function will have one "outer case statment", which forces evaluation of the `e` argument passed
-- to walkT, and some number of "inner case statements", to force evaluation of each sub-expression in `e`. 
-- The walk_a1 to walk_an functions are intended to do the job of walk over the polymorphic types.
--
-- As an example, consider the standard `List` type:
--
-- @
--   data List a = a : List a | []
-- @
--
-- The walk function for the List type would be:
--
-- @
--   walkList :: forall a . (a -> a) -> List a -> List a
--   walkList = \a -> \f -> xs -> case xs of                                        -- Outer case statement on walked type
--                                      [] -> []
--                                      (y:ys) -> case f y of                       -- Inner case statement on argument
--                                                  z -> case walkList ys of        -- Inner case statement on argument
--                                                          zs -> z:zs
-- @ 
-- Notice that the expressions with polymorphic type `a` are forced with the passed function `f`, and
-- the list tail is forced with a recursive call to `walkList`.


import G2.Language

import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

type BoundName = Name

createDeepSeqWalks :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, NameGen, Walkers)
createDeepSeqWalks eenv tenv ng =
    let
        tenv' = HM.toList tenv
    in
    createFuncs eenv ng tenv' M.empty (createDeepSeqName . fst) createDeepSeqStore (createDeepSeqExpr tenv)

createDeepSeqName ::  Name -> Name
createDeepSeqName n = Name ("walk" `T.append` nameOcc n) Nothing 0 (spanning n)

-- | Given a type name and definition, and a name for the corresponding walker function,
-- create a mapping in `Walkers` from the type name to the walker function `Id`.
createDeepSeqStore :: (Name, AlgDataTy) -- ^ The type name and definition
                   -> Name -- ^ The walker function name
                   -> Walkers
                   -> Walkers
createDeepSeqStore (n, adt) n' w =
    let
        bi = bound_ids adt
        bn = map TyVar $ bound_ids adt
        bnf = map (\b -> TyFun b b) bn

        dc_t = foldr (const $ TyFun TYPE) TYPE [1..length bi]

        base = TyFun (TyCon n dc_t) (TyCon n dc_t)

        t = foldr TyFun base (bn ++ bnf)
        t' = foldr TyForAll t bi
        i = Id n' t'
    in
    M.insert n i w

type RenameMap = HM.HashMap Name Name

type TyVarWalkersFuncs = [Id]
type TyVarWalkers = [(Name, Id)]

-- | Generates the code for a walker function.
createDeepSeqExpr :: TypeEnv
                  -> Walkers
                  -> (Name, AlgDataTy) -- ^ The type to generate a walker function for.
                  -> NameGen
                  -> (Expr, NameGen)
createDeepSeqExpr tenv w (n, adt) ng =
    let
        bn = bound_ids adt

        -- Fresh names for type lambas
        (bn', ng') = freshNames (length bn) ng
        -- Fresh names for functions to force evaluation of each polymorphic type variable (walk_a1 to walk_an in Note [Walker function code])
        (wbn, ng'') = freshNames (length bn) ng'

        bni = map (flip Id TYPE) bn'
        wbni = zipWith (\b f -> Id f (TyFun (TyVar (Id b TYPE)) (TyVar (Id b TYPE)))) bn' wbn

        (e, ng''') = createDeepSeqCase1 tenv w wbni n bn' adt ng''
    in
    (mkLams (map (TypeL,) bni ++ map (TermL,) wbni) e, ng''')

-- | Creating the "outer case statement" described in Note [Walker function code]
createDeepSeqCase1 :: TypeEnv -> Walkers -> TyVarWalkersFuncs -> Name -> [BoundName] -> AlgDataTy -> NameGen -> (Expr, NameGen)
createDeepSeqCase1 tenv w ti n bn (DataTyCon {data_cons = dc}) ng =
    let
        (i, ng') = freshId (mkFullAppedTyCon n (map (TyVar . flip Id TYPE) bn) TYPE) ng
        (caseB, ng'') = freshId (mkFullAppedTyCon n (map (TyVar . flip Id TYPE) bn) TYPE) ng'

        (alts, ng''') = createDeepSeqDataConCase1Alts tenv w ti n caseB bn ng'' dc

        cs_t = case alts of
                (a:_) -> typeOf a
                _ -> TyBottom

        c = Case (Var i) caseB cs_t alts
    in
    (Lam TermL i c, ng''')
createDeepSeqCase1 _ w ti n bn (NewTyCon {bound_ids = bids, rep_type = t}) ng =
    let
        rm = HM.fromList $ zip (map idName bids) bn

        t' = mkFullAppedTyCon n (map (TyVar . flip Id TYPE) bn) TYPE
        t'' = renames rm t

        (i, ng') = freshId t' ng
        (caseB, ng'') = freshId t'' ng'

        cast = Cast (Var i) (t' :~ t'')

        ti' = zip bn ti
        (e, ng''') = deepSeqFuncCall w ng'' ti' rm (Var caseB)
        e' = Cast e (t'' :~ t')

        alt = Alt Default e'

        c = Case cast caseB t' [alt]
    in
    (Lam TermL i c, ng''')
createDeepSeqCase1 _ _ _ _ _ _ _ = error "createDeepSeqCase1: bad argument passed"

-- | Creating alternatives for the "outer case statement" in Note [Walker function code]
createDeepSeqDataConCase1Alts :: TypeEnv -> Walkers -> TyVarWalkersFuncs -> Name -> Id -> [BoundName] -> NameGen -> [DataCon] -> ([Alt], NameGen)
createDeepSeqDataConCase1Alts _ _ _ _ _ _ ng [] = ([], ng)
createDeepSeqDataConCase1Alts tenv w ti n i bn ng (dc@(DataCon _ dc_t):xs) =
    let
        t_ids = leadingTyForAllBindings $ PresType dc_t
        rm' = HM.fromList (zip (map idName t_ids) bn)
        dct = bindTypes rm' (Data dc)

        ti' = zip bn ti

        ts = renames rm' $ anonArgumentTypes dc
        (binds, ng') = freshIds ts ng

        (e, ng'') = createDeepSeqDataConCase2 tenv w ti' rm' binds ng' dct
        alt = Alt (DataAlt dc binds) e

        (alts, ng''') = createDeepSeqDataConCase1Alts tenv w ti n i bn ng'' xs
    in
    (alt:alts, ng''')

bindTypes :: RenameMap -> Expr -> Expr
bindTypes rm e =
    let
        t_ids = leadingTyForAllBindings e
        tb = map (Type . TyVar . renames rm) t_ids
    in
    foldl' App e tb

-- | Creating the "inner case statement" in Note [Walker function code]
createDeepSeqDataConCase2 :: TypeEnv -> Walkers -> TyVarWalkers -> RenameMap -> [Id] -> NameGen -> Expr -> (Expr, NameGen)
createDeepSeqDataConCase2 _ _ _ _ [] ng e = (e, ng)
createDeepSeqDataConCase2 tenv w ti rm (i:is) ng e
    | t@(TyCon n _) <- typeOf i 
    , Just (NewTyCon {rep_type = rt}) <- HM.lookup n tenv =
    let
        (i', ng') = freshId rt ng

        (b, ng'') = deepSeqFuncCall w ng' ti rm (Var i)
        bCast = Cast b (t :~ rt)

        vi = Var i'
        viCast = Cast vi (rt :~ t)

        (ae, ng''') = createDeepSeqDataConCase2 tenv w ti rm is ng'' (App e viCast)
    in
    (Case bCast i' (typeOf e) [Alt Default ae], ng''')
    | otherwise =
        let
            (i', ng') = freshId (typeOf i) ng

            (b, ng'') = deepSeqFuncCall w ng' ti rm (Var i)

            (ae, ng''') = createDeepSeqDataConCase2 tenv w ti rm is ng'' (App e (Var i'))
        in
        (Case b i' (typeOf ae) [Alt Default ae], ng''')

-- | Creates code to call the appropriate walker function for the passed Expr
deepSeqFuncCall :: Walkers
                -> NameGen
                -> TyVarWalkers
                -> RenameMap
                -> Expr -- ^ The Expr to force via a walker function
                -> (Expr, NameGen)
deepSeqFuncCall w ng ti rm e =
    case deepSeqFunc w ng ti rm e of
        Just (e', ng') -> (App e' e, ng')
        Nothing -> (e, ng)

deepSeqFunc :: Typed t => Walkers -> NameGen -> TyVarWalkers -> RenameMap -> t -> Maybe (Expr, NameGen)
deepSeqFunc w ng ti rm e
    | t <- typeOf e
    , TyCon n _ <- tyAppCenter t
    , ts <- tyAppArgs t
    , Just f <- M.lookup n w =
        let
            as = map Type $ renames rm ts
            as' = map (walkerFunc w ti rm) ts
        in
        Just $ (foldl' App (Var f) (as ++ as'), ng)
    | t@(TyFun _ _) <- typeOf e =
        let
            (a_in, ng') = freshId t ng

            tys = anonArgumentTypes e
            (f_is, ng'') = freshIds tys ng' 
            
            cll = mkApp $ Var a_in:map Var f_is
            let_cll = Let (zip f_is $ map (SymGen SNoLog) tys) cll

            ds_type = typeOf ds_cll

            (ds_cll, ng''') = deepSeqFuncCall w ng'' ti rm let_cll
            (bnd, ng'''') = freshId ds_type ng'''

            (lam_ids, ng''''') = freshIds tys ng''''

            cse = Case ds_cll bnd ds_type [Alt Default $ mkLams (zip (repeat TermL) lam_ids) (Var bnd)]
        in
        Just (Lam TermL a_in cse, ng''''')
    | (TyVar (Id n _)) <- typeOf e
    , Just f <- lookup n ti =
       Just (Var f, ng)
    | otherwise = Nothing

walkerFunc :: Walkers -> TyVarWalkers -> RenameMap -> Type -> Expr
walkerFunc _ ti _ (TyVar (Id n _))
    | Just tyF <- lookup n ti = 
        Var tyF
walkerFunc w ti rm t
    | TyCon n _ <- tyAppCenter t
    , ts <- tyAppArgs t
    , Just f <- M.lookup n w =
        let
            as = renames rm $ map Type ts
            ft = renames rm . map fst $ mapMaybe (deepSeqFunc w undefined ti rm . PresType) ts
        in
        foldl' App (Var f) (as ++ ft)
walkerFunc _ ni _ t = error $ "walkerFunc: bad argument passed" ++ "\n" ++ show ni ++ "\n" ++ show t
