-- | Adds the Ord typeclass into the Num typeclass.
-- We need this to work with refinements like:
--
-- @
-- {-@ sub :: Num a => {x:a | x > 0} -> {y:a | y >= 0} @-}
-- @
--
-- which only have a prerequisite of Num, but use Ord functions in the refinement.
-- Not all Num types have an Ord instance. However, we will only try
-- to extact it in LH refinement types, and LH only allows Num/Ord to be
-- used with Ints or Integers. So this is perfectly safe.

module G2.Liquid.AddOrdToNum (addOrdToNum) where

import G2.Language
import G2.Language.Monad
import G2.Liquid.Types

-- | Adds an extra field to the Num dict, which contains the Ord
-- dict for the corresponding type.  Updates all other code accordingly.
-- Of course, there might be types that have a Num instance, but no Ord
-- instance.  These types dicts have the field filled in with Prim Undefined
addOrdToNum :: LHStateM ()
addOrdToNum = do
    tc <- typeClasses
    lh_tc <- lhRenamedTCM
    num <- numTCM

    -- Rewrite dictionary declaration
    let tcd = lookupTCDicts num tc
        lh_tcd = lookupTCDicts num lh_tc
    case (tcd, lh_tcd) of
        (Just tcd', Just lh_tcd') -> do
            mapM_ (uncurry (addOrdToNumDictDec lookupE insertE)) tcd'
            mapM_ (uncurry (addOrdToNumDictDec lookupMeasureM insertMeasureM)) lh_tcd'
        _ -> return ()

    -- Rewrite case statements
    mapME addOrdToNumCase
    mapMeasuresM addOrdToNumCase

    -- Rewrite the types of Num DataCons
    mapME changeNumType
    mapMeasuresM changeNumType

    -- Update Type Environment
    changeNumTypeEnv

    -- Create a function to extract the Ord Dict
    ordDictFunc

addOrdToNumDictDec :: (Name -> LHStateM (Maybe Expr))
                   -> (Name -> Expr -> LHStateM ())
                   -> Type
                   -> Id
                   -> LHStateM ()
addOrdToNumDictDec lkup insert t (Id n _) = do
    ord <- ordTCM

    me <- lkup n

    case me of
        Just e -> do
            ordD <- lookupTCDictTC ord t
            let ordD' = maybe (Prim Undefined TyBottom) Var ordD

            e' <- insertInLamsE (\_ e'' -> return (App e'' ordD')) e

            insert n e'
        Nothing -> return ()

addOrdToNumCase :: Expr -> LHStateM Expr
addOrdToNumCase = modifyASTsM addOrdToNumCase'

addOrdToNumCase' :: Expr -> LHStateM Expr
addOrdToNumCase' ce@(Case e i@(Id _ t) a@[Alt (DataAlt dc is) ae])
    | (TyCon n ts) <- tyAppCenter t = do
        num <- numTCM
        ord <- ordTCM

        let ordT = mkTyApp (TyCon ord ts:tyAppArgs t)

        if num == n then do
            ordI <- freshIdN ordT
            let is' = is ++ [ordI]
            return (Case e i [Alt (DataAlt dc is') ae])
        else return (Case e i a)
    | otherwise = return ce
addOrdToNumCase' e = return e

changeNumType :: Expr -> LHStateM Expr
changeNumType e = do
    num <- numTCM
    modifyASTsM (changeNumType' num) e

changeNumType' :: Name -> Expr -> LHStateM Expr
changeNumType' num d@(Data dc)
    | (TyCon n _) <- tyAppCenter $ returnType dc
    , num == n = return . Data =<< changeNumTypeDC dc
    | otherwise = return d
changeNumType' num ce@(Case e i@(Id n _) [Alt (DataAlt dc is) ae])
    | num == n = do
        dc' <- changeNumTypeDC dc
        return (Case e i [Alt (DataAlt dc' is) ae])
    | otherwise = return ce
changeNumType' _ e = return e

changeNumTypeDC :: DataCon -> LHStateM DataCon
changeNumTypeDC (DataCon n t) = do
    t' <- changeNumTypeType Nothing t
    return (DataCon n t')

changeNumTypeType :: Maybe Id -> Type -> LHStateM Type
changeNumTypeType _ (TyForAll b@(NamedTyBndr i) t) = return . TyForAll b =<< changeNumTypeType (Just i) t
changeNumTypeType i (TyForAll b t) = return . TyForAll b =<< changeNumTypeType i t
changeNumTypeType i (TyFun t t') = return . TyFun t =<< changeNumTypeType i t'
changeNumTypeType i t = do
    ord <- ordTCM
    let ordT = TyCon ord TYPE

    case i of
        Just i' -> return $ TyFun (TyApp ordT (TyVar i')) t
        Nothing -> return (TyFun ordT t)

changeNumTypeEnv :: LHStateM ()
changeNumTypeEnv = do
    num <- numTCM

    adt <- lookupT num

    case adt of
        Just adt'@(DataTyCon {data_cons = [dc]}) -> do
            dc' <- changeNumTypeDC dc
            insertT num $ adt' {data_cons = [dc']}
        _ -> return ()

-- Must be called after updating the TypeEnv, with changeNumTypeEnv, so that
-- the Num DataCon has it's correct type
ordDictFunc :: LHStateM ()
ordDictFunc = do
    num <- numTCM
    let numT = TyCon num TYPE

    numDC <- lookupT num
    let [numDC'] = case numDC of
                    Just ndc -> dataCon ndc
                    Nothing -> error "ordDictFunc: No NumDC"

    let numA = dataConArgs numDC'

    lamI <- freshIdN numT
    caseI <- freshIdN numT

    binds <- freshIdsN numA
    let cOrdBIs = last binds

    let e = Lam TermL lamI $ Case (Var lamI) caseI [Alt (DataAlt numDC' binds) (Var cOrdBIs)]

    (Id n _) <- lhNumOrdM
    insertE n e

    return ()
