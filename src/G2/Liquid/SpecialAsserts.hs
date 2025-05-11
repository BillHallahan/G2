{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.SpecialAsserts ( addSpecialAsserts
                                , addTrueAsserts
                                , addTrueAssertsAll
                                , addErrorAssumes
                                , arbErrorTickish
                                , assumeErrorTickish) where

import G2.Liquid.Config
import G2.Language
import qualified G2.Language.KnownValues as KV
import G2.Language.Monad
import G2.Liquid.Types

import qualified Data.HashSet as S
import qualified Data.Text as T

import Debug.Trace
import qualified G2.Language.TyVarEnv as TV


-- | Adds an assert of false to the function called when a pattern match fails
addSpecialAsserts :: LHStateM ()
addSpecialAsserts = do
    pen <- KV.patErrorFunc <$> knownValues
    pe <- lookupE pen

    let e = case pe  of
            Just e2 -> e2
            Nothing -> Prim Undefined TyBottom

    let fc = FuncCall {funcName = pen, arguments = [], returns = Prim Undefined TyBottom}
    
    false <- mkFalseE
    let e' = Assert (Just fc) false e
    
    insertE pen e'

-- | Adds an Assert of True to any function without an assertion already,
-- excluding certain functions (namely dicts) that we never want to abstract
-- Furthermore, expands all Lambdas as much as possible, so that we get all the arguments
-- for the assertion. 
addTrueAsserts :: ExState s m => TV.TyVarEnv -> Name -> m ()
addTrueAsserts tv n = do
    ns <- return . maybe [] varNames =<< lookupE n
    tc <- return . tcDicts =<< typeClasses
    
    let tc' = map idName tc
        ns' = filter (`notElem` tc') ns
    
    mapWithKeyME (addTrueAsserts' tv ns')

addTrueAsserts' :: ExState s m => TV.TyVarEnv -> [Name] -> Name -> Expr -> m Expr
addTrueAsserts' tv ns n e
    | n `elem` ns = addTrueAssert'' tv n e
    | otherwise = return e

addTrueAssert'' :: ExState s m => TV.TyVarEnv -> Name -> Expr -> m Expr 
addTrueAssert'' tv n e = do
    insertInLamsE (\is e' ->
                case e' of
                    Let [(_, _)] (Assert _ _ _) -> return e'
                    _ -> do
                        true <- mkTrueE
                        r <- freshIdN (returnType (typeOf tv e') )

                        more_is <- tyBindings tv e'

                        let fc = FuncCall { funcName = n
                                          , arguments = map Var $ is ++ map snd more_is
                                          , returns = (Var r)}
                            e'' = mkLams more_is $ Let [(r, mkApp $ e':map (Var . snd) more_is)] $ Assert (Just fc) true (Var r)

                        return e''
                ) =<< etaExpandToE (numArgs (typeOf tv e) ) e

tyBindings :: (ExState s m, Typed t) => TV.TyVarEnv -> t -> m [(LamUse, Id)]
tyBindings tv t = do
    let at = spArgumentTypes (typeOf tv t)
    fn <- freshNamesN (length at)
    return $ tyBindings' fn at

tyBindings' :: [Name] -> [ArgType] -> [(LamUse, Id)]
tyBindings' _ [] = []
tyBindings' ns (NamedType i:ts) = (TypeL, i):tyBindings' ns ts
tyBindings' (n:ns) (AnonType t:ts) = (TermL, Id n t):tyBindings' ns ts
tyBindings' [] _ = error "Name list exhausted in tyBindings'"

addTrueAssertsAll :: ExState s m => TV.TyVarEnv -> m ()
addTrueAssertsAll tv = mapWithKeyME (addTrueAssert'' tv)

--- [BlockErrors]
-- | Blocks calling error in the functions specified in the block_errors_in in
-- the Config, by wrapping the errors in Assume False.
addErrorAssumes :: TV.TyVarEnv -> LHConfig -> LHStateM ()
addErrorAssumes tv config = do
    kv <- knownValues
    mapWithKeyME (addErrorAssumes' tv (block_errors_method config) (block_errors_in config) kv)
    lh_kv <- lhKnownValuesM
    mapMeasuresWithKeyM (addErrorAssumes' tv (block_errors_method config) (block_errors_in config) lh_kv)

addErrorAssumes' :: TV.TyVarEnv -> BlockErrorsMethod -> S.HashSet (T.Text, Maybe T.Text) -> KnownValues -> Name -> Expr -> LHStateM Expr
addErrorAssumes' tv be ns kv (Name n m _ _) e = do
    if (n, m) `S.member` ns then addErrorAssumes'' tv be kv (typeOf tv e) e else return e

addErrorAssumes'' :: TV.TyVarEnv -> BlockErrorsMethod -> KnownValues -> Type -> Expr -> LHStateM Expr
addErrorAssumes'' tv be kv _ v@(Var (Id n t))
    | KV.isErrorFunc kv n 
    , be == AssumeBlock = do
        flse <- mkFalseE
        return $ Assume Nothing (Tick assumeErrorTickish flse) v
    | KV.isErrorFunc kv n
    , be == ArbBlock = do
        d <- freshSeededStringN "d"
        let ast = spArgumentTypes t
            rt = returnType t

            lam_it = map (\as -> case as of
                                    AnonType at -> (TermL, Id d at)
                                    NamedType i -> (TypeL, i)) ast
        fr_n <- trace ("ast = " ++ show ast ++ "\nrt = " ++ show rt) freshSeededStringN "t"
 
        flse <- mkFalseE

        return . mkLams lam_it
               . Assume Nothing (Tick assumeErrorTickish flse) 
               . Tick arbErrorTickish
               $ Let [(Id fr_n TYPE, Type rt)] v
addErrorAssumes'' tv be kv (TyForAll _ t) (Lam u i e) = return . Lam u i =<< modifyChildrenM (addErrorAssumes'' tv be kv t) e
addErrorAssumes'' tv be kv (TyFun _ t) (Lam u i e) = return . Lam u i =<< modifyChildrenM (addErrorAssumes'' tv be kv t) e
addErrorAssumes'' tv be kv t e = modifyChildrenM (addErrorAssumes'' tv be kv t) e

arbErrorTickish :: Tickish
arbErrorTickish = NamedLoc (Name "arb_error" Nothing 0 Nothing)

assumeErrorTickish :: Tickish
assumeErrorTickish = NamedLoc (Name "library_error" Nothing 0 Nothing)