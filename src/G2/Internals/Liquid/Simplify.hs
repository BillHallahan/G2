{-# Language FlexibleContexts #-}

module G2.Internals.Liquid.Simplify ( simplify ) where

import G2.Internals.Language
import G2.Internals.Language.KnownValues
import G2.Internals.Language.Monad
import G2.Internals.Liquid.TCValues
import G2.Internals.Liquid.Types

import Debug.Trace

-- The LH translation generates certain redundant Expr's over and over again.
-- Here we stamp them out.
simplify :: LHStateM ()
simplify = simplifyExprEnv

simplifyExprEnv :: LHStateM ()
simplifyExprEnv = do
	mapME simplifyTrueLams
	mapME simplifyAnds

simplifyTrueLams :: Expr -> LHStateM Expr
simplifyTrueLams e = do
	true <- mkTrueE
	modifyASTsM (simplifyTrueLams' true) e

simplifyTrueLams' :: Expr -> Expr -> LHStateM Expr
simplifyTrueLams' true e@(App (Lam _ _ le) _) = 
	if true == le then return true else return e
simplifyTrueLams' _ e = return e

simplifyAnds :: Expr -> LHStateM Expr
simplifyAnds e = do
	and <- lhAndE
	true <- mkTrueE
	modifyAppTopE (simplifyAnds' and true) e

simplifyAnds' :: Expr -> Expr -> Expr -> LHStateM Expr
simplifyAnds' and true e = do
	let a = unApp e

	case a of
		[e1, e2, e3]
			| e1 == and
			, e2 == true -> trace ("e3") return e3
			| e1 == and
			, e3 == true -> trace ("e2") return e2
			| otherwise -> trace ("e first") return e
		_ -> trace ("e second") return e

-- helpers
fixM :: (Monad m, Eq a) => (a -> m a) -> a -> m a
fixM f e = do
	e' <- f e
	if e == e' then return e else fixM f e'