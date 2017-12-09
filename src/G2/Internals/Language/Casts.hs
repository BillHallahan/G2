{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Language.Casts where

import G2.Internals.Language.AST
import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Language.Typing

-- | unsafeElimCast
-- Removes all casts from the expression.  Makes no guarentees about the type
-- correctness of the resulting expression.  In particular, the expression
-- is likely to not actually type correctly if it contains variables that
-- are mapped in the Expression Environment
unsafeElimCast :: ASTContainer m Expr => m -> m
unsafeElimCast = modifyASTsFix unsafeElimCast'

unsafeElimCast' :: Expr -> Expr
unsafeElimCast' (Cast e (t1 :~ t2)) = replaceASTs t1 t2 e
unsafeElimCast' e = e

-- | splitCast
-- Given a function cast from (t1 -> t2) to (t1' -> t2'), decomposes it to two
-- seperate casts, from t1 to t1', and from t2 to t2'.  Given a cast (t1 ~ t2)
-- where t1 is a NewTyCon N t3 such that t2 /= t3, changes the cast to be
-- (t1 ~ t3) (t3 ~ t2).
-- Given any other expression, acts as the identity function
splitCast :: NameGen -> Expr -> (Expr, NameGen)
splitCast ng (Cast e ((TyFun t1 t2) :~ (TyFun t1' t2'))) =
    let
        (i, ng') = freshId t1 ng

        e' = Lam i $ 
                (Cast 
                    (App 
                        e
                        (Cast (Var i) (t1 :~ t1'))
                    )
                    (t2 :~ t2')
                )
    in
    (e', ng')
splitCast ng e = (e, ng)

-- | simplfyCasts
-- Eliminates redundant casts 
simplifyCasts :: ASTContainer m Expr => m -> m
simplifyCasts = modifyASTsFix simplifyCasts'


simplifyCasts' :: Expr -> Expr
simplifyCasts' e
    | (Cast (Cast e' (t1 :~ _)) (_ :~ t2)) <- e
    -- , t1 == t2
        = Cast e' (t1 :~ t2)
    | (Cast e' (t1 :~ t2)) <- e
    , t2 .:: t1
        = e'
    | otherwise = e

exprInCasts :: Expr -> Expr
exprInCasts (Cast e _) = exprInCasts e
exprInCasts e = e

typeInCasts :: Expr -> Type
typeInCasts = typeOf . exprInCasts