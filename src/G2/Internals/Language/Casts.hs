{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Language.Casts ( unsafeElimCast
                                   , splitCast
                                   , simplifyCasts
                                   , liftCasts
                                   , exprInCasts
                                   , typeInCasts
                                   )where

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
splitCast ng (Cast e ((TyForAll (NamedTyBndr ni) t2) :~ (TyForAll (NamedTyBndr ni') t2'))) =
    let
        t1 = typeOf ni
        t1' = typeOf ni'

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
splitCast ng c@(Cast e (t1 :~ t2)) =
    if hasFuncType t1 || hasFuncType t2 then (e, ng) else (c, ng)
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

-- | liftCasts
-- Changes casts on functions to casts on non-functional values
-- (As much as possible)
liftCasts :: ASTContainer m Expr => m -> m 
liftCasts = modifyASTsFix liftCasts'

liftCasts' :: Expr -> Expr
liftCasts' a@(App _ _) = liftCasts'' a
liftCasts' e = e

liftCasts'' :: Expr -> Expr
-- liftCasts'' (App (Cast f ((TyFun t1 t2) :~ (TyFun t1' t2'))) e) = 
--     Cast (App f e) (t2 :~ t2')
liftCasts'' (App (Cast f (t1 :~ t2)) e)
    | (TyFun _ t1'') <- inTyForAlls t1
    , (TyFun _ t2'') <- inTyForAlls t2
    , nt1 <- nestTyForAlls t1
    , nt2 <- nestTyForAlls t2 =
        Cast (App f e) ((nt1 t1'') :~ (nt2 t2''))
liftCasts'' a@(App e e') =
    let
        lifted = App (liftCasts'' e) (liftCasts'' e')
    in
    if a == lifted then a else liftCasts'' lifted
liftCasts'' e = e

exprInCasts :: Expr -> Expr
exprInCasts (Cast e _) = exprInCasts e
exprInCasts e = e

typeInCasts :: Expr -> Type
typeInCasts = typeOf . exprInCasts