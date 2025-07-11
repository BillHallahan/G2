{-# LANGUAGE FlexibleContexts #-}

module G2.Language.Casts ( unsafeElimCast
                         , unsafeElimOuterCast
                         , splitCast
                         , simplifyCasts
                         , liftCasts
                         , exprInCasts
                         , typeInCasts
                         ) where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax
import G2.Language.Typing
import Data.Monoid as M
import qualified G2.Language.TyVarEnv as TV 
import Debug.Trace

containsCast :: ASTContainer m Expr => m -> M.Any
containsCast = evalASTs isCast

isCast :: Expr -> M.Any
isCast (Cast _ _) = Any True
isCast _ = Any False

-- | Removes all casts from the expression.  Makes no guarantees about the type
-- correctness of the resulting expression.  In particular, the expression
-- is likely to not actually type correctly if it contains variables that
-- are mapped in the Expression Environment
unsafeElimCast :: ASTContainer m Expr => m -> m
unsafeElimCast e = if (getAny $ containsCast e) then modifyContainedASTs unsafeElimOuterCast e else e

unsafeElimOuterCast :: Expr -> Expr
unsafeElimOuterCast (Cast e (t1 :~ t2)) = replaceASTs t1 t2 e
unsafeElimOuterCast e = e

-- | Given a function cast from (t1 -> t2) to (t1' -> t2'), decomposes it to two
-- seperate casts, from t1' to t1, and from t2 to t2'.
-- Note that the direction of the cast differs intentionally.  Consider:
--
-- @ newtype Money = Money Int
--   newtype Person = Person String 
--   f :: String -> Money
--   p :: Person
--   
--   g = coerce (f :: Person -> Int) p
--   g' = coerce (f (coerce p :: String)) :: Int
-- @
-- g and g' are equivalent. To shift the coercion from a function coercion to coercions on the inputs and outputs,
-- we keep the same result type coercion, but have to flip the argument coercion. 
--
-- In addition to splitting function casts, given a cast (t1 ~ t2) where t1 is a NewTyCon N t3 such that t2 /= t3,
-- we change the cast to be (t1 ~ t3) (t3 ~ t2).
--
-- Given any other expression, acts as the identity function
splitCast :: TV.TyVarEnv -> NameGen -> Expr -> (Expr, NameGen)
splitCast _ ng (Cast e ((TyFun t1 t2) :~ (TyFun t1' t2'))) =
    let
        (i, ng') = freshId t1 ng

        e' = Lam TermL i $ 
                (Cast 
                    (App 
                        e
                        (Cast (Var i) (t1' :~ t1))
                    )
                    (t2 :~ t2')
                )
    in
    (e', ng')
splitCast tv ng (Cast e ((TyForAll ni t2) :~ (TyForAll ni' t2'))) =
    let
        t1 = typeOf tv ni
        t1' = typeOf tv ni'

        (i, ng') = freshId t1 ng

        e' = Lam TypeL i $ 
                (Cast
                    (App 
                        e
                        (Cast (Var i) (t1 :~ t1'))
                    )
                    (rename (idName ni) (idName i) t2 :~ rename (idName ni') (idName i) t2')
                )
    in
    (e', ng')
-- splitCast ng c@(Cast e (t1 :~ t2)) =
--     if hasFuncType (PresType t1) || hasFuncType (PresType t2) then (e, ng) else (c, ng)
splitCast _ ng e = (e, ng)

-- | Eliminates redundant casts.
simplifyCasts :: ASTContainer m Expr => m -> m
simplifyCasts = modifyASTsFix simplifyCasts'

simplifyCasts' :: Expr -> Expr
simplifyCasts' e
    | (Cast (Cast e' (t1 :~ _)) (_ :~ t2)) <- e
        = Cast e' (t1 :~ t2)
    | (Cast e' (t1 :~ t2)) <- e
    , t2 .:: t1
        = e'
    | otherwise = e

-- | Changes casts on functions to casts on non-functional values
-- (As much as possible)
liftCasts :: ASTContainer m Expr => m -> m 
liftCasts = simplifyCasts . modifyASTsFix liftCasts'

liftCasts' :: Expr -> Expr
liftCasts' a@(App _ _) =  liftCasts'' a
liftCasts' e = e

liftCasts'' :: Expr-> Expr
liftCasts'' (App (Cast f (TyForAll b1 t1 :~ TyForAll b2 t2)) e@(Type t)) =
    let
        t1' = retype b1 t t1
        t2' = retype b2 t t2
    in
    Cast (App f e) (t1' :~ t2')
liftCasts'' (App (Cast f (TyFun _ t2 :~ TyFun _ t2')) e) =
    Cast (App f e) (t2 :~ t2')
liftCasts'' a@(App e e') =
    let
        a' = App (liftCasts'' e) (liftCasts'' e')
    in
    if a == a' then a else liftCasts'' a'
liftCasts'' e = e

-- | Extracts an `Expr` nested in one or more Casts.
exprInCasts :: Expr -> Expr
exprInCasts (Cast e _) = exprInCasts e
exprInCasts e = e

-- | Gets the type of an `Expr`, ignoring Casts.
typeInCasts :: TV.TyVarEnv -> Expr -> Type
typeInCasts tv e = typeOf tv $ exprInCasts e
