module G2.Execution.FuncConstraints where

-- Note [Solving Function Constraints]
-- Function constraints have the forms:
--
--   preconditions => f a1 ... ak = r
--
-- where:
-- * preconditions is a conjunction and disjunction of equalities/inequalities between integer variables and concrete integers, 
-- * f is a symbolic function
-- * a1 ... ak are arguments, r is the return value.
--
-- Typically, the set of preconditions for each constraint will be empty in an initial problem;
-- however, the procedure to solve a set of function constraints will generate function constraints with preconditions.
--
-- To solve a set of function constraints, we (a) take the following steps 1 to 3 repeatedly and (b) take step (4) if none of these earlier rules apply:
-- 1) We check if all return values for a given function are indistinguishable (see Note [Distinguishability], below.)
--    If all return values are indistinguishable, we simply instantiate the function to be a constant function, and
--    remove the constraints.
-- 2) We check if there is a function f such that the i^th argument x of that function is in WHNF in all constraints.
--    If there is, we instantiate this function to branch on that argument. Each of the k branches then calls a corresponding newly generated
--    symbolic function f1...fk. This function is passed all arguments of f EXCEPT for x. If x has an ADT type, each function is also passed all
--     arguments from the constructor.  The original constraints are then rewritten in terms of f1...fk.
--
--    For example, suppose we have:
--        f (x:xs) 4 = 6
--        f (y:ys) e = 10 -- ^ For some expression e
--        f [] 6 = 22
--        f [] 19 = 25
--    The first argument to each f is in WHNF, so we instantiate f to branch on that argument:
--        f = \y z -> case y of
--                      [] -> f1 z
--                      w:ws -> f2 w ws z
--    We then rewrite the constraints to:
--        f2 x xs 4 = 6
--        f2 y ys e = 10
--        f1 6 = 22
--        f1 19 = 25
--    (Note that this step might be done repeatedly- for example, in the above, we can now split on the first argument of f1)
-- 3) We look for arguments that are symbolic variables. We then instantiate these symbolic variables to case expressions
--    that branch on a fresh integer variable to choose a constructor with fresh symbolic arguments. For example, if we have:
--        f (xs :: [Int]) = 7
--    where xs is symbolic, we introduce a fresh Int n, and instantiate xs to:
--       xs = case n of
--                1 -> []
--                2 -> y:ys -- y, ys fresh symbolic variables
--    We add a path constraint that `1 <= n <= 2`.
--    We then unroll the constraint on f into separate constraints for each possible constructor, with corresponding preconditions.
-- For example, the constraint above becomes:
--        n = 1 => f [] = 7
--        n = 2 => f (y:ys) = 7
--
-- If none of steps (1) to (3) apply, we move on to step (4):
-- 4) Since none of (1) to (3) apply, for each argument of a function f, there must be at least one constraint
-- where that argument is not in WHNF and is not a symbolic variable.  For instance:
--                 f 9  7  = 6
--        n = 1 => f 1  4  = 2
--        n = 1 => f e1 4  = 5
--        n = 2 => f 8  e2 = 10
--        where e1, e2 are non-SWHNF expressions.
-- Here, we cannot branch on any of the arguments via step (2), because e1 blocks branching on the first argument, and e2 blocks branching on the second argument.
-- However, if we knew that either n = 1 or n = 2, then branching would be possible. Thus, we choose one of these constraints, and rewrite f.
-- Suppose we choose `n = 1`.  We instantiate f to be:
--        f x y = case n = 1 of
--                      True -> f2 y -- Notice we exclude the first argument, because it is e1 in one of the constraints when `n = 1`
--                      False -> f3 x y
-- We then rewrite accordingly:
--        n = 1 =>  f2 7  = 6
--        n /= 1 => f3 9 7  = 6
--        n = 1 =>  f2 4  = 2
--        n = 1 =>  f2 4  = 5
--        n = 2 =>  f3 8 e2 = 10
-- We now return to rules (1) to (3). Notice that we will actually not be able to solve for `n = 1`/f2, because `f2 4 = 2` and `f2 4 = 5` is a constradiction.
-- However, we will be able to solve for `n = 2` and `f3`.

-- Note [Delaying Step 4]
-- Read Note [Solving Function Constraints] (above) first.
-- A natural question is why we delay step 4 until after none of steps 1 to 3 apply. To answer this, consider:
--        n = 1 => f (x:xs) e1 = 1
--        n = 1 => f []     4  = 2
--        n = 1 => f []     6  = 5
--        n = 2 => f []     6 =  3
--        n = 2 => f []     6 =  4
-- To solve the above, we must have `n = 1`, otherwise we have `f [] 6 = 3` and `f [] 6 = 4`. Notice, though, that if we apply step (4) immediately, we get:
--        f a b = case n = 1 of
--                    True -> f2 a
--                    False -> f3 a b
-- Which gets us new constraints:
--        n = 1 => f2 (x:xs)   = 1
--        n = 1 => f2 []       = 2
--        n = 1 => f2 []       = 5
--        n = 2 => f3 []     6 =  3
--        n = 2 => f3 []     6 =  4
-- This is now unsatisfiable, because we have `f2 [] = 2` and `f2 [] = 5`. Thus, we instead must branch the function based on list constructor:
--        f a b = case a of
--                    [] -> f3 b
--                    c:ds -> f4 c ds b
--  getting new constraints:
--        n = 1 => f3 e1 = 1
--        n = 1 => f4 4  = 2
--        n = 1 => f4 6  = 5
--        n = 2 => f4 6 =  3
--        n = 2 => f4 6 =  4
-- f3 can now be handled by step (1) and f4 by step (2).

data Precond = Id :== Int | Id :/= Int

data FuncConstraint =
    FC { func_name :: Name
       , preconds :: [Precond]
       , args :: [Expr]
       , ret :: Expr
       }

-- Note [Distinguishability]
-- We say two expressions are "distinguishable" if they are (partially) fully reduced,
-- and can be seen to be syntactically different based on the exposed constructors/literals.
-- Two expressions are "indistinguishable" if they are not distinguishable.
-- The "indistinguishable region" of two expressions is the reduced pattern of constructors/literals
-- over which those expressions are indistinguishable.

-- | Returns Just the indistinguishable region of two expressions (looking through variables),
-- or Nothing if the expressions are distinguishable.
--
-- See  Note [Distinguishability].
indistinguishableRegions :: ExprEnv -> Expr -> Expr -> Maybe Expr
indistinguishableRegions eenv e1_ e2_ = go (inlineVars eenv e1_) (inlineVars eenv e2_)
    where      
        -- (Possibly) indistinguishable matching
        go (App e1 e2) (App e1' e2') = liftM2 App (go e1 e1') (go e2 e2')
        go dc@(Data (DataCon { dc_name = n1 })) (Data (DataCon { dc_name = n2 })) | n1 == n2 = Just dc
                                                                                  | otherwise = Nothing
        go t@(Type t1) (Type t2) | t1 == t2 = Just t
                                 | otherwise = Nothing
        go l@(Lit l1) (Lit l2) | l1 == l2 = Just l
                               | otherwise = Nothing

        -- Distinguishable, so return Nothing
        go (Data _) e@(App _ _) | Data _:_ <- unApp e = Nothing
        go e@(App _ _) (Data _) | Data _:_ <- unApp e = Nothing
        go (Data _) (Type _) = Nothing
        go (Type _) (Data _) = Nothing

        go _ _ = Just $ Prim Undefined TyBottom

        -- go a@(App _ _) _ | Data _:_ <- unApp a