{-# LANGUAGE FlexibleContexts #-}

-- | Functionality to check if a symbolic variable is reachable from some expression.
module G2.Language.ReachesSym ( ReachesSymMemoTable
                              , ReachesSym (..)
                              , reachesSymbolic
                              , reachesSymbolicMemo) where

import qualified G2.Language.ExprEnv as E
import G2.Language.Support
import G2.Language.Syntax
import G2.Execution.NormalForms ( normalForm )

import qualified Control.Monad.State as SM
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM

-- Note [Memoization and SWHNF]
-- We memoize our delayability and reaches symbolic values checks.  However, laziness can make this tricky,
-- as a non-SWHNF thunk which includes a "must exec" function or a symbolic variable may be rewritten to a
-- SWHNF value which does not. It is thus possible for a definition for which we returned EXEC to become
-- a definition for which we should return SKIP (the opposite situation cannot occur.)
-- Similarly, an expression which includes a symbolic variable may be rewritten to an expression that does
-- not include a symbolic variable (but not vice versa.)
-- Below, we focus on delayability checks- but the handling for symbolic variables is analogous. 
--
-- Because we search through variable names, we may even have situations like the following:
--
--   x -> 1:ys
--   ys -> 2:zs
--   zs -> ws
--   ws -> f as
--
-- If f is "must exec", then x will be "must exec" as well.  We would like to memoize this result, so that we
-- avoid (potentially expensive) delayabilty checks in the future.  However, now suppose ws is evaluated to reach
-- an empty list, and we update the thunk for ws:
--
--   ws -> []
--
-- Now, x should be skippable.
--
-- To address this, when memoizing a delayability result for some function f, we also record a "checkpoint function" g.
-- A call to g must (1) be reachable from f following only SWHNF definitions, and (b) g's delayability result
-- must be EXEC (at the time the result is memoized.)  These checkpoint values essentially form a linked list from
-- a definition through each successive EXEC function, ending at a "must exec" function.
--
-- When we see a memoized value, we search down through the checkpoint values until we either
-- (1) reach a "must exec" value, in which case we return EXEC
-- or
-- (2) reach a SWHNF definition being used as a checkpoint, at which point we know we must discard the memoized value and recompute.

data ReachesSym = ReachesSym -- ^ A symbolic variable can be reached from the variable definition
                    (Maybe Name) -- ^ Name of a "checkpoint function", see Note [Memoization and SWHNF]
                                 -- Can be Nothing when returned from a SymGen
                | NotReachesSym -- ^ A symbolic variable cannot be reached from the variable definition
type ReachesSymMemoTable = HM.HashMap Name ReachesSym

instance Semigroup ReachesSym where
    NotReachesSym <> NotReachesSym = NotReachesSym
    rs@(ReachesSym _) <> _ = rs
    _ <> rs@(ReachesSym _) = rs

instance Monoid ReachesSym where
    mempty = NotReachesSym

-- | Can evaluating the Expr branch? Or is it fully concrete (including looking through variables.)
reachesSymbolic :: ExprEnv -> Expr -> Bool
reachesSymbolic eenv = fst . reachesSymbolicMemo mempty eenv

-- | Can evaluating the Expr branch? Or is it fully concrete (including looking through variables.)
reachesSymbolicMemo :: ReachesSymMemoTable -> ExprEnv -> Expr -> (Bool, ReachesSymMemoTable)
reachesSymbolicMemo rsmt eenv e = 
    let 
        (res, rsmt') = SM.runState (reachesSymbolic' eenv e) rsmt
        res' = case res of
                    ReachesSym _ -> True
                    NotReachesSym -> False 
    in (res', rsmt')

reachesSymbolic' :: SM.MonadState ReachesSymMemoTable m => ExprEnv -> Expr -> m ReachesSym
reachesSymbolic' eenv = go
    where
        go (SymGen _ _) = return (ReachesSym Nothing)
        go (Var (Id n _)) = do
            let e = E.lookupConcOrSym n eenv
            memo <- SM.get
            case HM.lookup n memo of
                Just NotReachesSym -> return $ NotReachesSym
                Just (ReachesSym n') | checkNotNormalForm memo (Just n) -> return (ReachesSym n')
                _ | Just (E.Conc e') <- e ->  do
                    SM.modify (HM.insert n NotReachesSym)
                    r <- go e'
                    SM.modify (HM.insert n r)
                    -- See Note [Memoization and SWHNF].  For memoization of a ReachesSymbolic result for a function f, we
                    -- want a checkpoint function g that is (a) reachable from f only through SWHNF definitions and (b) returns
                    -- the result ReachesSymbolic.  We thus ensure that we are returning ReachesSymbolic's that fit these
                    -- two conditions
                    let r' = case r of
                                NotReachesSym -> r
                                ReachesSym _ -> if normalForm eenv e' then r else ReachesSym (Just n)

                    return r'
                  | Just (E.Sym _) <- e -> return (ReachesSym (Just n))
                  | otherwise -> return NotReachesSym
        go e = return . mconcat =<< mapM go (children e)

        checkNotNormalForm memo (Just n) | E.isSymbolic n eenv = True
                                         | Just e <- E.lookup n eenv
                                         , not (normalForm eenv e) =
                                            case HM.lookup n memo of
                                                Just (ReachesSym Nothing) -> True
                                                Just (ReachesSym n') -> checkNotNormalForm memo n'
                                                Just NotReachesSym -> False
                                                Nothing -> False
                                         | otherwise = False
        checkNotNormalForm _ Nothing = True