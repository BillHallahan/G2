module G2.Language.Approximation where

import G2.Execution.NormalForms
import G2.Language.Expr
import qualified G2.Language.ExprEnv as E
import G2.Language.Naming
import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Typing as T

import Control.Monad.Extra
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM

type GenerateLemma t l = State t -> State t -> (HM.HashMap Id Expr, HS.HashSet (Expr, Expr)) -> Expr -> Expr -> l
type Lookup t = Name -> State t -> Maybe E.ConcOrSym

type MRCont t l =  State t
                -> State t
                -> HS.HashSet Name
                -> (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
                -> Bool -- ^ indicates whether this is part of the "active expression"
                -> [(Name, Expr)] -- ^ variables inlined previously on the LHS
                -> [(Name, Expr)] -- ^ variables inlined previously on the RHS
                -> Expr
                -> Expr
                -> Either [l] (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))

-- s1 is the old state, s2 is the new state
-- If any recursively-defined functions or other expressions manage to slip
-- through the cracks with the other mechanisms in place for avoiding infinite
-- inlining loops, then we can handle them here by keeping track of all of the
-- variables that have been inlined previously.
-- Keeping track of inlinings by adding to ns only lets a variable be inlined
-- on one side.  We need to have two separate lists of variables that have been
-- inlined previously so that inlinings on one side do not block any inlinings
-- that need to happen on the other side.
-- Whenever a variable is inlined, we record the expression that was on the
-- opposite side at the time.  Under the original system, a variable could not
-- be inlined at all on one side in any sub-expressions that resulted from an
-- inlining of it, and that was too restrictive.  Under the current system,
-- repeated inlinings of a variable are allowed as long as the expression on
-- the opposite side is not the same as it was when a previous inlining of the
-- same variable happened.
-- When we make the two sides for a new lemma, if the two expressions
-- contain any variables that aren't present in the expression environment,
-- we add them to the expression environment as non-total symbolic
-- variables.  This can happen if an expression for a lemma is a
-- sub-expression of a Case branch, a Let statement, or a lambda expression
-- body.  It is possible that we may lose information about the variables
-- because of these insertions, but this cannot lead to spurious
-- counterexamples because these insertions apply only to lemmas and lemmas
-- are not used for counterexample generation.
moreRestrictive' :: MRCont t l
                 -> GenerateLemma t l
                 -> Lookup t
                 -> State t
                 -> State t
                 -> HS.HashSet Name
                 -> (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
                 -> Bool -- ^ indicates whether this is part of the "active expression"
                 -> [(Name, Expr)] -- ^ variables inlined previously on the LHS
                 -> [(Name, Expr)] -- ^ variables inlined previously on the RHS
                 -> Expr
                 -> Expr
                 -> Either [l] (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
moreRestrictive' mr_cont gen_lemma lkp s1@(State {expr_env = h1}) s2@(State {expr_env = h2}) ns hm active n1 n2 e1 e2 =
  case (e1, e2) of
    (Var i, _) | m <- idName i
               , not $ HS.member m ns
               , not $ (m, e2) `elem` n1
               , Just (E.Conc e) <- lkp m s1 ->
                 moreRestrictive' mr_cont gen_lemma lkp s1 s2 ns hm active ((m, e2):n1) n2 e e2
    (_, Var i) | m <- idName i
               , not $ HS.member m ns
               , not $ (m, e1) `elem` n2
               , Just (E.Conc e) <- lkp m s2 ->
                 moreRestrictive' mr_cont gen_lemma lkp s1 s2 ns hm active n1 ((m, e1):n2) e1 e
    (Var i1, Var i2) | HS.member (idName i1) ns
                     , idName i1 == idName i2 -> Right hm
                     | HS.member (idName i1) ns -> Left []
                     | HS.member (idName i2) ns -> Left []
    (Var i, _) | Just (E.Sym _) <- lkp (idName i) s1
               , (hm', hs) <- hm
               , Nothing <- HM.lookup i hm' -> Right (HM.insert i (inlineEquiv lkp [] s2 ns e2) hm', hs)
               | Just (E.Sym _) <- lkp (idName i) s1
               , Just e <- HM.lookup i (fst hm)
               , e == inlineEquiv lkp [] s2 ns e2 -> Right hm
               -- this last case means there's a mismatch
               | Just (E.Sym _) <- lkp (idName i) s1 -> Left []
               | not $ (idName i, e2) `elem` n1
               , not $ HS.member (idName i) ns -> error $ "unmapped variable " ++ (show i)
    (_, Var i) | Just (E.Sym _) <- lkp (idName i) s2 -> Left [] -- sym replaces non-sym
               | not $ (idName i, e1) `elem` n2
               , not $ HS.member (idName i) ns -> error $ "unmapped variable " ++ (show i)
  
    (App f1 a1, App f2 a2) | Right hm_fa <- moreResFA -> Right hm_fa
                           -- don't just choose the minimal conflicting expressions
                           -- collect all suitable pairs for potential lemmas
                           | not (hasFuncType e1)
                           , not (hasFuncType e2)
                           , not active
                           , Var (Id m1 _):_ <- unApp (modifyASTs stripTicks e1)
                           , Var (Id m2 _):_ <- unApp (modifyASTs stripTicks e2)
                           , nameOcc m1 == nameOcc m2
                           , Left lems <- moreResFA ->
                                Left $ (gen_lemma s1 s2 hm e1 e2):lems
                            | Left (_:_) <- moreResFA -> moreResFA
        where
            moreResFA = do
                hm_f <- moreRestrictive' mr_cont gen_lemma lkp s1 s2 ns hm active n1 n2 f1 f2
                moreRestrictive' mr_cont gen_lemma lkp s1 s2 ns hm_f False n1 n2 a1 a2
    -- These two cases should come after the main App-App case.  If an
    -- expression pair fits both patterns, then discharging it in a way that
    -- does not add any extra proof obligations is preferable.
    (App _ _, _) | e1':_ <- unApp e1
                 , (Prim _ _) <- inlineTop lkp [] s1 e1'
                 , T.isPrimType $ typeOf e1
                 , T.isPrimType $ typeOf e2
                 , isSWHNF $ (s2 { curr_expr = CurrExpr Evaluate e2 }) ->
                                  let (hm', hs) = hm
                                  in Right (hm', HS.insert (inlineFull lkp [] s1 e1, inlineFull lkp [] s2 e2) hs)
    (_, App _ _) | e2':_ <- unApp e2
                 , (Prim _ _) <- inlineTop lkp [] s2 e2'
                 , T.isPrimType $ typeOf e2
                 , T.isPrimType $ typeOf e1
                 , isSWHNF $ (s1 { curr_expr = CurrExpr Evaluate e1 }) ->
                                  let (hm', hs) = hm
                                  in Right (hm', HS.insert (inlineFull lkp [] s1 e1, inlineFull lkp [] s2 e2) hs)
    -- We just compare the names of the DataCons, not the types of the DataCons.
    -- This is because (1) if two DataCons share the same name, they must share the
    -- same type, but (2) "the same type" may be represented in different syntactic
    -- ways, most significantly bound variable names may differ
    -- "forall a . a" is the same type as "forall b . b", but fails a syntactic check.
    (Data (DataCon d1 _), Data (DataCon d2 _))
                                  | d1 == d2 -> Right hm
                                  | otherwise -> Left []
    -- We neglect to check type equality here for the same reason.
    (Prim p1 _, Prim p2 _) | p1 == p2 -> Right hm
                           | otherwise -> Left []
    (Lit l1, Lit l2) | l1 == l2 -> Right hm
                     | otherwise -> Left []
    (Lam lu1 i1 b1, Lam lu2 i2 b2)
                | lu1 == lu2
                , i1 == i2 ->
                  let ns' = HS.insert (idName i1) ns
                  -- no need to insert twice over because they're equal
                  in moreRestrictive' mr_cont gen_lemma lkp s1 s2 ns' hm active n1 n2 b1 b2
                | otherwise -> Left []
    -- ignore types, like in exprPairing
    (Type _, Type _) -> Right hm
    -- only works if both binding lists are the same length
    (Let binds1 e1', Let binds2 e2') ->
                let pairs = (e1', e2'):(zip (map snd binds1) (map snd binds2))
                    ins (i_, e_) h_ = E.insert (idName i_) e_ h_
                    h1_ = foldr ins h1 binds1
                    h2_ = foldr ins h2 binds2
                    s1' = s1 { expr_env = h1_ }
                    s2' = s2 { expr_env = h2_ }
                    mf hm_ (e1_, e2_) = moreRestrictive' mr_cont gen_lemma lkp s1' s2' ns hm_ active n1 n2 e1_ e2_
                in
                if length binds1 == length binds2
                then foldM mf hm pairs
                else Left []
    -- id equality never checked directly, but it's covered indirectly
    (Case e1' i1 _ a1, Case e2' i2 _ a2)
                | Right hm' <- b_mr ->
                  let h1_ = E.insert (idName i1) e1' h1
                      h2_ = E.insert (idName i2) e2' h2
                      s1' = s1 { expr_env = h1_ }
                      s2' = s2 { expr_env = h2_ }
                      mf hm_ (e1_, e2_) = moreRestrictiveAlt mr_cont gen_lemma lkp s1' s2' ns hm_ False n1 n2 e1_ e2_
                      l = zip a1 a2
                  in foldM mf hm' l
                | otherwise -> b_mr
                where
                    b_mr = moreRestrictive' mr_cont gen_lemma lkp s1 s2 ns hm active n1 n2 e1' e2'
    (Cast e1' c1, Cast e2' c2) | c1 == c2 ->
        moreRestrictive' mr_cont gen_lemma lkp s1 s2 ns hm active n1 n2 e1' e2'

    -- ignore all Ticks
    _ -> mr_cont s1 s2 ns hm active n1 n2 e1 e2

-- check only the names for DataAlt
altEquiv :: AltMatch -> AltMatch -> Bool
altEquiv (DataAlt dc1 ids1) (DataAlt dc2 ids2) =
  let DataCon dn1 _ = dc1
      DataCon dn2 _ = dc2
      n1 = map idName ids1
      n2 = map idName ids2
  in
  dn1 == dn2 && n1 == n2
altEquiv (LitAlt l1) (LitAlt l2) = l1 == l2
altEquiv Default Default = True
altEquiv _ _ = False

-- These helper functions have safeguards to avoid cyclic inlining.
inlineTop :: Lookup t -> [Name] -> State t -> Expr -> Expr
inlineTop lkp acc s v@(Var (Id n _))
    | n `elem` acc = v
    | Just cs <- lkp n s =
        case cs of
            E.Sym _ -> v
            E.Conc e -> inlineTop lkp (n:acc) s e
inlineTop lkp acc s (Tick _ e) = inlineTop lkp acc s e
inlineTop _ _ _ e = e

inlineFull :: Lookup t -> [Name] -> State t -> Expr -> Expr
inlineFull lkp acc s v@(Var (Id n _))
    | n `elem` acc = v
    | Just cs <- lkp n s =
        case cs of
            E.Sym _ -> v
            E.Conc e -> inlineFull lkp (n:acc) s e
inlineFull lkp acc s e = modifyChildren (inlineFull lkp acc s) e

inlineEquiv :: Lookup t -> [Name] -> State t -> HS.HashSet Name -> Expr -> Expr
inlineEquiv lkp acc s ns v@(Var (Id n _))
    | n `elem` acc = v
    | Just (E.Sym _) <- cs = v
    | HS.member n ns = v
    | Just (E.Conc e) <- cs = inlineEquiv lkp (n:acc) s ns e
    where
        cs = lkp n s
inlineEquiv lkp acc s ns e = modifyChildren (inlineEquiv lkp acc s ns) e

-- ids are the same between both sides; no need to insert twice
moreRestrictiveAlt :: MRCont t l
                   -> GenerateLemma t l
                   -> Lookup t
                   -> State t
                   -> State t
                   -> HS.HashSet Name
                   -> (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
                   -> Bool -- ^ active expression?
                   -> [(Name, Expr)] -- ^ variables inlined previously on the LHS
                   -> [(Name, Expr)] -- ^ variables inlined previously on the RHS
                   -> Alt
                   -> Alt
                   -> Either [l] (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
moreRestrictiveAlt mr_cont gen_lemma lkp s1 s2 ns hm active n1 n2 (Alt am1 e1) (Alt am2 e2) =
  if altEquiv am1 am2 then
  case am1 of
    DataAlt _ t1 -> let ns' = foldr HS.insert ns $ map idName t1
                    in moreRestrictive' mr_cont gen_lemma lkp s1 s2 ns' hm active n1 n2 e1 e2
    _ -> moreRestrictive' mr_cont gen_lemma lkp s1 s2 ns hm active n1 n2 e1 e2
  else Left []
