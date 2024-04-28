module G2.Language.Approximation ( GenerateLemma
                                 , Lookup
                                 , MRCont
                                 
                                 , moreRestrictive
                                 , moreRestrictive'
                                 , moreRestrictivePC

                                 , applySolver
                                 
                                 , inlineEquiv) where

import G2.Execution.NormalForms
import G2.Language.Expr
import qualified G2.Language.ExprEnv as E
import G2.Language.Naming
import qualified G2.Language.PathConds as P
import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Typing as T
import qualified G2.Solver as S

import Control.Monad.Extra
import Control.Monad.IO.Class
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

-------------------------------------------------------------------------------
-- [Inlining]
-- We keep two separate lists of variables that have been inlined previously on
-- the LHS and RHS. This means that inlinings on one side do not block any inlinings
-- that need to happen on the other side.
--
-- Whenever a variable is inlined, we record the expression that was on the
-- opposite side at the time.  Not allowing a variable to be inlined at all on one
-- side in any sub-expressions that resulted from an inlining of it is too restrictive
-- in practice.  We allow repeated inlinings of a variable as long as the expression on
-- the opposite side is not the same as it was when a previous inlining of the
-- same variable happened.
-------------------------------------------------------------------------------

-- | Check is s1 is an approximation of s2 (if s2 is more restrictive than s1.)
moreRestrictive :: MRCont t l -- ^ For special case handling - what to do if we don't match elsewhere in moreRestrictive
                -> GenerateLemma t l
                -> Lookup t -- ^ How to lookup variable names
                -> State t -- ^ s1
                -> State t -- ^ s2
                -> HS.HashSet Name -- ^ Names that should not be inlined (often: top level names from the original source code)
                -> (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
                -> Either [l] (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
moreRestrictive mr_cont gen_lemma lkp s1 s2 ns hm =
    moreRestrictive' mr_cont gen_lemma lkp s1 s2 ns hm True [] [] (getExpr s1) (getExpr s2)

moreRestrictive' :: MRCont t l -- ^ For special case handling - what to do if we don't match elsewhere in moreRestrictive'
                 -> GenerateLemma t l
                 -> Lookup t
                 -> State t
                 -> State t
                 -> HS.HashSet Name -- ^ Names that should not be inlined (often: top level names from the original source code)
                 -> (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
                 -> Bool -- ^ indicates whether this is part of the "active expression"
                 -> [(Name, Expr)] -- ^ variables inlined previously on the LHS (see [Inlining])
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
               , Nothing <- HM.lookup i hm' -> Right (HM.insert i (inlineEquiv lkp s2 ns e2) hm', hs)
               | Just (E.Sym _) <- lkp (idName i) s1
               , Just e <- HM.lookup i (fst hm)
               , e == inlineEquiv lkp s2 ns e2 -> Right hm
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
                           --, not active
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
    --
    -- We use an empty HashSet when inlining because when generating a path constraint
    -- we DO NOT want any top level names being preserved- these would just confuse the SMT solver.
    (App _ _, _) | e1':_ <- unApp e1
                 , (Prim _ _) <- inlineEquiv lkp s1 HS.empty e1'
                 , T.isPrimType $ typeOf e1
                 , T.isPrimType $ typeOf e2
                 , isSWHNF $ (s2 { curr_expr = CurrExpr Evaluate e2 }) ->
                                  let (hm', hs) = hm
                                  in Right (hm', HS.insert (inlineEquiv lkp s1 HS.empty e1, inlineEquiv lkp s2 HS.empty e2) hs)
    (_, App _ _) | e2':_ <- unApp e2
                 , (Prim _ _) <- inlineEquiv lkp s2 HS.empty e2'
                 , T.isPrimType $ typeOf e2
                 , T.isPrimType $ typeOf e1
                 , isSWHNF $ (s1 { curr_expr = CurrExpr Evaluate e1 }) ->
                                  let (hm', hs) = hm
                                  in Right (hm', HS.insert (inlineEquiv lkp s1 HS.empty e1, inlineEquiv lkp s2 HS.empty e2) hs)
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

inlineEquiv :: Lookup t  -> State t -> HS.HashSet Name -> Expr -> Expr
inlineEquiv lkp s ns v@(Var (Id n _))
    | Just (E.Sym _) <- cs = v
    | HS.member n ns = v
    | Just (E.Conc e) <- cs = inlineEquiv lkp s (HS.insert n ns) e
    where
        cs = lkp n s
inlineEquiv lkp s ns e = modifyChildren (inlineEquiv lkp s ns) e

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

-- s1 is old state, s2 is new state
-- only apply to old-new state pairs for which moreRestrictive' works
moreRestrictivePC :: (MonadIO m, S.Solver solver) =>
                     solver ->
                     State t ->
                     State t ->
                     HM.HashMap Id Expr ->
                     m Bool
moreRestrictivePC solver s1 s2 hm = do
  let new_conds = map extractCond (P.toList $ path_conds s2)
      old_conds = map extractCond (P.toList $ path_conds s1)
      l = map (\(i, e) -> (Var i, e)) $ HM.toList hm
      -- this should only be used with primitive types
      -- no apparent problems come from using TyUnknown
      l' = map (\(e1, e2) ->
                  if (T.isPrimType $ typeOf e1) && (T.isPrimType $ typeOf e2)
                  then Just $ App (App (Prim Eq TyUnknown) e1) e2
                  else Nothing) l
      l'' = [c | Just c <- l']
      new_conds' = l'' ++ new_conds
      -- not safe to use unless the lists are non-empty
      conj_new = foldr1 (\o1 o2 -> App (App (Prim And TyUnknown) o1) o2) new_conds'
      conj_old = foldr1 (\o1 o2 -> App (App (Prim And TyUnknown) o1) o2) old_conds

      imp = App (App (Prim Implies TyUnknown) conj_new) conj_old
      neg_imp = ExtCond (App (Prim Not TyUnknown) imp) True
      neg_conj = ExtCond (App (Prim Not TyUnknown) conj_old) True
  
  res <- if null old_conds
         then return $ S.UNSAT ()
         else if null new_conds'
                then liftIO $ applySolver solver (P.insert neg_conj P.empty) s1 s2
                else liftIO $ applySolver solver (P.insert neg_imp P.empty) s1 s2
  case res of
    S.UNSAT () -> return True
    _ -> return False

-- shortcut:  don't invoke Z3 if there are no path conds
applySolver :: S.Solver solver =>
               solver ->
               PathConds ->
               State t ->
               State t ->
               IO (S.Result () () ())
applySolver solver extraPC s1 s2 =
    let unionEnv = E.union (expr_env s1) (expr_env s2)
        rightPC = P.toList $ path_conds s2
        unionPC = foldr P.insert (path_conds s1) rightPC
        -- adding extraPC in here may be redundant
        allPC = foldr P.insert unionPC (P.toList extraPC)
        newState = s1 { expr_env = unionEnv, path_conds = extraPC }
    in case (P.toList allPC) of
      [] -> return $ S.SAT ()
      _ -> S.check solver newState allPC

-- All the PathConds that this receives are generated by symbolic execution.
-- Consequently, non-primitive types are not an issue here.
extractCond :: PathCond -> Expr
extractCond (ExtCond e True) = e
extractCond (ExtCond e False) = App (Prim Not TyUnknown) e
extractCond (AltCond l e True) =
  App (App (Prim Eq TyUnknown) e) (Lit l)
extractCond (AltCond l e False) =
  App (App (Prim Neq TyUnknown) e) (Lit l)
extractCond _ = error "Not Supported"
