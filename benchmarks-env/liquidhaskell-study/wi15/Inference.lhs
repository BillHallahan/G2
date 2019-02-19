Type Inference
==============

<div class="hidden">
\begin{code}
{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, OverlappingInstances, FlexibleInstances #-}

import qualified Data.Map as Map 
import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Writer
import Test.QuickCheck 
import Control.Monad (forM, forM_)
import Data.List (transpose, intercalate)

import qualified Data.Set as Set
import Control.Applicative ((<$>))
import qualified Text.PrettyPrint as PP

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import System.Exit
import System.IO.Unsafe
import Data.IORef

quickCheckN n = quickCheckWith $ stdArgs { maxSuccess = n}
\end{code}
</div>

In this problem, we will take the bare-bones language for which we
studied [type inference](/lectures/inference.html), add features 
to it, and update the inference to work with those features.

(a) Pairs
---------

The first feature we will add is pairs, ie tuples of size 2. 
Specifically, we have extended the language of expressions `Expr`
to include

~~~~~{.haskell}
data Exp = ...
         | Exp `ECom` Exp  -- Construct a pair of two expressions
         | EFst  Exp         -- Extract the first  element of a pair
	     | ESnd  Exp         -- Extract the second element of a pair
~~~~~

Correspondingly, we have extended the language of types to include

~~~~~{.haskell}
data Type = ... 
          |  Type `TCom` Type -- Pair of two types
~~~~~

Extend the definition of the `mgu` and `ti` functions to correctly infer
types for the extended language.



When you are done, you should be able to infer that the expression

\begin{code}
eSwap = EAbs (EV "x") $ (ELet (EV "a") (EFst (EVbl (EV "x")))
                        (ELet (EV "b") (ESnd (EVbl (EV "x")))
                        (EVbl (EV "b") `ECom` EVbl (EV "a"))))
\end{code}

has the type (equivalent to)

\begin{code}
tSwap = Forall [TV "a", TV "b"] $
          (TVbl (TV "a") `TCom` TVbl (TV "b")) `TArr` ((TVbl (TV "b") `TCom` TVbl (TV "a")))
\end{code}

(b) Lists  
---------

Next, let us add lists, to the language. Specifically, we 
extend the language of expressions `Expr` to include

~~~~~{.haskell}
data Exp = ...
         | ENil            -- empty list
         | Exp `ECons` Exp -- head "cons-ed" to a tail
	     | EIsNil Exp      -- test if a list is empty
	     | EDcons Exp      -- return a pair of (head, tail) of (non-empty) list
~~~~~

Correspondingly, we have extended the language of types to include

~~~~~{.haskell}
data Type = ... 
          | TList Type     -- TList t is a list of t values 
~~~~~

Extend the definition of the `mgu` and `ti` functions to correctly infer
types for the extended language.

When you are done, you should be able to infer that in the environment 

\begin{code}
env   = Map.fromList 
  [ (EV "plus", Forall [] $ tArrs [TInt, TInt, TInt])
  , (EV "ite" , Forall [TV "a"] $ tArrs [TBool, TVbl (TV "a"), TVbl (TV "a"), TVbl (TV "a")])]

tenv  = TypeEnv env
\end{code}

the expressions `eHd` and `eList`

\begin{code}
eZero = ELit (LInt 0)
eOne  = ELit (LInt 1)
ePlus = EVbl (EV "plus")


eInc  = EAbs (EV "x") $ eApps [ePlus, eOne, EVbl (EV "x")]

eHd   = EAbs (EV "x") $ EFst (EDcons (EVbl (EV "x")))
eTl   = EAbs (EV "x") $ ESnd (EDcons (EVbl (EV "x")))

eList = EAbs (EV "x") 
          (eIf (EIsNil (EVbl (EV "x"))) 
               eZero
               (eInc `EApp` ((eHd `EApp` (EVbl (EV "x"))) `EApp` eZero)))
\end{code}

have the respective types

\begin{code}
tHd   = Forall [TV "a"] $ (TList (TVbl (TV "a"))) `TArr` (TVbl (TV "a"))
tTl   = Forall [TV "a"] $ (TList (TVbl (TV "a"))) `TArr` (TList (TVbl (TV "a")))
tList = Forall [] ((TList (TInt `TArr` TInt)) `TArr` TInt)
\end{code}

where the helper functions are defined

\begin{code}
tArrs = foldr1 TArr 
eApps = foldl1 EApp
eIf   = \b e1 e2 -> eApps [EVbl (EV "ite"), b, e1, e2] 
\end{code}


(c) Recursion 
-------------

Finally, we will add recursive functions to the language, via the following
construct.

~~~~~{.haskell}
data Exp = ...
         | ELetrec EVbl Exp Exp -- "ELetrec x e1 e2" allows x to appear in e1
~~~~~

We need not extend the language of types at all, and hence the `mgu`
function remains the same. However, the tricky bit is to figure out
how to break the following cycle: we need to use the type of x to
determine the type of e1, but we need to type e1 to determine the type
of x!


When you are done, you should be able to infer that the expressions `eTl`
and `eLen` 

\begin{code}
eLen = ERec (EV "len") 
          (EAbs (EV "xs") $ 
             eIf (EIsNil (EVbl (EV "xs"))) 
                 eZero 
                 (eInc `EApp`(((EVbl (EV "len")) `EApp` (eTl `EApp` (EVbl (EV "xs")))))))
          (EVbl (EV "len"))

eMap = ERec (EV "map") 
          (EAbs (EV "f") $ EAbs (EV "xs") $ 
             eIf (EIsNil (EVbl (EV "xs"))) 
                 ENil
                 (ECons (EVbl (EV "f") `EApp` (eHd `EApp` (EVbl (EV "xs"))))
                        ((EVbl (EV "map") `EApp` (EVbl (EV "f"))) `EApp`
                        (eTl `EApp` (EVbl (EV "xs"))))))

          (EVbl (EV "map"))
\end{code}

have the types equivalent to

\begin{code}
tLen  = Forall [TV "a"] $ ((TList (TVbl (TV "a"))) `TArr` TInt)
tMap  = Forall [TV "a", TV "b"] $ tArrs [TVbl (TV "a") `TArr` TVbl (TV "b")
                                        ,TList (TVbl (TV "a"))
                                        ,TList (TVbl (TV "b"))]
\end{code}

Appendix: Code for Type Inference from Lecture
----------------------------------------------

\begin{code}
data Exp     =  EVbl EVbl 
             |  ELit Lit
             |  EApp Exp Exp
             |  EAbs EVbl Exp
             |  ELet EVbl Exp Exp
                                  -- part (a)
             |  Exp `ECom` Exp    -- Construct a pair of two expressions
             |  EFst  Exp         -- Extract the first  element of a pair
             |  ESnd  Exp         -- Extract the second element of a pair
                                  -- part (b)
             |  ENil              -- empty list
             |  Exp `ECons` Exp   -- head "cons-ed" to a tail
             |  EIsNil Exp        -- test if a list is empty
             |  EDcons Exp        -- return a pair of (head, tail) of (non-empty) list
                                  -- part (c)
             |  ERec EVbl Exp Exp -- ERec x e1 e2 is like Let x e1 e2 but x can appear in e1
             deriving (Eq, Ord)

newtype EVbl = EV String deriving (Eq, Ord)

data Lit     =  LInt Integer
             |  LBool Bool
             deriving (Eq, Ord)

data Type    =  TVbl TVbl 
             |  TInt
             |  TBool
             |  Type `TArr` Type
                                   -- part (a)
             |  Type `TCom` Type   -- Pair of two types
                                   -- part (b)
             |  TList Type         -- TList t is a list of t values 
             deriving (Eq, Ord)

newtype TVbl = TV String deriving (Eq, Ord)

data Scheme  =  Forall [TVbl] Type

newtype TypeEnv = TypeEnv (Map.Map EVbl Scheme)

(\\) :: TypeEnv -> (EVbl, Scheme) -> TypeEnv
(TypeEnv env) \\ (x, s) =  TypeEnv $ Map.insert x s env

type Subst = Map.Map TVbl Type

class Substitutable a where 
  apply     :: Subst -> a -> a
  freeTvars :: a -> Set.Set TVbl

instance Substitutable Type where
  apply _  TInt            = TInt
  apply _  TBool           = TBool
  apply su t@(TVbl a)      = Map.findWithDefault t a su 
  apply su (t1 `TArr` t2)  = apply su t1 `TArr` apply su t2
  apply su (t1 `TCom` t2)  = error "TBD"
  apply su (TList t)       = error "TBD"

  freeTvars TInt           =  Set.empty
  freeTvars TBool          =  Set.empty
  freeTvars (TVbl a)       =  Set.singleton a
  freeTvars (t1 `TArr` t2) =  freeTvars t1 `Set.union` freeTvars t2
  freeTvars (t1 `TCom` t2) = error "TBD"
  freeTvars (TList t)      = error "TBD"

instance Substitutable Scheme where
  apply s (Forall as t)   = Forall as $ apply s' t 
                            where s' = foldr Map.delete s as 

  freeTvars (Forall as t) = (freeTvars t) `Set.difference` (Set.fromList as)


instance Substitutable a => Substitutable [a] where
  apply     = map . apply
  freeTvars = foldr Set.union Set.empty . map freeTvars

instance Substitutable TypeEnv where
  apply s   (TypeEnv env) =  TypeEnv   $ Map.map (apply s) env
  freeTvars (TypeEnv env) =  freeTvars $ Map.elems env

empSubst  ::  Subst
empSubst  =   Map.empty

after         :: Subst -> Subst -> Subst
su1 `after` su2 = (Map.map (apply su1) su2) `Map.union` su1


mgu (l `TCom` r) (l' `TCom` r')  = error "TBD"
mgu (TList t1) (TList t2)        = error "TBD"
mgu (l `TArr` r) (l' `TArr` r')  = do  s1 <- mgu l l'
                                       s2 <- mgu (apply s1 r) (apply s1 r')
                                       return (s2 `after` s1)
mgu (TVbl a) t                   = varAsgn a t
mgu t (TVbl a)                   = varAsgn a t
mgu TInt TInt                    = return empSubst
mgu TBool TBool                  = return empSubst
mgu t1 t2                        = throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

varAsgn a t 
  | t == TVbl a                  =  return empSubst
  | a `Set.member` (freeTvars t) =  throwError $ "occur check fails: " ++ show a ++ " in " ++ show t
  | otherwise                    =  return $ Map.singleton a t

generalize        ::  TypeEnv -> Type -> Scheme
generalize env t  =   Forall as t
  where as = Set.toList $ (freeTvars t) `Set.difference` (freeTvars env)

data TIState = TIState { count :: Int }

fresh :: (MonadState TIState m) => m Int
fresh = do s     <- get
           let n = count s
           put   $ s { count = n + 1 }
           return n

freshTVbl prefix = fresh >>= return . TVbl . TV . (prefix ++) . show

instantiate (Forall as t) = do as' <- mapM (\ _ -> freshTVbl "a") as 
                               let s = Map.fromList $ zip as as'
                               return $ apply s t

ti ::  (MonadState TIState m, MonadError String m) => 
       TypeEnv -> Exp -> m (Subst, Type)

ti env (ELit (LInt _))  = return (empSubst, TInt)
ti env (ELit (LBool _)) = return (empSubst, TBool)
ti (TypeEnv env) (EVbl x) = 
    case Map.lookup x env of
       Nothing   ->  throwError $ "unbound variable: " ++ show x
       Just s    ->  instantiate s >>= return . (,) empSubst 
ti env (EAbs x e) =
    do  tv       <- freshTVbl "a"
        let env' = env \\ (x, Forall [] tv)
        (s1, t1) <- ti env' e
        return (s1, (apply s1 tv) `TArr` t1)
ti env (EApp e1 e2) =
    do  tv       <- freshTVbl "a"
        (s1, t1) <- ti env e1
        (s2, t2) <- ti (apply s1 env) e2
        s3       <- mgu (apply s2 t1) (TArr t2 tv)
        return (s3 `after` s2 `after` s1, apply s3 tv)
ti env (ELet x e1 e2) =
    do  (s1, t1) <- ti env e1
        let t'   = generalize (apply s1 env) t1
            env' = env \\ (x, t')
        (s2, t2) <- ti (apply s1 env') e2
        return (s2 `after` s1, t2)

ti env (e1 `ECom` e2) = error "TBD"
ti env (EFst e)       = error "TBD"
ti env (ESnd e)       = error "TBD"

ti env ENil            = error "TBD"
ti env (e1 `ECons` e2) = error "TBD"
ti env (EIsNil e)      = error "TBD"
ti env (EDcons e)      = error "TDB"

ti env (ERec x e1 e2)  = error "TBD"

ti_top env e =
    do  (s, t) <- ti env e
        return  $ generalize (apply s env) (apply s t)

typeInference :: TypeEnv -> Exp -> Either String Scheme 
typeInference env e = res
  where act = ti_top env e
        res = evalState (runErrorT act) s0 
        s0  = TIState { count = 0 }


test :: Exp -> IO ()
test e = case typeInference (TypeEnv Map.empty) e of
           Left err  ->  putStrLn $ "error: " ++ err
           Right t   ->  putStrLn $ show e ++ " :: " ++ show t


instance Show TVbl where
  showsPrec _ x = shows (prTVbl x)

prTVbl (TV a) = PP.text a

instance Show Type where
  showsPrec _ x = shows (prType x)

prType             ::  Type -> PP.Doc
prType (TVbl a)    =   prTVbl a
prType TInt        =   PP.text "Int"
prType TBool       =   PP.text "Bool"
prType (TArr t s)  =   prParenType t PP.<+> PP.text "->" PP.<+> prType s
prType _           =   PP.text "FINAL optional"

prParenType     ::  Type -> PP.Doc
prParenType  t  =   case t of
                      TArr _ _  -> PP.parens (prType t)
                      _         -> prType t

instance Show EVbl where
  showsPrec _ x = shows (prEVbl x)

instance Show Exp where
  showsPrec _ x = shows (prExp x)

prEVbl (EV x)          = PP.text x

prExp                  ::  Exp -> PP.Doc
prExp (EVbl x)         =   prEVbl x
prExp (ELit lit)       =   prLit lit
prExp (ELet x b body)  =   PP.text "let" PP.<+> 
                           prEVbl x PP.<+> PP.text "=" PP.<+>
                           prExp b PP.<+> PP.text "in" PP.$$
                           PP.nest 2 (prExp body)
prExp (EApp e1 e2)     =   prExp e1 PP.<+> prParenExp e2
prExp (EAbs x e)       =   PP.char '\\' PP.<+> prEVbl x PP.<+>
                           PP.text "->" PP.<+>
                           prExp e
prExp _                =   PP.text "FINAL optional"
                                                                   

prParenExp    ::  Exp -> PP.Doc
prParenExp t  =   case t of
                    ELet _ _ _  -> PP.parens (prExp t)
                    EApp _ _    -> PP.parens (prExp t)
                    EAbs _ _    -> PP.parens (prExp t)
                    _           -> prExp t

instance Show Lit where
    showsPrec _ x = shows (prLit x)

prLit            ::  Lit -> PP.Doc
prLit (LInt i)   =   PP.integer i
prLit (LBool b)  =   if b then PP.text "True" else PP.text "False"

instance Show Scheme where
    showsPrec _ x = shows (prScheme x)

prScheme                ::  Scheme -> PP.Doc
prScheme (Forall as t)  =   PP.text "All" PP.<+>
                            PP.hcat (PP.punctuate PP.comma (map prTVbl as))
                            PP.<> PP.text "." PP.<+> prType t
\end{code}
