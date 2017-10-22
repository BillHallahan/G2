module GetNthTest where

import G2.Internals.Language

data CList = Cons Int CList | Nil

getNth :: CList -> Int -> Int 
getNth (Cons x _)  0 = x 
getNth (Cons _ xs) n = getNth xs (n - 1)
getNth _      _ = -1

getNthErr :: CList -> Int -> Maybe Int 
getNthErr (Cons x _)  0 = Just x 
getNthErr (Cons _ xs) n = getNth xs (n - 1)
getNthErr _      _ = Nothing

toCList :: Expr -> CList
toCList (App (App (Data (DataCon (Name "Cons" _ _) _ _)) (Lit (LitInt x))) y) = Cons x (toCList y)
toCList _ = Nil

getNthTest :: [Expr] -> Bool
getNthTest [cl, (Lit (LitInt i)), (Lit (LitInt a))] = getNth (toCList cl) i == a
getNthTest _ = False

getNthErrTest :: [Expr] -> Bool
getNthErrTest [cl, (Lit (LitInt i)), (Lit (LitInt a))] = getNthErr (toCList cl) i == Just a
getNthErrTest _ = getNthErr (toCList cl) i == Nothing