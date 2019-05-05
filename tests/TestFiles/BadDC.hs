module BadDC where

data E
  = I Int
  | B Bool
  | Cond E
  deriving (Eq, Show)

f :: E -> E
f (Cond cond) = case f cond of
  (B True) -> B True
  otherwise -> error $ "error"
f e = e

g :: E -> E
g (Cond cond) = error $ "error"
g e = e