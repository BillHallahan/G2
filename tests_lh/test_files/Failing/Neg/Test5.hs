module Combined (List, g) where

import Prelude hiding (foldr, foldr1)

import qualified Data.Map as M

infixr 9 :+:

data List a = Emp
            | (:+:) a (List a)

{-@ g :: (Ord k) => List k -> M.Map k (List v) @-}
g :: (Ord k) => List k -> M.Map k (List v)
g = f h M.empty

{-@ h :: Ord k => k -> M.Map k ({ xs:List v | false }) -> M.Map k (List v) @-}
h k m = M.insert k Emp m

f :: (a -> b -> b) -> b -> List a -> b
f _  b Emp        = b
f op b (x :+: xs) = x `op` f op b xs