module ExH where

import qualified Data.Map as M

data H = H

{-@ M.map :: f:(a -> b) -> m1:M.Map k a -> {m2:M.Map k b | m1 == M.empty => m2 == M.empty}  @-}
{-@ c  :: M.Map Int H -> M.Map Int H @-}
c :: M.Map Int H -> M.Map Int H
c = M.map idH

idH :: H -> H
idH x = x