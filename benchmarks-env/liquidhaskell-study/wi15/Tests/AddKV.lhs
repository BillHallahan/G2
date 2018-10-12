\begin{code}
module AddKV where

import Prelude hiding (foldr)
import qualified Data.Map as M

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

\end{code}

\begin{code}

addKV :: M.Map Int (List Int) -> List Int
addKV m = vs'
  where
    vs'       = Emp
\end{code}
