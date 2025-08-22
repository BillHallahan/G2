{-# LANGUAGE GADTs, DataKinds, KindSignatures, RankNTypes, TypeFamilies, FlexibleInstances, FlexibleContexts #-}

module GADTs2 where

import GHC.TypeLits 
import Data.Kind

-- This file aims to provide more test cases to ensure that GADT works with G2
-- When trying to verify GADT code, we always use the flag --inst-after, --validate
-- It's also recommended that not to try gadt invovle recursion since it's will get pretty complicated pretty quick

