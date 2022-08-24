
module Ptr1 where

import Data.Word
import Helper.Ptr

-- import Foreign.C.Types
-- import Foreign.ForeignPtr
-- import Foreign.Ptr
-- import Foreign.Storable
-- import System.IO.Unsafe

zero4 = do fp <- mallocForeignPtrBytes 4 
           withForeignPtr fp $ \p -> do
             poke (p `plusPtr` 0) zero
             poke (p `plusPtr` 1) zero
             poke (p `plusPtr` 2) zero
             poke (p `plusPtr` 3) zero
           return fp
        where
           zero = 0 :: Word8