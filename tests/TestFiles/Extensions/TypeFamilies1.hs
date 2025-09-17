{-# LANGUAGE TypeFamilies #-}

module TypeFamily where

type family F a where
    F Int = Bool
    F Bool = Int

data C a where
    I :: C Int
    B :: C Bool 

f :: C a -> F a
f I = True
f B = 0