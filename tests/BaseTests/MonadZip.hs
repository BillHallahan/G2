module MonadZip where

import Control.Monad.Zip

callList :: [a] -> [b] -> [(a, b)]
callList = mzip

callMaybe :: Maybe a -> Maybe b -> Maybe (a, b)
callMaybe = mzip