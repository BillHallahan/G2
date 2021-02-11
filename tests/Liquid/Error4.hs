module Error4 where

data EitherList = LeftL | RightL

{-@ measure isRight @-}
isRight :: EitherList -> Bool
isRight RightL = True
isRight LeftL = False

{-@ extractOnlyRights :: { el:EitherList | isRight el } -> Int @-}
extractOnlyRights :: EitherList -> Int
extractOnlyRights RightL = 0
extractOnlyRights _ = error "extractOnlyRights: LeftL in list"

extractRights :: Int
extractRights = extractOnlyRights LeftL