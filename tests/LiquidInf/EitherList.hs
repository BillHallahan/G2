module EitherList where

data EitherList a b = LeftL [a] | RightL [b]

{-@ measure isLeft @-}
isLeft :: EitherList a b -> Bool
isLeft (LeftL _) = True
isLeft (RightL _) = False

{-@ measure isRight @-}
isRight :: EitherList a b -> Bool
isRight (RightL _) = True
isRight (LeftL _) = False

rights :: [EitherList a b] -> [EitherList a b]
rights [] = []
rights (r@(RightL _):xs) = r:rights xs
rights (LeftL _:xs) = rights xs

{-@ extractOnlyRights :: [{ el:EitherList a b | isRight el }] -> [b] @-}
extractOnlyRights :: [EitherList a b] -> [b]
extractOnlyRights [] = []
extractOnlyRights (RightL rs:xs) = rs ++ extractOnlyRights xs
extractOnlyRights (LeftL _:_) = error "extractOnlyRights: LeftL in list"

extractRights :: [EitherList a b] -> [b]
extractRights = extractOnlyRights . rights