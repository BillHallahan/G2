
module Val1 where


data AB = A | B deriving (Eq)

ab :: AB -> Bool
ab A = True
ab _ = error ""

call :: ((AB -> Bool) -> Bool) -> Bool
call f = f ab
