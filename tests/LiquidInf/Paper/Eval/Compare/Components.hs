module Components where

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

-- init -> condition -> increment -> body -> ...
for :: a -> (a -> Bool) -> (a -> a) -> (a -> a) -> a
for init pred incr body =
	if pred init
		then for init pred incr body (incr (body init))
		else init