module Primitives where
	
import G2.Internals.Language.Syntax 

mkPrim :: Int -> NameGen -> Primitive -> (Expr, NameGen)
mkPrim n ngen p =
    let
        (names, ngen') = freshNames n ngen
        (binds, ngen'') = freshNames n ngen'

        lamIds = map (flip Id TyBottom) names
        bindsIds = map (flip Id TyBottom) names
    in
    foldr1 () (map Lam lamIds)