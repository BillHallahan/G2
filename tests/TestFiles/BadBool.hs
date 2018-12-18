module BadBool where
    
f :: Float -> Float -> Float -> Float
f orig x eAllowed =
    let
        guess = (orig / x) + x
        e = orig - guess
    in
    if e <= eAllowed then guess else f orig guess eAllowed

g :: Float -> Float -> Float
g orig x =
    let
        guess = (orig / x) + x
        e = orig - guess
    in
    if e <= 1 then guess else g orig guess