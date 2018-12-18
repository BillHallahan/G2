module BadBool where
    
f :: Float -> Float -> Float -> Float
f orig x eAllowed =
    let
        guess = (orig / x) + x
        e = orig - guess
    in
    if e <= eAllowed then guess else f orig guess eAllowed