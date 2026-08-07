module Regex where

import G2.Plugin

{-# ANN isNum (SMTEquivIsWithConfig "smtIsNum" "--smt cvc5")
    #-}
isNum :: String -> Bool
isNum (x:xs) = x >= '0' && x <= '9' && isNum xs
isNum _ = True

smtIsNum :: String -> Bool
smtIsNum s =
    let digit = smtReRange "0" "9"
        many_digits = smtReStar digit
    in smtInRe s many_digits

{-# ANN isNumBad (SMTEquivIsWithConfig "smtIsNumBad" "--smt cvc5") 
    #-}
isNumBad :: String -> Bool
isNumBad (x:xs) = x >= '0' && x <= '9' && isNumBad xs
isNumBad _ = True

smtIsNumBad :: String -> Bool
smtIsNumBad s =
    let digit = smtReRange "4" "5"
        many_digits = smtReStar digit
    in smtInRe s many_digits

{-# ANN containsFour (SMTEquivIsWithConfig "smtContainsFour" "--smt cvc5")
    #-}
containsFour :: String -> Bool
containsFour [] = False
containsFour ('4':_) = True
containsFour (_:xs) = containsFour xs

smtContainsFour :: String -> Bool
smtContainsFour s =
    let four = smtToRe "4"
        four_n = four `smtReUnion` smtReNone
        any_chars = smtReStar smtReAllChar
        has_four = any_chars `smtReConcat` four_n `smtReConcat` any_chars
    in smtInRe s has_four

{-# ANN containsFourBad (SMTEquivIsWithConfig "smtContainsFourBad" "--smt cvc5")
    #-}
containsFourBad :: String -> Bool
containsFourBad [] = False
containsFourBad ('4':_) = True
containsFourBad (_:xs) = containsFourBad xs

smtContainsFourBad :: String -> Bool
smtContainsFourBad s =
    let four = smtReComp smtReAll -- Definitely not a four
        any_chars = smtReStar smtReAllChar
        has_four = any_chars `smtReConcat` four `smtReConcat` any_chars
    in smtInRe s has_four

{-# ANN noPat (SMTEquivIsWithConfig "smtNoPat" "--smt cvc5 --print-smt")
    #-}
noPat :: String -> Bool
noPat [] = True
noPat ('6':_) = False
noPat ('4':_) = False
noPat (_:xs) = noPat xs

smtNoPat :: String -> Bool
smtNoPat s =
    let pat1 = smtToRe "6"
        pat2 = smtToRe "4"
        all_pat = pat1 `smtReUnion` pat2
        any_chars = smtReStar smtReAllChar
        has_pat = any_chars `smtReConcat` all_pat `smtReConcat` any_chars
        no_pat = smtReComp has_pat
    in smtInRe s no_pat

{-# ANN noPatBad (SMTEquivIsWithConfig "smtNoPatBad" "--smt cvc5")
    #-}
noPatBad :: String -> Bool
noPatBad [] = True
noPatBad ('6':_) = False
noPatBad ('4':_) = False
noPatBad (_:xs) = noPatBad xs

smtNoPatBad :: String -> Bool
smtNoPatBad s =
    let pat1 = smtToRe "6"
        pat2 = smtToRe "4"
        -- Intersection instead of Union makes this impossible
        all_pat = pat1 `smtReInter` pat2
        any_chars = smtReStar smtReAllChar
        has_pat = any_chars `smtReConcat` all_pat `smtReConcat` any_chars
        no_pat = smtReComp has_pat
    in smtInRe s no_pat