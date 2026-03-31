{-# LANGUAGE BangPatterns, MagicHash, ScopedTypeVariables, TypeApplications, ViewPatterns #-}
module Spec where

import GHC.Prim2
import Control.Exception

regex1 :: String -> Int
regex1 x =
    let !re1 = toRe# "abc"
        !re2 = toRe# "abcdefghij"
        !re_union = re1 `reUnion#` re2 in
    case assert False (inRe# x re_union) of
        True | length x > 5 -> 1
             | otherwise -> 2
        False -> 3

regex2 :: String -> Int
regex2 x =
    let !re1 = toRe# "abc"
        !re2 = toRe# "xyz"
        !re_union = re1 `reUnion#` re2
        !re_inter = re1 `reInter#` re_union in
    case assert False (inRe# x re_inter) of
        True | x == "xyz" -> 1 -- Unreachable
             | otherwise -> 2
        False -> 3

regex3 :: String -> Int
regex3 x =
    let !re1 = toRe# "abc"
        !re_star = reStar# re1 in
    case assert False (inRe# x re_star) of
        True | length x > 31 -> 1
             | length x > 40 -> 2 -- Unreachable
             | otherwise -> 3
        False -> 4

regex4 :: String -> Int
regex4 x =
    let !re1 = toRe# "abc"
        !re2 = toRe# "xyz"
        !re_concat = reConcat# re2 re1 in
    case assert False (inRe# x re_concat) of
        True | length x > 50 -> 1 -- Unreachable
             | length x > 10 -> 2 -- Unreachable
             | otherwise -> 3
        False -> 4

regex5 :: String -> Int
regex5 x =
    let !re_all = reAll# @Char
        !re_none = reNone# @Char
        !re_union = re_all `reUnion#` re_none in
    case assert False (inRe# x re_union) of
        True | length x > 50 -> 1
             | length x > 10 -> 2
             | otherwise -> 3
        False -> 4 -- Unreachable

regex6 :: String -> Int
regex6 x =
    let !re_all = reAllChar# @Char
        !re_none = reNone# @Char
        !re_union = re_all `reUnion#` re_none in
    case assert False (inRe# x re_union) of
        True | length x > 50 -> 1 -- Unreachable
             | length x > 10 -> 2 -- Unreachable
             | otherwise -> 3
        False -> 4

regex7 :: String -> Int
regex7 x =
    let !re_all = reAllChar# @Char
        !re_empty = toRe# ""
        !re_union = re_all `reUnion#` re_empty
        !re_comp = reComp# re_union
    in
    case assert False (inRe# x re_comp) of
        True | length x > 50 -> 1 
             | length x > 1 -> 2
             | otherwise -> 3 -- Unreachable
        False -> 4

regex8 :: String -> Int
regex8 x =
    let !re_range = reRange# "a" "z"
        !re_none = reNone# @Char
        !re_union = re_range `reUnion#` re_none in
    case assert False (inRe# x re_union) of
        True | length x > 50 -> 1 -- Unreachable
             | length x > 10 -> 2 -- Unreachable
             | otherwise -> 3
        False -> 4

regex9 :: String -> Int
regex9 x =
    let !re1 = toRe# "abc"
        !x' = strReplaceRe# x re1 "hello" in
    case assert False (strContains# x' "hello") of
        True | strContains# x' "abc" -> 1
             | otherwise -> 2
        False -> 3

regex10 :: String -> Int
regex10 x =
    let !re1 = toRe# "abc"
        !x' = strReplaceReAll# x re1 "hello" in
    case assert False (strContains# x' "hello") of
        True | strContains# x' "abc" -> 1
             | otherwise -> 2
        False -> 3

-- Should return True
retRegex1 :: String -> Bool
retRegex1 x =
    let !re1 = toRe# "abc"
        !re_all = reAll# @Char
        !re_concat = reConcat# re_all re1 in
    assert False (inRe# "match abc" re_concat)

-- Should return True
retRegex2 :: String -> Bool
retRegex2 x =
    let !re1 = toRe# "abc"
        !re2 = toRe# "defghi"
        !re_concat = reConcat# re1 re2 in
    assert False (inRe# "abcdefghi" re_concat)

-- Should return True
retRegex3 :: String -> Bool
retRegex3 x =
    let !re1 = toRe# "abc"
        !re2 = toRe# "def"
        !re_union = reUnion# re1 re2 in
    assert False (inRe# "def" re_union)

-- Should return True
retRegex4 :: String -> Bool
retRegex4 x =
    let !re1 = toRe# "abc"
        !re_star = reStar# re1 in
    assert False (inRe# "abcabcabcabc" re_star)

-- Should return False
retRegex5 :: String -> Bool
retRegex5 x =
    let !re1 = toRe# "abc"
        !re_star = reStar# re1 in
    assert False (inRe# "abcabcabcDabc" re_star)

-- Should return True
retRegex6 :: String -> Bool
retRegex6 x =
    let !re1 = toRe# "abc"
        !re_star = reStar# re1
        !re_comp = reComp# re_star in
    assert False (inRe# "abcabcabcDabc" re_comp)

-- Should return False
retRegex7 :: String -> Bool
retRegex7 x =
    let !re1 = toRe# "abc"
        !re_star = reStar# re1
        !re_comp = reComp# re_star in
    assert False (inRe# "abcabcabcabc" re_comp)

-- Should return True
retRegex8 :: String -> Bool
retRegex8 x =
    let !re1 = toRe# "abc"
        !re2 = toRe# "bc"
        !re_star = reStar# re1
        !re_comp = reComp# re_star
        !re_app = reConcat# re_comp re2 in
    assert False (inRe# "abc" re_app)

-- Should return False
retRegex9 :: String -> Bool
retRegex9 x =
    let !re1 = toRe# "abc"
        !re_star = reStar# re1
        !re_comp = reComp# re_star
        !re_app = reConcat# re_comp re1 in
    assert False (inRe# "abc" re_app)

-- Should return True
retRegex10 :: String -> Bool
retRegex10 x =
    let !re_range = reRange# "abc" "zyx" in
    assert False (inRe# "m" re_range)

-- Should return False
retRegex11 :: String -> Bool
retRegex11 x =
    let !re_range = reRange# "abc" "zyx" in
    assert False (inRe# "M" re_range)
