{-# OPTIONS_GHC -Wno-type-defaults -Wno-orphans #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import qualified Definitions as D
import qualified Nat as N
import qualified ZenoWithDelete as ZDelete
import qualified ZenoWithDrop as ZDrop
import qualified ZenoWithElem as ZElem
import qualified ZenoWithFilter as ZFilter
import qualified ZenoWithHeight as ZHeight
import qualified ZenoWithIns as ZIns
import qualified ZenoWithLen as ZLen
import qualified ZenoWithMap as ZMap
import qualified ZenoWithMirror as ZMirror
import qualified ZenoWithRev as ZRev
import qualified ZenoWithTake as ZTake
import qualified ZenoWithTakeWhile as ZTakeWhile
import qualified ZenoWithZip as ZZip
import qualified ZenoBadProp as ZBP

import Control.Monad
import Test.Tasty
import Test.Tasty.QuickCheck

-- Pass:
-- --min-duration-to-report 0s
-- on the command line to make sure we get times for all tests
main :: IO ()
main =
    defaultMainWithIngredients
        defaultIngredients
        $ testGroup "All"[
          definitions
        , nat
        , zenoWithDelete
        , zenoWithDrop
        , zenoWithElem
        , zenoWithFilter
        , zenoWithHeight
        , zenoWithIns
        , zenoWithLen
        , zenoWithMap
        , zenoWithMirror
        , zenoWithRev
        , zenoWithTake
        , zenoWithTakeWhile
        , zenoWithZip
        , zenoBadProp
        ]


definitions :: TestTree
definitions =
    testGroup "Definitions" [
          testProperty "prop_rot_bogus" D.prop_rot_bogus
        , testProperty "prop_len_bs" D.prop_len_bs
        , testProperty "prop_drop_idem" D.prop_drop_idem
        , testProperty "prop_drop_invol" D.prop_drop_invol
        , testProperty "prop_drop_inj1" D.prop_drop_inj1
        , testProperty "prop_drop_inj2" D.prop_drop_inj2
        , testProperty "prop_union_comm" D.prop_union_comm
        , testProperty "prop_rot_inj0" D.prop_rot_inj0
        , testProperty "prop_rot_uhhhw1" D.prop_rot_uhhhw1
        , testProperty "prop_rot_uhhhw2" D.prop_rot_uhhhw2
    ]

nat :: TestTree
nat =
    testGroup "Nat" [
          testProperty "plus_idem" N.plus_idem
        , testProperty "plus_not_idem" N.plus_not_idem
        , testProperty "plus_inf" N.plus_inf
        , testProperty "mul_idem" N.mul_idem
        , testProperty "silly" N.silly
        , testProperty "sub_assoc" N.sub_assoc
        , testProperty "not_trans" N.not_trans
        , testProperty "sub_comm" N.sub_comm
    ]

zenoWithDelete :: TestTree
zenoWithDelete =
    testGroup "zenoWithDelete" [
          testProperty "prop_37" ZDelete.prop_37
    ]

zenoWithDrop :: TestTree
zenoWithDrop =
    testGroup "zenoWithDrop" [
          testProperty "prop_01" (ZDrop.prop_01 @Int)
        , testProperty "prop_13" (ZDrop.prop_13 @Int)
        , testProperty "prop_19" (ZDrop.prop_19 @Int)
        , testProperty "prop_56" (ZDrop.prop_56 @Int)
        , testProperty "prop_57" (ZDrop.prop_57 @Int)
        , testProperty "prop_72" (ZDrop.prop_72 @Int)
        , testProperty "prop_74" (ZDrop.prop_74 @Int)
        , testProperty "prop_81" (ZDrop.prop_81 @Int)
        , testProperty "prop_83" (ZDrop.prop_83 @Int @Int)
        , testProperty "prop_84" (ZDrop.prop_84 @Int @Int)
    ]

zenoWithElem :: TestTree
zenoWithElem =
    testGroup "zenoWithElem" [
          testProperty "prop_26" ZElem.prop_26
        , testProperty "prop_37" ZElem.prop_37
        , testProperty "prop_71" ZElem.prop_71
    ]

zenoWithFilter :: TestTree
zenoWithFilter =
    testGroup "zenoWithFilter" [
          testProperty "prop_14" (\(Blind f) -> ZFilter.prop_14 @Int f)
        , testProperty "prop_73" (\(Blind f) -> ZFilter.prop_73 @Int f)
    ]

zenoWithHeight :: TestTree
zenoWithHeight =
    testGroup "zenoWithHeight" [
          testProperty "prop_47" (ZHeight.prop_47 @Int)
    ]

zenoWithIns :: TestTree
zenoWithIns =
    testGroup "zenoWithIns" [
          testProperty "prop_15" ZIns.prop_15
        , testProperty "prop_30" ZIns.prop_30
    ]

zenoWithLen :: TestTree
zenoWithLen =
    testGroup "zenoWithLen" [
          testProperty "prop_15" ZLen.prop_15
        , testProperty "prop_19" (ZLen.prop_19 @Int)
        , testProperty "prop_50" (ZLen.prop_50 @Int)
        , testProperty "prop_55" (ZLen.prop_55 @Int)
        , testProperty "prop_63" ZLen.prop_63
        , testProperty "prop_66" (\(Blind f) -> ZLen.prop_66 @Int f)
        , testProperty "prop_67" (ZLen.prop_67 @Int)
        , testProperty "prop_68" ZLen.prop_68
        , testProperty "prop_72" (ZLen.prop_72 @Int)
        , testProperty "prop_74" (ZLen.prop_74 @Int)
        , testProperty "prop_80" (ZLen.prop_80 @Int)
        , testProperty "prop_83" (ZLen.prop_83 @Int @Int)
        , testProperty "prop_84" (ZLen.prop_84 @Int @Int)
    ]

zenoWithMap :: TestTree
zenoWithMap =
    testGroup "zenoWithMap" [
          testProperty "prop_41" (\n (Blind f) -> ZMap.prop_41 @Int @Int n f)
    ]

zenoWithMirror :: TestTree
zenoWithMirror =
    testGroup "zenoWithMirror" [
          testProperty "prop_47" (ZMirror.prop_47 @Int)
    ]

zenoWithRev :: TestTree
zenoWithRev =
    testGroup "zenoWithRev" [
        testProperty "prop_52" ZRev.prop_52
      , testProperty "prop_72" (ZRev.prop_72 @Int)
      , testProperty "prop_74" (ZRev.prop_74 @Int)
    ]

zenoWithTake :: TestTree
zenoWithTake =
    testGroup "zenoWithTake" [
        testProperty "prop_01" (ZTake.prop_01 @Int)
      , testProperty "prop_42" (ZTake.prop_42 @Int)
      , testProperty "prop_50" (ZTake.prop_50 @Int)
      , testProperty "prop_57" (ZTake.prop_57 @Int)
      , testProperty "prop_72" (ZTake.prop_72 @Int)
      , testProperty "prop_74" (ZTake.prop_74 @Int)
      , testProperty "prop_80" (ZTake.prop_80 @Int)
      , testProperty "prop_81" (ZTake.prop_81 @Int)
      , testProperty "prop_83" (ZTake.prop_83 @Int @Int)
      , testProperty "prop_84" (ZTake.prop_84 @Int @Int)
    ]

zenoWithTakeWhile :: TestTree
zenoWithTakeWhile =
    testGroup "zenoWithTakeWhile" [
        testProperty "prop_36" (ZTakeWhile.prop_36 @Int)
      , testProperty "prop_43" (\(Blind f) -> ZTakeWhile.prop_43 @Int f)
    ]

zenoWithZip :: TestTree
zenoWithZip =
    testGroup "zenoWithZip" [
        testProperty "prop_44" (ZZip.prop_44 @Int @Int)
      , testProperty "prop_45" (ZZip.prop_45 @Int @Int)
      , testProperty "prop_58" (ZZip.prop_58 @Int @Int)
      , testProperty "prop_82" (ZZip.prop_82 @Int @Int)
      , testProperty "prop_83" (ZZip.prop_83 @Int @Int)
      , testProperty "prop_84" (ZZip.prop_84 @Int @Int)
      , testProperty "prop_85" (ZZip.prop_85 @Int @Int)
    ]

zenoBadProp :: TestTree
zenoBadProp =
    testGroup "ZenoBadProp" [
          testProperty "prop_01" (ZBP.prop_01 @Int)
        , testProperty "prop_02" ZBP.prop_02
        , testProperty "prop_03" ZBP.prop_03
        , testProperty "prop_04" ZBP.prop_04
        , testProperty "prop_05" ZBP.prop_05
        , testProperty "prop_06" ZBP.prop_06
        , testProperty "prop_07" ZBP.prop_07
        , testProperty "prop_08" ZBP.prop_08
        , testProperty "prop_09" ZBP.prop_09
        , testProperty "prop_10" ZBP.prop_10
        , testProperty "prop_11" (ZBP.prop_11 @Int)
        , testProperty "prop_12" (\n (Blind f) -> ZBP.prop_12 @Int @Int n f)
        , testProperty "prop_13" (ZBP.prop_13 @Int)
        , testProperty "prop_14" (\(Blind f) -> ZBP.prop_14 @Int f)
        , testProperty "prop_15" ZBP.prop_15
        , testProperty "prop_16" ZBP.prop_16
        , testProperty "prop_17" ZBP.prop_17
        , testProperty "prop_18" ZBP.prop_18
        , testProperty "prop_19" (ZBP.prop_19 @Int)
        , testProperty "prop_20" ZBP.prop_20
        , testProperty "prop_21" ZBP.prop_21
        , testProperty "prop_22" ZBP.prop_22
        , testProperty "prop_23" ZBP.prop_23
        , testProperty "prop_24" ZBP.prop_24
        , testProperty "prop_25" ZBP.prop_25
        , testProperty "prop_26" ZBP.prop_26
        , testProperty "prop_27" ZBP.prop_27
        , testProperty "prop_28" ZBP.prop_28
        , testProperty "prop_29" ZBP.prop_29
        , testProperty "prop_30" ZBP.prop_30
        , testProperty "prop_31" ZBP.prop_31
        , testProperty "prop_32" ZBP.prop_32
        , testProperty "prop_33" ZBP.prop_33
        , testProperty "prop_34" ZBP.prop_34
        , testProperty "prop_35" ZBP.prop_35
        , testProperty "prop_36" ZBP.prop_36
        , testProperty "prop_37" ZBP.prop_37
        , testProperty "prop_38" ZBP.prop_38
        , testProperty "prop_39" ZBP.prop_39
        , testProperty "prop_40" (ZBP.prop_40 @Int)
        , testProperty "prop_41" (\n (Blind f) -> ZBP.prop_41 @Int @Int n f)
        , testProperty "prop_42" (ZBP.prop_42 @Int)
        , testProperty "prop_43" (\(Blind f) -> ZBP.prop_43 @Int f)
        , testProperty "prop_44" (ZBP.prop_44 @Int @Int)
        , testProperty "prop_45" (ZBP.prop_45 @Int @Int)
        , testProperty "prop_46" (ZBP.prop_46 @Int)
        , testProperty "prop_47" (ZBP.prop_47 @Int)
        , testProperty "prop_48" ZBP.prop_48
        , testProperty "prop_49" (ZBP.prop_49 @Int)
        , testProperty "prop_50" (ZBP.prop_50 @Int)
        , testProperty "prop_51" (ZBP.prop_51 @Int)
        , testProperty "prop_52" ZBP.prop_52
        , testProperty "prop_53" ZBP.prop_53
        , testProperty "prop_54" ZBP.prop_54
        , testProperty "prop_55" (ZBP.prop_55 @Int)
        , testProperty "prop_56" (ZBP.prop_56 @Int)
        , testProperty "prop_57" (ZBP.prop_57 @Int)
        , testProperty "prop_58" (ZBP.prop_58 @Int @Int)
        , testProperty "prop_59" ZBP.prop_59
        , testProperty "prop_60" ZBP.prop_60
        , testProperty "prop_61" ZBP.prop_61
        , testProperty "prop_62" ZBP.prop_62
        , testProperty "prop_63" ZBP.prop_63
        , testProperty "prop_64" ZBP.prop_64
        , testProperty "prop_65" ZBP.prop_65
        , testProperty "prop_66" (\(Blind f) -> ZBP.prop_66 @Int f)
        , testProperty "prop_67" (ZBP.prop_67 @Int)
        , testProperty "prop_68" ZBP.prop_68
        , testProperty "prop_69" ZBP.prop_69
        , testProperty "prop_70" ZBP.prop_70
        , testProperty "prop_71" ZBP.prop_71
        , testProperty "prop_72" (ZBP.prop_72 @Int)
        , testProperty "prop_73" (\(Blind f) -> ZBP.prop_73 @Int f)
        , testProperty "prop_74" (ZBP.prop_74 @Int)
        , testProperty "prop_75" ZBP.prop_75
        , testProperty "prop_76" ZBP.prop_76
        , testProperty "prop_77" ZBP.prop_77
        , testProperty "prop_78" ZBP.prop_78
        , testProperty "prop_79" ZBP.prop_79
        , testProperty "prop_80" (ZBP.prop_80 @Int)
        , testProperty "prop_81" (ZBP.prop_81 @Int)
        , testProperty "prop_82" (ZBP.prop_82 @Int @Int)
        , testProperty "prop_83" (ZBP.prop_83 @Int @Int)
        , testProperty "prop_84" (ZBP.prop_84 @Int @Int)
        , testProperty "prop_85" (ZBP.prop_85 @Int @Int)
        ]

instance Arbitrary D.Nat where
    arbitrary = frequency [(8, D.S <$> arbitrary), (1, return D.Z)]

instance Arbitrary N.Nat where
    arbitrary = frequency [(8, N.S <$> arbitrary), (1, return N.Z)]

instance Arbitrary ZDelete.Nat where
    arbitrary = frequency [(8, ZDelete.S <$> arbitrary), (1, return ZDelete.Z)]

instance Arbitrary ZDrop.Nat where
    arbitrary = frequency [(8, ZDrop.S <$> arbitrary), (1, return ZDrop.Z)]

instance Arbitrary ZElem.Nat where
    arbitrary = frequency [(8, ZElem.S <$> arbitrary), (1, return ZElem.Z)]

instance Arbitrary ZIns.Nat where
    arbitrary = frequency [(8, ZIns.S <$> arbitrary), (1, return ZIns.Z)]

instance Arbitrary ZLen.Nat where
    arbitrary = frequency [(8, ZLen.S <$> arbitrary), (1, return ZLen.Z)]

instance Arbitrary ZMap.Nat where
    arbitrary = frequency [(8, ZMap.S <$> arbitrary), (1, return ZMap.Z)]

instance Arbitrary ZRev.Nat where
    arbitrary = frequency [(8, ZRev.S <$> arbitrary), (1, return ZRev.Z)]

instance Arbitrary ZTake.Nat where
    arbitrary = frequency [(8, ZTake.S <$> arbitrary), (1, return ZTake.Z)]

instance Arbitrary ZTakeWhile.Nat where
    arbitrary = frequency [(8, ZTakeWhile.S <$> arbitrary), (1, return ZTakeWhile.Z)]

instance Arbitrary ZZip.Nat where
    arbitrary = frequency [(8, ZZip.S <$> arbitrary), (1, return ZZip.Z)]

instance Arbitrary ZBP.Nat where
    arbitrary = frequency [(8, ZBP.S <$> arbitrary), (1, return ZBP.Z)]

instance CoArbitrary ZBP.Nat where
    coarbitrary ZBP.Z = variant 0
    coarbitrary (ZBP.S x) = variant 1 . coarbitrary x

instance Arbitrary a => Arbitrary (ZBP.Tree a) where
    arbitrary = sized arbTree

arbTree :: Arbitrary a => Int -> Gen (ZBP.Tree a)
arbTree 0 = return ZBP.Leaf
arbTree n = frequency [(4, liftM3 ZBP.Node (arbTree (n `div` 2)) arbitrary (arbTree (n `div` 2))), (1, return ZBP.Leaf)]

instance Arbitrary a => Arbitrary (ZHeight.Tree a) where
    arbitrary = sized arbTreeH

arbTreeH :: Arbitrary a => Int -> Gen (ZHeight.Tree a)
arbTreeH 0 = return ZHeight.Leaf
arbTreeH n = frequency [(4, liftM3 ZHeight.Node (arbTreeH (n `div` 2)) arbitrary (arbTreeH (n `div` 2))), (1, return ZHeight.Leaf)]

instance Arbitrary a => Arbitrary (ZMirror.Tree a) where
    arbitrary = sized arbTreeM

arbTreeM :: Arbitrary a => Int -> Gen (ZMirror.Tree a)
arbTreeM 0 = return ZMirror.Leaf
arbTreeM n = frequency [(4, liftM3 ZMirror.Node (arbTreeM (n `div` 2)) arbitrary (arbTreeM (n `div` 2))), (1, return ZMirror.Leaf)]
