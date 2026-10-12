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
import Test.Tasty.HUnit
import qualified Test.QuickCheck as QC

-- Pass:
-- --min-duration-to-report 0s
-- on the command line to make sure we get times for all tests
main :: IO ()
main = do
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

myTestProperty :: Testable prop => String -> String -> prop -> TestTree
myTestProperty bench name prop =
    testCase name $ do
        result <- QC.quickCheckResult $ property prop
        case result of
            QC.Success {QC.numTests = n
                       , QC.numDiscarded = d} -> putStrLn $ " Benchmark: " ++ bench ++ " Property: " ++ name ++ " Passed: " ++ show n ++ ", Discarded: " ++ show d
            QC.Failure { QC.numTests = n
                       , QC.numDiscarded = d } -> error $ " Benchmark: " ++ bench ++ " Property: " ++ name ++
                        " Failed after " ++ show n ++
                    " tests, Discarded: " ++ show d 
            _ -> error $ output result
        -- case result of
        --     QC.Success {} -> putStrLn ("Benchmark: " ++ bench ++ " Property: " ++ name ++ "\n")
        --     _ -> error $ "Benchmark: " ++ bench ++ " Property: " ++ name ++ "\n" ++  output result ++ "\ndiscarded " ++ show (numDiscarded result)

definitions :: TestTree
definitions =
    testGroup "Definitions" [
          myTestProperty "Definitions" "prop_rot_bogus" D.prop_rot_bogus
        , myTestProperty "Definitions" "prop_len_bs" D.prop_len_bs
        , myTestProperty "Definitions" "prop_drop_idem" D.prop_drop_idem
        , myTestProperty "Definitions" "prop_drop_invol" D.prop_drop_invol
        , myTestProperty "Definitions" "prop_drop_inj1" D.prop_drop_inj1
        , myTestProperty "Definitions" "prop_drop_inj2" D.prop_drop_inj2
        , myTestProperty "Definitions" "prop_union_comm" D.prop_union_comm
        , myTestProperty "Definitions" "prop_rot_inj0" D.prop_rot_inj0
        , myTestProperty "Definitions" "prop_rot_uhhhw1" D.prop_rot_uhhhw1
        , myTestProperty "Definitions" "prop_rot_uhhhw2" D.prop_rot_uhhhw2
    ]

nat :: TestTree
nat =
    testGroup "Nat" [
          myTestProperty "Nat" "plus_idem" N.plus_idem
        , myTestProperty "Nat" "plus_not_idem" N.plus_not_idem
        , myTestProperty "Nat" "plus_inf" N.plus_inf
        , myTestProperty "Nat" "mul_idem" N.mul_idem
        , myTestProperty "Nat" "silly" N.silly
        , myTestProperty "Nat" "sub_assoc" N.sub_assoc
        , myTestProperty "Nat" "not_trans" N.not_trans
        , myTestProperty "Nat" "sub_comm" N.sub_comm
    ]

zenoWithDelete :: TestTree
zenoWithDelete =
    testGroup "zenoWithDelete" [
          myTestProperty "zenoWithDelete" "prop_37" ZDelete.prop_37
    ]

zenoWithDrop :: TestTree
zenoWithDrop =
    testGroup "zenoWithDrop" [
          myTestProperty "zenoWithDrop" "prop_01" (ZDrop.prop_01 @Int)
        , myTestProperty "zenoWithDrop" "prop_13" (ZDrop.prop_13 @Int)
        , myTestProperty "zenoWithDrop" "prop_19" (ZDrop.prop_19 @Int)
        , myTestProperty "zenoWithDrop" "prop_56" (ZDrop.prop_56 @Int)
        , myTestProperty "zenoWithDrop" "prop_57" (ZDrop.prop_57 @Int)
        , myTestProperty "zenoWithDrop" "prop_72" (ZDrop.prop_72 @Int)
        , myTestProperty "zenoWithDrop" "prop_74" (ZDrop.prop_74 @Int)
        , myTestProperty "zenoWithDrop" "prop_81" (ZDrop.prop_81 @Int)
        , myTestProperty "zenoWithDrop" "prop_83" (ZDrop.prop_83 @Int @Int)
        , myTestProperty "zenoWithDrop" "prop_84" (ZDrop.prop_84 @Int @Int)
    ]

zenoWithElem :: TestTree
zenoWithElem =
    testGroup "zenoWithElem" [
          myTestProperty "zenoWithElem" "prop_26" ZElem.prop_26
        , myTestProperty "zenoWithElem" "prop_37" ZElem.prop_37
        , myTestProperty "zenoWithElem" "prop_71" ZElem.prop_71
    ]

zenoWithFilter :: TestTree
zenoWithFilter =
    testGroup "zenoWithFilter" [
          myTestProperty "zenoWithFilter" "prop_14" (\(Blind f) -> ZFilter.prop_14 @Int f)
        , myTestProperty "zenoWithFilter" "prop_73" (\(Blind f) -> ZFilter.prop_73 @Int f)
    ]

zenoWithHeight :: TestTree
zenoWithHeight =
    testGroup "zenoWithHeight" [
          myTestProperty "zenoWithHeight" "prop_47" (ZHeight.prop_47 @Int)
    ]

zenoWithIns :: TestTree
zenoWithIns =
    testGroup "zenoWithIns" [
          myTestProperty "zenoWithIns" "prop_15" ZIns.prop_15
        , myTestProperty "zenoWithIns" "prop_30" ZIns.prop_30
    ]

zenoWithLen :: TestTree
zenoWithLen =
    testGroup "zenoWithLen" [
          myTestProperty "zenoWithLen" "prop_15" ZLen.prop_15
        , myTestProperty "zenoWithLen" "prop_19" (ZLen.prop_19 @Int)
        , myTestProperty "zenoWithLen" "prop_50" (ZLen.prop_50 @Int)
        , myTestProperty "zenoWithLen" "prop_55" (ZLen.prop_55 @Int)
        , myTestProperty "zenoWithLen" "prop_63" ZLen.prop_63
        , myTestProperty "zenoWithLen" "prop_66" (\(Blind f) -> ZLen.prop_66 @Int f)
        , myTestProperty "zenoWithLen" "prop_67" (ZLen.prop_67 @Int)
        , myTestProperty "zenoWithLen" "prop_68" ZLen.prop_68
        , myTestProperty "zenoWithLen" "prop_72" (ZLen.prop_72 @Int)
        , myTestProperty "zenoWithLen" "prop_74" (ZLen.prop_74 @Int)
        , myTestProperty "zenoWithLen" "prop_80" (ZLen.prop_80 @Int)
        , myTestProperty "zenoWithLen" "prop_83" (ZLen.prop_83 @Int @Int)
        , myTestProperty "zenoWithLen" "prop_84" (ZLen.prop_84 @Int @Int)
    ]

zenoWithMap :: TestTree
zenoWithMap =
    testGroup "zenoWithMap" [
          myTestProperty "zenoWithMap" "prop_41" (\n (Blind f) -> ZMap.prop_41 @Int @Int n f)
    ]

zenoWithMirror :: TestTree
zenoWithMirror =
    testGroup "zenoWithMirror" [
          myTestProperty "zenoWithMirror" "prop_47" (ZMirror.prop_47 @Int)
    ]

zenoWithRev :: TestTree
zenoWithRev =
    testGroup "zenoWithRev" [
        myTestProperty "zenoWithRev" "prop_52" ZRev.prop_52
      , myTestProperty "zenoWithRev" "prop_72" (ZRev.prop_72 @Int)
      , myTestProperty "zenoWithRev" "prop_74" (ZRev.prop_74 @Int)
    ]

zenoWithTake :: TestTree
zenoWithTake =
    testGroup "zenoWithTake" [
        myTestProperty "zenoWithTake" "prop_01" (ZTake.prop_01 @Int)
      , myTestProperty "zenoWithTake" "prop_42" (ZTake.prop_42 @Int)
      , myTestProperty "zenoWithTake" "prop_50" (ZTake.prop_50 @Int)
      , myTestProperty "zenoWithTake" "prop_57" (ZTake.prop_57 @Int)
      , myTestProperty "zenoWithTake" "prop_72" (ZTake.prop_72 @Int)
      , myTestProperty "zenoWithTake" "prop_74" (ZTake.prop_74 @Int)
      , myTestProperty "zenoWithTake" "prop_80" (ZTake.prop_80 @Int)
      , myTestProperty "zenoWithTake" "prop_81" (ZTake.prop_81 @Int)
      , myTestProperty "zenoWithTake" "prop_83" (ZTake.prop_83 @Int @Int)
      , myTestProperty "zenoWithTake" "prop_84" (ZTake.prop_84 @Int @Int)
    ]

zenoWithTakeWhile :: TestTree
zenoWithTakeWhile =
    testGroup "zenoWithTakeWhile" [
        myTestProperty "zenoWithTakeWhile" "prop_36" (ZTakeWhile.prop_36 @Int)
      , myTestProperty "zenoWithTakeWhile" "prop_43" (\(Blind f) -> ZTakeWhile.prop_43 @Int f)
    ]

zenoWithZip :: TestTree
zenoWithZip =
    testGroup "zenoWithZip" [
        myTestProperty "zenoWithZip" "prop_44" (ZZip.prop_44 @Int @Int)
      , myTestProperty "zenoWithZip" "prop_45" (ZZip.prop_45 @Int @Int)
      , myTestProperty "zenoWithZip" "prop_58" (ZZip.prop_58 @Int @Int)
      , myTestProperty "zenoWithZip" "prop_82" (ZZip.prop_82 @Int @Int)
      , myTestProperty "zenoWithZip" "prop_83" (ZZip.prop_83 @Int @Int)
      , myTestProperty "zenoWithZip" "prop_84" (ZZip.prop_84 @Int @Int)
      , myTestProperty "zenoWithZip" "prop_85" (ZZip.prop_85 @Int @Int)
    ]

zenoBadProp :: TestTree
zenoBadProp =
    testGroup "ZenoBadProp" [
          myTestProperty "ZenoBadProp" "prop_01" (ZBP.prop_01 @Int)
        , myTestProperty "ZenoBadProp" "prop_02" ZBP.prop_02
        , myTestProperty "ZenoBadProp" "prop_03" ZBP.prop_03
        , myTestProperty "ZenoBadProp" "prop_04" ZBP.prop_04
        , myTestProperty "ZenoBadProp" "prop_05" ZBP.prop_05
        , myTestProperty "ZenoBadProp" "prop_06" ZBP.prop_06
        , myTestProperty "ZenoBadProp" "prop_07" ZBP.prop_07
        , myTestProperty "ZenoBadProp" "prop_08" ZBP.prop_08
        , myTestProperty "ZenoBadProp" "prop_09" ZBP.prop_09
        , myTestProperty "ZenoBadProp" "prop_10" ZBP.prop_10
        , myTestProperty "ZenoBadProp" "prop_11" (ZBP.prop_11 @Int)
        , myTestProperty "ZenoBadProp" "prop_12" (\n (Blind f) -> ZBP.prop_12 @Int @Int n f)
        , myTestProperty "ZenoBadProp" "prop_13" (ZBP.prop_13 @Int)
        , myTestProperty "ZenoBadProp" "prop_14" (\(Blind f) -> ZBP.prop_14 @Int f)
        , myTestProperty "ZenoBadProp" "prop_15" ZBP.prop_15
        , myTestProperty "ZenoBadProp" "prop_16" ZBP.prop_16
        , myTestProperty "ZenoBadProp" "prop_17" ZBP.prop_17
        , myTestProperty "ZenoBadProp" "prop_18" ZBP.prop_18
        , myTestProperty "ZenoBadProp" "prop_19" (ZBP.prop_19 @Int)
        , myTestProperty "ZenoBadProp" "prop_20" ZBP.prop_20
        , myTestProperty "ZenoBadProp" "prop_21" ZBP.prop_21
        , myTestProperty "ZenoBadProp" "prop_22" ZBP.prop_22
        , myTestProperty "ZenoBadProp" "prop_23" ZBP.prop_23
        , myTestProperty "ZenoBadProp" "prop_24" ZBP.prop_24
        , myTestProperty "ZenoBadProp" "prop_25" ZBP.prop_25
        , myTestProperty "ZenoBadProp" "prop_26" ZBP.prop_26
        , myTestProperty "ZenoBadProp" "prop_27" ZBP.prop_27
        , myTestProperty "ZenoBadProp" "prop_28" ZBP.prop_28
        , myTestProperty "ZenoBadProp" "prop_29" ZBP.prop_29
        , myTestProperty "ZenoBadProp" "prop_30" ZBP.prop_30
        , myTestProperty "ZenoBadProp" "prop_31" ZBP.prop_31
        , myTestProperty "ZenoBadProp" "prop_32" ZBP.prop_32
        , myTestProperty "ZenoBadProp" "prop_33" ZBP.prop_33
        , myTestProperty "ZenoBadProp" "prop_34" ZBP.prop_34
        , myTestProperty "ZenoBadProp" "prop_35" ZBP.prop_35
        , myTestProperty "ZenoBadProp" "prop_36" ZBP.prop_36
        , myTestProperty "ZenoBadProp" "prop_37" ZBP.prop_37
        , myTestProperty "ZenoBadProp" "prop_38" ZBP.prop_38
        , myTestProperty "ZenoBadProp" "prop_39" ZBP.prop_39
        , myTestProperty "ZenoBadProp" "prop_40" (ZBP.prop_40 @Int)
        , myTestProperty "ZenoBadProp" "prop_41" (\n (Blind f) -> ZBP.prop_41 @Int @Int n f)
        , myTestProperty "ZenoBadProp" "prop_42" (ZBP.prop_42 @Int)
        , myTestProperty "ZenoBadProp" "prop_43" (\(Blind f) -> ZBP.prop_43 @Int f)
        , myTestProperty "ZenoBadProp" "prop_44" (ZBP.prop_44 @Int @Int)
        , myTestProperty "ZenoBadProp" "prop_45" (ZBP.prop_45 @Int @Int)
        , myTestProperty "ZenoBadProp" "prop_46" (ZBP.prop_46 @Int)
        , myTestProperty "ZenoBadProp" "prop_47" (ZBP.prop_47 @Int)
        , myTestProperty "ZenoBadProp" "prop_48" ZBP.prop_48
        , myTestProperty "ZenoBadProp" "prop_49" (ZBP.prop_49 @Int)
        , myTestProperty "ZenoBadProp" "prop_50" (ZBP.prop_50 @Int)
        , myTestProperty "ZenoBadProp" "prop_51" (ZBP.prop_51 @Int)
        , myTestProperty "ZenoBadProp" "prop_52" ZBP.prop_52
        , myTestProperty "ZenoBadProp" "prop_53" ZBP.prop_53
        , myTestProperty "ZenoBadProp" "prop_54" ZBP.prop_54
        , myTestProperty "ZenoBadProp" "prop_55" (ZBP.prop_55 @Int)
        , myTestProperty "ZenoBadProp" "prop_56" (ZBP.prop_56 @Int)
        , myTestProperty "ZenoBadProp" "prop_57" (ZBP.prop_57 @Int)
        , myTestProperty "ZenoBadProp" "prop_58" (ZBP.prop_58 @Int @Int)
        , myTestProperty "ZenoBadProp" "prop_59" ZBP.prop_59
        , myTestProperty "ZenoBadProp" "prop_60" ZBP.prop_60
        , myTestProperty "ZenoBadProp" "prop_61" ZBP.prop_61
        , myTestProperty "ZenoBadProp" "prop_62" ZBP.prop_62
        , myTestProperty "ZenoBadProp" "prop_63" ZBP.prop_63
        , myTestProperty "ZenoBadProp" "prop_64" ZBP.prop_64
        , myTestProperty "ZenoBadProp" "prop_65" ZBP.prop_65
        , myTestProperty "ZenoBadProp" "prop_66" (\(Blind f) -> ZBP.prop_66 @Int f)
        , myTestProperty "ZenoBadProp" "prop_67" (ZBP.prop_67 @Int)
        , myTestProperty "ZenoBadProp" "prop_68" ZBP.prop_68
        , myTestProperty "ZenoBadProp" "prop_69" ZBP.prop_69
        , myTestProperty "ZenoBadProp" "prop_70" ZBP.prop_70
        , myTestProperty "ZenoBadProp" "prop_71" ZBP.prop_71
        , myTestProperty "ZenoBadProp" "prop_72" (ZBP.prop_72 @Int)
        , myTestProperty "ZenoBadProp" "prop_73" (\(Blind f) -> ZBP.prop_73 @Int f)
        , myTestProperty "ZenoBadProp" "prop_74" (ZBP.prop_74 @Int)
        , myTestProperty "ZenoBadProp"  "prop_75" ZBP.prop_75
        , myTestProperty "ZenoBadProp" "prop_76" ZBP.prop_76
        , myTestProperty "ZenoBadProp" "prop_77" ZBP.prop_77
        , myTestProperty "ZenoBadProp" "prop_78" ZBP.prop_78
        , myTestProperty "ZenoBadProp" "prop_79" ZBP.prop_79
        , myTestProperty "ZenoBadProp" "prop_80" (ZBP.prop_80 @Int)
        , myTestProperty "ZenoBadProp" "prop_81" (ZBP.prop_81 @Int)
        , myTestProperty "ZenoBadProp" "prop_82" (ZBP.prop_82 @Int @Int)
        , myTestProperty "ZenoBadProp" "prop_83" (ZBP.prop_83 @Int @Int)
        , myTestProperty "ZenoBadProp" "prop_84" (ZBP.prop_84 @Int @Int)
        , myTestProperty "ZenoBadProp" "prop_85" (ZBP.prop_85 @Int @Int)
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
