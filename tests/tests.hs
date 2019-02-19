{-# LANGUAGE DataKinds,
             TypeApplications,
             DeriveGeneric,
             StandaloneDeriving,
             PartialTypeSignatures
#-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Main where

import Data.RBR
import Data.SOP
import GHC.Generics (Generic)

import Test.Tasty
import Test.Tasty.HUnit (testCase,Assertion,assertEqual,assertBool)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [ testCase "recordGetSet01" testRecordGetSet01,
                            testCase "variantInjectMatch01" testVariantInjectMatch01,
                            testCase "projectSubset01" testProjectSubset01,
                            testCase "toRecord01" testToRecord01,
                            testCase "fromRecord01" testFromRecord01,
                            testCase "toVariant01" testToVariant01,
                            testCase "fromVariant01" testFromVariant01,
                            testGroup "deletion" [
                                testGroup "records" [
                                    testCase "recordDeletionSingleElem" testRecordDeletionSingleElem,
                                    testCase "recordDeletionLeftElem"   testRecordDeletionLeftElem,
                                    testCase "recordDeletionRightElem"  testRecordDeletionRightElem
                                ],
                                testGroup "variants" [
                                    testCase "variantDeletionSingleElem" testVariantDeletionSingleElem,
                                    testCase "variantDeletionLeftElem" testVariantDeletionLeftElem,
                                    testCase "variantDeletionRightElem" testVariantDeletionRightElem,
                                    testCase "variantDeletion3Elem" testVariantDeletion3Elem,
                                    testCase "variantDeletionMany" testVariantDeletionMany 
                                ]
                            ]
                          ]


testRecordGetSet01 :: Assertion
testRecordGetSet01 = do
    let r = insertI @"bfoo" 'c'
          . insertI @"bbar" True
          . insertI @"bbaz" (1::Int)
          . insertI @"afoo" 'd'
          . insertI @"abar" False
          . insertI @"abaz" (2::Int)
          . insertI @"zfoo" 'x'
          . insertI @"zbar" False
          . insertI @"zbaz" (4::Int)
          . insertI @"dfoo" 'z'
          . insertI @"dbar" True
          . insertI @"dbaz" (5::Int)
          . insertI @"fbaz" (6::Int)
          $ unit
        s = setFieldI @"fbaz" 9 (setFieldI @"zfoo" 'k' r)
    assertEqual "bfoo" (getFieldI  @"bfoo" s) 'c'
    assertEqual "bbar" (getFieldI  @"bbar" s) True
    assertEqual "bbaz" (getFieldI  @"bbaz" s) (1::Int)
    assertEqual "afoo" (getFieldI  @"afoo" s) 'd'
    assertEqual "abar" (getFieldI  @"abar" s) False
    assertEqual "abaz" (getFieldI  @"abaz" s) (2::Int)
    assertEqual "zfoo" (getFieldI  @"zfoo" s) 'k'
    assertEqual "zbar" (getFieldI  @"zbar" s) False
    assertEqual "zbaz" (getFieldI  @"zbaz" s) (4::Int)
    assertEqual "dfoo" (getFieldI  @"dfoo" s) 'z'
    assertEqual "dbar" (getFieldI  @"dbar" s) True
    assertEqual "dbaz" (getFieldI  @"dbaz" s) (5::Int)
    assertEqual "fbaz" (getFieldI  @"fbaz" s) (9::Int)
    return ()

type Tree01 = FromList [ '("bfoo",Char),
                         '("bbar",Bool),
                         '("bbaz",Int),
                         '("afoo",Char),
                         '("abar",Bool),
                         '("abaz",Int),
                         '("zfoo",Char),
                         '("zbar",Bool),
                         '("zbaz",Int),
                         '("dfoo",Char),
                         '("dbar",Bool),
                         '("dbaz",Int),
                         '("fbaz",Int),
                         '("kgoz",Int) ]

testVariantInjectMatch01 :: Assertion
testVariantInjectMatch01 = do
    let r0  =  injectI @"bfoo" @Tree01 'c'
        r1  =  injectI @"bbar" @Tree01 True
        r2  =  injectI @"bbaz" @Tree01 (1::Int)
        r3  =  injectI @"afoo" @Tree01 'd'
        r4  =  injectI @"abar" @Tree01 False
        r5  =  injectI @"abaz" @Tree01 (2::Int)
        r6  =  injectI @"zfoo" @Tree01 'x'
        r7  =  injectI @"zbar" @Tree01 False
        r8  =  injectI @"zbaz" @Tree01 (4::Int)
        r9  =  injectI @"dfoo" @Tree01 'z'
        r10 =  injectI @"dbar" @Tree01 True
        r11 =  injectI @"dbaz" @Tree01 (5::Int)
        r12 =  injectI @"fbaz" @Tree01 (6::Int)
        r13 =  injectI @"kgoz" @Tree01 (9::Int)
    assertEqual "bfoo" (matchI  @"bfoo" r0 ) $ Just 'c'
    assertEqual "bbar" (matchI  @"bbar" r1 ) $ Just True
    assertEqual "bbaz" (matchI  @"bbaz" r2 ) $ Just (1::Int)
    assertEqual "afoo" (matchI  @"afoo" r3 ) $ Just 'd'
    assertEqual "abar" (matchI  @"abar" r4 ) $ Just False
    assertEqual "abaz" (matchI  @"abaz" r5 ) $ Just (2::Int)
    assertEqual "zfoo" (matchI  @"zfoo" r6 ) $ Just 'x'
    assertEqual "zbar" (matchI  @"zbar" r7 ) $ Just False
    assertEqual "zbaz" (matchI  @"zbaz" r8 ) $ Just (4::Int)
    assertEqual "dfoo" (matchI  @"dfoo" r9 ) $ Just 'z'
    assertEqual "dbar" (matchI  @"dbar" r10) $ Just True
    assertEqual "dbaz" (matchI  @"dbaz" r11) $ Just (5::Int)
    assertEqual "fbaz" (matchI  @"fbaz" r12) $ Just (6::Int)
    assertEqual "kgoz" (matchI  @"kgoz" r13) $ Just (9::Int)
    return ()


testProjectSubset01 :: Assertion
testProjectSubset01 = do
    let r = insertI @"foo" 'c'
          . insertI @"bar" True
          . insertI @"baz" (1::Int)
          $ unit
        s = projectSubset @(FromList '[ '("bar",_),
                                        '("baz",_) ]) r
        bar = getFieldI @"bar" s
        baz = getFieldI @"baz" s
    assertEqual "bar" bar True
    assertEqual "baz" baz 1

data Person = Person { name :: String, age :: Int, whatever :: Char } deriving (Generic,Eq,Show)

instance ToRecord Person
instance FromRecord Person

testToRecord01 :: Assertion
testToRecord01 = do
    let r = toRecord (Person "Foo" 50 'z')
    assertEqual "name" "Foo" (getFieldI @"name" r)
    assertEqual "age" 50 (getFieldI @"age" r)
    assertEqual "whatever" 'z' (getFieldI @"whatever" r)

testFromRecord01 :: Assertion
testFromRecord01 = do
    let r = insertI @"name" "Foo"
          . insertI @"age" 50
          . insertI @"whatever" 'z'
          $ unit
    assertEqual "person" (Person "Foo" 50 'z') (fromRecord r)

data Variant01 = Variant01A Int
               | Variant01B Char
               | Variant01C Bool
               | Variant01D Bool
               deriving (Generic,Eq,Show)

instance ToVariant Variant01
instance FromVariant Variant01

testToVariant01 :: Assertion
testToVariant01 = do
    let val1 = Variant01A 0
        val2 = Variant01B 'c'
        val3 = Variant01C True
        cases = addCaseI @"Variant01A" (const 'F')
              . addCaseI @"Variant01B" id
              . addCaseI @"Variant01C" (const 'F')
              . addCaseI @"Variant01D" (const 'F')
              $ unit
        variant = toVariant (Variant01B 'T')
    -- Eliminate would also work because the order of the eliminators is the
    -- same as the order of the cases.
    assertEqual "T" 'T' (eliminateSubset cases variant)

testFromVariant01 :: IO ()
testFromVariant01 = do
    let val1 = fromVariant (injectI @"Variant01A" 1)
        val2 = fromVariant (injectI @"Variant01B" 'z')
        val3 = fromVariant (injectI @"Variant01C" True)
        val4 = fromVariant (injectI @"Variant01D" False)
    assertEqual "Variant01A" val1 (Variant01A 1)
    assertEqual "Variant01B" val2 (Variant01B 'z')
    assertEqual "Variant01C" val3 (Variant01C True)
    assertEqual "Variant01D" val4 (Variant01D False)
 
testRecordDeletionSingleElem :: IO ()
testRecordDeletionSingleElem = do
    let r = insertI @"bar" False
          . insertI @"foo" 'c'
          . delete @"foo" @Bool 
          . insertI @"foo" True
          $ unit
    assertEqual "foo" (getFieldI  @"foo" r) 'c'
    assertEqual "bar" (getFieldI  @"bar" r) False

testVariantDeletionSingleElem :: IO ()
testVariantDeletionSingleElem = do
    let v = injectI @"foo" @(FromList '[ '("foo",Bool) ]) False
        Right r = winnowI @"foo" @Bool v
    assertEqual "foo" False r

testRecordDeletionRightElem :: IO ()
testRecordDeletionRightElem = do
    let r = delete @"foo" @Char
          . insertI @"foo" 'f'
          . insertI @"bar" 'b'
          $ unit
    assertEqual "bar" (getFieldI  @"bar" r) 'b'

testVariantDeletionRightElem :: IO ()
testVariantDeletionRightElem = do
    let v = injectI @"foo" @(FromList '[ '("foo",Bool), '("bar",Char) ]) False
        Left v' = winnowI @"bar" @Char v
        Right r = winnowI @"foo" @Bool v'
    assertEqual "foo" False r

testRecordDeletionLeftElem :: IO ()
testRecordDeletionLeftElem = do
    let r = delete @"bar" @Char
          . insertI @"foo" 'f'
          . insertI @"bar" 'b'
          $ unit
    assertEqual "foo" (getFieldI  @"foo" r) 'f'

testVariantDeletionLeftElem :: IO ()
testVariantDeletionLeftElem = do
    let v = injectI @"bar" @(FromList '[ '("foo",Bool), '("bar",Char) ]) 'b'
        Left v' = winnowI @"foo" @Bool v
        Right r = winnowI @"bar" @Char v'
    assertEqual "bar" 'b' r

type TreeX3 = FromList [ '("bfoo",Char),
                         '("bbar",Bool),
                         '("bbaz",Int)  ]

testVariantDeletion3Elem :: IO ()
testVariantDeletion3Elem = do
    let v = injectI @"bbaz" @TreeX3 1
        Right r = winnowI @"bbaz" @Int v
    assertEqual "bbaz" 1 r


type Tree02 = FromList [ 
                         '("bfoo",Char),
                         '("bbar",Bool),
                         '("bbaz",Int),
                         '("afoo",Char),
                         '("abar",Bool),
                         '("abaz",Int),
                         '("zfoo",Char),
                         '("zbar",Bool),
                         '("zbaz",Int),
                         '("dfoo",Char),
                         '("dbar",Bool),
                         '("dbaz",Int),
                         '("fbaz",Int),
                         '("kgoz",Int) 
                         ]

testVariantDeletionMany :: IO ()
testVariantDeletionMany = do
    let a00 = injectI @"bfoo" @Tree02 'z'
        Left a02 = winnowI @"bbar" @Bool a00
        Left a03 = winnowI @"bbaz" @Int a02
        Left a04 = winnowI @"afoo" @Char a03
        Left a05 = winnowI @"abar" @Bool a04
        Left a06 = winnowI @"abaz" @Int a05
        Left a07 = winnowI @"zfoo" @Char a06
        Left a08 = winnowI @"zbar" @Bool a07
        Left a09 = winnowI @"zbaz" @Int a08
        Left a10 = winnowI @"dfoo" @Char a09
        Left a11 = winnowI @"dbar" @Bool a10
        Left a12 = winnowI @"dbaz" @Int a11
        Left a13 = winnowI @"fbaz" @Int a12
        Left a14 = winnowI @"kgoz" @Int a13
        Right a  = winnowI @"bfoo" @Char a14
    assertEqual "bfoo" a 'z'
    return ()
