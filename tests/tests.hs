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
tests = testGroup "Tests" [ testCase "testProjectSubset01" testProjectSubset01,
                            testCase "testToRecord01" testToRecord01,
                            testCase "testFromRecord01" testFromRecord01,
                            testCase "testToVariant01" testToVariant01,
                            testCase "testFromVariant01" testFromVariant01
                          ]

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

