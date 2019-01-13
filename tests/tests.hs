{-# LANGUAGE DataKinds,
             TypeApplications,
             DeriveGeneric,
             StandaloneDeriving,
             PartialTypeSignatures
#-}
{-#  OPTIONS_GHC -Wno-partial-type-signatures  #-}
module Main where

import Data.RBR
import Data.SOP
import GHC.Generics (Generic)

import Test.Tasty
import Test.Tasty.HUnit (testCase,assertEqual,assertBool)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [ testCase "testProjectSubset01" testProjectSubset01,
                            testCase "testToVariant01" testToVariant01
                          ]

testProjectSubset01 :: IO ()
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


data Variant01 = Variant01A Int
               | Variant01B Char
               | Variant01C Bool
               deriving (Generic,Show)

instance ToVariant Variant01

testToVariant01 :: IO ()
testToVariant01 = do
    let val1 = Variant01A 0
        val2 = Variant01B 'c'
        val3 = Variant01C True
        cases = addCaseI @"Variant01A" (const 'F')
              . addCaseI @"Variant01B" id
              . addCaseI @"Variant01C" (const 'F')
              $ unit
        variant = toVariant (Variant01B 'T')
    -- Eliminate would also work because the order of the eliminators is the
    -- same as the order of the cases.
    print $ eliminateSubset cases variant

