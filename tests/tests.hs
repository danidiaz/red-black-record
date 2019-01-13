{-# LANGUAGE DataKinds,
             TypeApplications,
             PartialTypeSignatures
#-}
{-#  OPTIONS_GHC -Wno-partial-type-signatures  #-}
module Main where

import Data.RBR
import Data.SOP

import Test.Tasty
import Test.Tasty.HUnit (testCase,assertEqual,assertBool)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [ testCase "testProjectSubset01" testProjectSubset01
                          ]

testProjectSubset01 :: IO ()
testProjectSubset01  = do
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

