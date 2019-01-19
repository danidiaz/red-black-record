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
tests = testGroup "Tests" [ testCase "testRecordGetSet01" testRecordGetSet01
                          ]


testRecordGetSet01 :: Assertion
testRecordGetSet01 = do
    let r = 
            insertI @"bfoo" 'c'
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
          . insertI @"fbax" (6::Int)
          . insertI @"fbay" (6::Int)
          . insertI @"hbfoo" 'c'
          . insertI @"hbbar" True
          . insertI @"hbbaz" (1::Int)
          . insertI @"hafoo" 'd'
          . insertI @"habar" False
          . insertI @"habaz" (2::Int)
          . insertI @"hzfoo" 'x'
          . insertI @"hzbar" False
          . insertI @"hzbaz" (4::Int)
          . insertI @"hdfoo" 'z'
          . insertI @"hdbar" True
          . insertI @"hdbaz" (5::Int)
          . insertI @"hfbaz" (6::Int)
          . insertI @"hfbax" (6::Int)
          . insertI @"hfbay" (6::Int)
          . insertI @"xbfoo" 'c'
          . insertI @"xbbar" True
          . insertI @"xbbaz" (1::Int)
          . insertI @"xafoo" 'd'
          . insertI @"xabar" False
          . insertI @"xabaz" (2::Int)
          . insertI @"xzfoo" 'x'
          . insertI @"xzbar" False
          . insertI @"xzbaz" (4::Int)
          . insertI @"xdfoo" 'z'
          . insertI @"xdbar" True
          . insertI @"xdbaz" (5::Int)
          . insertI @"xfbaz" (6::Int)
          . insertI @"xfbax" (6::Int)
          . insertI @"xfbay" (6::Int)
          . insertI @"kdbar" True
          . insertI @"kdbaz" (5::Int)
          . insertI @"kfbaz" (6::Int)
          . insertI @"kfbax" (6::Int)
          . insertI @"kfbay" (6::Int)
          $ unit
        s = r
    assertEqual "bfoo" (getFieldI  @"bfoo" s) 'c'
    assertEqual "bbar" (getFieldI  @"bbar" s) True
    assertEqual "bbaz" (getFieldI  @"bbaz" s) (1::Int)
    assertEqual "afoo" (getFieldI  @"afoo" s) 'd'
    assertEqual "abar" (getFieldI  @"abar" s) False
    assertEqual "abaz" (getFieldI  @"abaz" s) (2::Int)
    assertEqual "zfoo" (getFieldI  @"zfoo" s) 'x'
    assertEqual "zbar" (getFieldI  @"zbar" s) False
    assertEqual "zbaz" (getFieldI  @"zbaz" s) (4::Int)
    assertEqual "dfoo" (getFieldI  @"dfoo" s) 'z'
    assertEqual "dbar" (getFieldI  @"dbar" s) True
    assertEqual "dbaz" (getFieldI  @"dbaz" s) (5::Int)
    assertEqual "fbaz" (getFieldI  @"fbaz" s) (6::Int)
    assertEqual "fbax" (getFieldI  @"fbaz" s) (6::Int)
    assertEqual "fbay" (getFieldI  @"fbaz" s) (6::Int)
    assertEqual "bfoo" (getFieldI  @"hbfoo" s) 'c'
    assertEqual "bbar" (getFieldI  @"hbbar" s) True
    assertEqual "bbaz" (getFieldI  @"hbbaz" s) (1::Int)
    assertEqual "afoo" (getFieldI  @"hafoo" s) 'd'
    assertEqual "abar" (getFieldI  @"habar" s) False
    assertEqual "abaz" (getFieldI  @"habaz" s) (2::Int)
    assertEqual "zfoo" (getFieldI  @"hzfoo" s) 'x'
    assertEqual "zbar" (getFieldI  @"hzbar" s) False
    assertEqual "zbaz" (getFieldI  @"hzbaz" s) (4::Int)
    assertEqual "dfoo" (getFieldI  @"hdfoo" s) 'z'
    assertEqual "dbar" (getFieldI  @"hdbar" s) True
    assertEqual "dbaz" (getFieldI  @"hdbaz" s) (5::Int)
    assertEqual "fbaz" (getFieldI  @"hfbaz" s) (6::Int)
    assertEqual "fbax" (getFieldI  @"hfbaz" s) (6::Int)
    assertEqual "fbay" (getFieldI  @"hfbaz" s) (6::Int)
    assertEqual "bfoo" (getFieldI  @"xbfoo" s) 'c'
    assertEqual "bbar" (getFieldI  @"xbbar" s) True
    assertEqual "bbaz" (getFieldI  @"xbbaz" s) (1::Int)
    assertEqual "afoo" (getFieldI  @"xafoo" s) 'd'
    assertEqual "abar" (getFieldI  @"xabar" s) False
    assertEqual "abaz" (getFieldI  @"xabaz" s) (2::Int)
    assertEqual "zfoo" (getFieldI  @"xzfoo" s) 'x'
    assertEqual "zbar" (getFieldI  @"xzbar" s) False
    assertEqual "zbaz" (getFieldI  @"xzbaz" s) (4::Int)
    assertEqual "dfoo" (getFieldI  @"xdfoo" s) 'z'
    assertEqual "dbar" (getFieldI  @"xdbar" s) True
    assertEqual "dbaz" (getFieldI  @"xdbaz" s) (5::Int)
    assertEqual "fbaz" (getFieldI  @"xfbaz" s) (6::Int)
    assertEqual "fbax" (getFieldI  @"xfbaz" s) (6::Int)
    assertEqual "fbay" (getFieldI  @"xfbaz" s) (6::Int)
    assertEqual "kbar" (getFieldI  @"xdbar" s) True
    assertEqual "kbaz" (getFieldI  @"xdbaz" s) (5::Int)
    assertEqual "kbaz" (getFieldI  @"xfbaz" s) (6::Int)
    assertEqual "kbax" (getFieldI  @"xfbaz" s) (6::Int)
    assertEqual "kbay" (getFieldI  @"xfbaz" s) (6::Int)
    return ()

