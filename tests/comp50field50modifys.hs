
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
          . insertI @"bbar" False
          . insertI @"bbaz" (1::Int)
          . insertI @"afoo" 'd'
          . insertI @"abar" False
          . insertI @"abaz" (2::Int)
          . insertI @"zfoo" 'x'
          . insertI @"zbar" False
          . insertI @"zbaz" (4::Int)
          . insertI @"dfoo" 'z'
          . insertI @"dbar" False
          . insertI @"dbaz" (5::Int)
          . insertI @"fbaz" (6::Int)
          . insertI @"fbax" (6::Int)
          . insertI @"fbay" (6::Int)
          . insertI @"hbfoo" 'c'
          . insertI @"hbbar" False
          . insertI @"hbbaz" (1::Int)
          . insertI @"hafoo" 'd'
          . insertI @"habar" False
          . insertI @"habaz" (2::Int)
          . insertI @"hzfoo" 'x'
          . insertI @"hzbar" False
          . insertI @"hzbaz" (4::Int)
          . insertI @"hdfoo" 'z'
          . insertI @"hdbar" False
          . insertI @"hdbaz" (5::Int)
          . insertI @"hfbaz" (6::Int)
          . insertI @"hfbax" (6::Int)
          . insertI @"hfbay" (6::Int)
          . insertI @"xbfoo" 'c'
          . insertI @"xbbar" False
          . insertI @"xbbaz" (1::Int)
          . insertI @"xafoo" 'd'
          . insertI @"xabar" False
          . insertI @"xabaz" (2::Int)
          . insertI @"xzfoo" 'x'
          . insertI @"xzbar" False
          . insertI @"xzbaz" (4::Int)
          . insertI @"xdfoo" 'z'
          . insertI @"xdbar" False
          . insertI @"xdbaz" (5::Int)
          . insertI @"xfbaz" (6::Int)
          . insertI @"xfbax" (6::Int)
          . insertI @"xfbay" (6::Int)
          . insertI @"kdbar" False
          . insertI @"kdbaz" (5::Int)
          . insertI @"kfbaz" (6::Int)
          . insertI @"kfbax" (6::Int)
          . insertI @"kfbay" (6::Int)
          $ unit
        s = r
    let s' = modifyFieldI @"bfoo"  succ
           . modifyFieldI @"bbar"  succ
           . modifyFieldI @"bbaz"  succ
           . modifyFieldI @"afoo"  succ
           . modifyFieldI @"abar"  succ
           . modifyFieldI @"abaz"  succ
           . modifyFieldI @"zfoo"  succ
           . modifyFieldI @"zbar"  succ
           . modifyFieldI @"zbaz"  succ
           . modifyFieldI @"dfoo"  succ
           . modifyFieldI @"dbar"  succ
           . modifyFieldI @"dbaz"  succ
           . modifyFieldI @"fbaz"  succ
           . modifyFieldI @"fbax"  succ
           . modifyFieldI @"fbay"  succ
           . modifyFieldI @"hbfoo" succ
           . modifyFieldI @"hbbar" succ
           . modifyFieldI @"hbbaz" succ
           . modifyFieldI @"hafoo" succ
           . modifyFieldI @"habar" succ
           . modifyFieldI @"habaz" succ
           . modifyFieldI @"hzfoo" succ
           . modifyFieldI @"hzbar" succ
           . modifyFieldI @"hzbaz" succ
           . modifyFieldI @"hdfoo" succ
           . modifyFieldI @"hdbar" succ
           . modifyFieldI @"hdbaz" succ
           . modifyFieldI @"hfbaz" succ
           . modifyFieldI @"hfbax" succ
           . modifyFieldI @"hfbay" succ
           . modifyFieldI @"xbfoo" succ
           . modifyFieldI @"xbbar" succ
           . modifyFieldI @"xbbaz" succ
           . modifyFieldI @"xafoo" succ
           . modifyFieldI @"xabar" succ
           . modifyFieldI @"xabaz" succ
           . modifyFieldI @"xzfoo" succ
           . modifyFieldI @"xzbar" succ
           . modifyFieldI @"xzbaz" succ
           . modifyFieldI @"xdfoo" succ
           . modifyFieldI @"xdbar" succ
           . modifyFieldI @"xdbaz" succ
           . modifyFieldI @"xfbaz" succ
           . modifyFieldI @"xfbax" succ
           . modifyFieldI @"xfbay" succ
           . modifyFieldI @"kdbar" succ
           . modifyFieldI @"kdbaz" succ
           . modifyFieldI @"kfbaz" succ
           . modifyFieldI @"kfbax" succ
           . modifyFieldI @"kfbay" succ
           $ s
    print s'
    return ()

--
--
--
