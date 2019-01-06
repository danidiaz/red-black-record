module Main where

import Test.Tasty
import Test.Tasty.HUnit (testCase,assertEqual,assertBool)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [
                          ]
