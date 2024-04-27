{-# LANGUAGE DataKinds,
             TypeOperators,
             TypeFamilies,
             TypeApplications,
             DeriveGeneric,
             StandaloneDeriving,
             DerivingStrategies,
             UndecidableInstances,
             KindSignatures,
             PartialTypeSignatures,
             FlexibleContexts,
             ScopedTypeVariables
#-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Main where

import Data.RBR

import GHC.Generics (Generic, Generically(..))

import Test.Tasty
import Test.Tasty.HUnit (testCase,Assertion,assertEqual,assertBool)

main :: IO ()
main = defaultMain tests

data Person = Person { personName :: String, address :: Address }
    deriving stock (Show, Generic)

data Address = Address { street :: String, number :: Int, other :: Int }
    deriving stock (Show, Generic)

tests :: TestTree
tests = testGroup "Tests" [ testCase "generically" testGenerically
    ]

testGenerically :: Assertion
testGenerically = do
    let r = Person "Foo" (Address "Somestreet" 1 2)
        a = Data.RBR.getFieldI @"address" (Data.RBR.toRecord (Generically r))
        n = Data.RBR.getFieldI @"number" (Data.RBR.toRecord (Generically a))
    assertEqual "number" n 1
