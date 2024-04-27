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
import TypeLevelRecordDot

import GHC.Generics (Generic, Generically(..))

import Test.Tasty
import Test.Tasty.HUnit (testCase,Assertion,assertEqual,assertBool)

main :: IO ()
main = defaultMain tests


data Person = Person { 
    personName :: String, 
    address :: Address,
    func :: Bool -> Int -> Address 
    }
    deriving stock (Generic)

data Address = Address { 
    street :: String, 
    number :: Int, 
    other :: Int
    }
    deriving stock (Generic)

-- | Checking that 'Dot' has the proper associativity...
foo :: Person `Dot` "address" `Dot` "number" 
foo = 5

foof :: Person `Dot` "func" `Dot` "number" 
foof = \_ _ -> 3

tests :: TestTree
tests = testGroup "Tests" [ testCase "generically" testGenerically
    ]

testGenerically :: Assertion
testGenerically = do
    let r = Person "Foo" (Address "Somestreet" 1 2 ) (\_ _ -> Address "Somestreet" 1 2)
        a = Data.RBR.getFieldI @"address" (Data.RBR.toRecord (Generically r))
        n = Data.RBR.getFieldI @"number" (Data.RBR.toRecord (Generically a))
    assertEqual "number" n 1
