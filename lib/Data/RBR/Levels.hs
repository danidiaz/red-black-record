{-# LANGUAGE DataKinds,
             TypeOperators,
             ConstraintKinds,
             PolyKinds,
             TypeFamilies,
             GADTs,
             MultiParamTypeClasses,
             FunctionalDependencies,
             FlexibleInstances,
             FlexibleContexts,
             UndecidableInstances,
             UndecidableSuperClasses,
             TypeApplications,
             ScopedTypeVariables,
             AllowAmbiguousTypes,
             ExplicitForAll,
             RankNTypes, 
             DefaultSignatures,
             PartialTypeSignatures,
             LambdaCase,
             EmptyCase 
#-}
{-#  OPTIONS_GHC -Wno-partial-type-signatures  #-}
module Data.RBR.Levels where

import           Data.Proxy
import           Data.Kind
import           GHC.TypeLits

import           Data.SOP (I(..))
import           Data.RBR.Internal

data Levels s q = Product (Map s (Levels s q))
                | Sum (Map s (Levels s q))
                | Leaf q
                deriving (Show,Eq)

newtype Y (levelz :: Levels Symbol Type) = Y (Multilevel levelz) 

data Multilevel (levels :: Levels Symbol Type)  where
    Atom :: v -> Multilevel (Leaf v)
    Record :: Record Y t -> Multilevel (Product t)
    Variant :: Variant Y t -> Multilevel (Sum t)

type (::>) a b = '(a, b)
type (::.) a b = '(a, Atom b)

type family ProductOf (input :: [(Symbol,Levels Symbol q)]) :: Levels Symbol q where
    ProductOf pairs = Product (FromList pairs)

type family SumOf (input :: [(Symbol,Levels Symbol q)]) :: Levels Symbol q where
    SumOf pairs = Sum (FromList pairs)

foo :: Multilevel (Product (FromList '[ '("foo", Leaf Char),
                                        '("bar", Sum (FromList '[ '("sub1", Leaf Char),
                                                                  '("sub2", Sum (FromList '[ '("subsub1", Leaf Int), 
                                                                                             '("subsub2", Leaf Char) ]))]))]))
foo = Record $ insert @"foo" (Y (Atom 'a'))
             . insert @"bar" (Y (Variant $ inject @"sub1" (Y (Atom 'a'))))
             $ unit


bar :: Multilevel (ProductOf [
                        "foo" ::. Char,
                        "bar" ::>
                            SumOf [
                                "sub1" ::. Char,
                                "sub2" ::>
                                    SumOf [
                                        "subsub1" ::. Int
                                        "subsub2" ::. Char
                                    ]
                            ]
                  ])
bar = Record $ insert @"foo" (Y (Atom 'a'))
             . insert @"bar" (Y (Variant $ inject @"sub1" (Y (Atom 'a'))))
             $ unit


foodo :: Char
foodo = case foo of
    Record thefoo -> case (getField @"foo"  thefoo) of
        Y (Atom c) -> c
