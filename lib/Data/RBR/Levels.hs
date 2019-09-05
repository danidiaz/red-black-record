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

data Levels s q = Product_ (Map s (Levels s q))
                | Sum_ (Map s (Levels s q))
                | Leaf_ q
                deriving (Show,Eq)

newtype Y (levelz :: Levels Symbol Type) = Y (Multilevel levelz) 

data Multilevel (levels :: Levels Symbol Type)  where
    Atom :: v -> Multilevel (Leaf_ v)
    Record :: Record Y t -> Multilevel (Product_ t)
    Variant :: Variant Y t -> Multilevel (Sum_ t)

type (::>) a b = '(a, b)
type (::.) a b = '(a, Leaf_ b)

type family ProductOf (input :: [(Symbol,Levels Symbol q)]) :: Levels Symbol q where
    ProductOf pairs = Product_ (FromList pairs)

type family SumOf (input :: [(Symbol,Levels Symbol q)]) :: Levels Symbol q where
    SumOf pairs = Sum_ (FromList pairs)

foo :: Multilevel (Product_ (FromList '[ '("foo", Leaf_ Char),
                                        '("bar", Sum_ (FromList '[ '("sub1", Leaf_ Char),
                                                                  '("sub2", Sum_ (FromList '[ '("subsub1", Leaf_ Int), 
                                                                                             '("subsub2", Leaf_ Char) ]))]))]))
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
                                        "subsub1" ::. Int,
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
