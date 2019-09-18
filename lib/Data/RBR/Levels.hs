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

import           Data.SOP (I(..),(:.:)(..))
import           Data.RBR.Internal hiding (Node)

data Levels o s q = Node o (Map s (Levels o s q))
                  | Leaf q
                  deriving (Show,Eq)

data Operation = Product
               | Sum
               deriving (Show,Eq)

newtype Y (f :: Type -> Type) (g :: Type -> Type) (ls :: Levels Operation Symbol Type) = Y (Multilevel f g ls) 

data Multilevel (f :: Type -> Type) (g :: Type -> Type) (levels :: Levels Operation Symbol Type)  where
    Atom ::    g v                      -> Multilevel f g (Leaf v)
    Record ::  Record  (f :.: Y f g) t  -> Multilevel f g (Node Product t)
    Variant :: Variant (f :.: Y f g) t  -> Multilevel f g (Node Sum t)

type Of o pairs = Node o (FromList pairs)

type (::.) a b = '(a, Leaf b)
infixr 0 ::.
type (::>) a b = '(a, b)
infixr 0 ::>

foo :: Multilevel I I (Node Product (FromList '[ '("foo", Leaf Char),
                                                 '("bar", Node Sum (FromList '[ '("sub1", Leaf Char),
                                                                                '("sub2", Node Sum (FromList '[ '("subsub1", Leaf Int), 
                                                                                                                '("subsub2", Leaf Char) ]))]))]))
foo = Record $ insert @"foo" (Comp (I (Y (Atom (I 'a')))))
             . insert @"bar" (Comp (I (Y (Variant $ inject @"sub1" (Comp (I (Y (Atom (I 'a')))))))))
             $ unit

bar :: Multilevel I I (Product `Of` [
                            "foo" ::. Char,
                            "bar" ::> Sum `Of`
                                [
                                    "sub1" ::. Char,
                                    "sub2" ::> Sum `Of`
                                        [
                                            "subsub1" ::. Int,
                                            "subsub2" ::. Char
                                        ]
                                ]
                      ])
bar = Record $ insert @"foo" (Comp (I (Y (Atom (I 'a')))))
             . insert @"bar" (Comp (I (Y (Variant $ inject @"sub1" (Comp (I (Y (Atom (I 'a')))))))))
             $ unit

foodo :: Char
foodo = case foo of
    Record thefoo -> case (getField @"foo"  thefoo) of
        Comp (I (Y (Atom (I c)))) -> c
