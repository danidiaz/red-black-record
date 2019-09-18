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
             EmptyCase,
             PatternSynonyms 
#-}
{-#  OPTIONS_GHC -Wno-partial-type-signatures  #-}
module Data.RBR.Levels where

import           Data.Proxy
import           Data.Kind
import           GHC.TypeLits

import           Data.SOP (I(I),(:.:)(Comp))
import           Data.RBR.Internal hiding (Node)

-- To be used as a kind
data Levels o s q = Node o (Map s (Levels o s q))
                  | Leaf q
                  deriving (Show,Eq)

-- To be used as a kind
data Operation = Product
               | Sum
               deriving (Show,Eq)

-- Newtype trick
newtype Y (f :: Type -> Type) (g :: Type -> Type) (ls :: Levels Operation Symbol Type) = Y (Multilevel f g ls) 

-- f wraps every named field
-- g wraps every atomic value
data Multilevel (f :: Type -> Type) (g :: Type -> Type) (levels :: Levels Operation Symbol Type)  where
    Atom ::    g v                      -> Multilevel f g (Leaf v)
    Record ::  Record  (f :.: Y f g) t  -> Multilevel f g (Node Product t)
    Variant :: Variant (f :.: Y f g) t  -> Multilevel f g (Node Sum t)

-- syntactic sugar for the type level
type Of o pairs = Node o (FromList pairs)

type (::.) a b = '(a, Leaf b)
infixr 0 ::.
type (::>) a b = '(a, b)
infixr 0 ::>

-- syntactic sugar for the term level
pattern AtomField :: x -> (I :.: Y I I) (Leaf x)
pattern AtomField v = Comp (I (Y (Atom (I v))))

pattern RecordField :: Record (I :.: Y I g) t -> (I :.: Y I g) (Node Product t)
pattern RecordField r = Comp (I (Y (Record r)))

pattern VariantField :: Variant (I :.: Y I g) t -> (I :.: Y I g) (Node Sum t)
pattern VariantField r = Comp (I (Y (Variant r)))

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
bar = Record $ insert @"foo" (AtomField 'a')
             . insert @"bar" (VariantField $ inject @"sub1" (AtomField 'a'))
             $ unit

barz :: Char
barz = case bar of
    Record thebar -> case (getField @"foo" thebar) of
        AtomField c -> c

