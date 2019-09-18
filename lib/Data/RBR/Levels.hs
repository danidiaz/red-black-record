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
{-#  OPTIONS_GHC -fwarn-incomplete-patterns  #-}
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
-- https://stackoverflow.com/questions/56821863/writing-a-complete-pragma-for-a-polymorphic-pattern-synonym
pattern PureAtom :: x -> (I :.: Y I I) (Leaf x)
pattern PureAtom v = Comp (I (Y (Atom (I v))))
{-# COMPLETE PureAtom #-}

pattern PureRecord :: Record (I :.: Y I g) t -> (I :.: Y I g) (Node Product t)
pattern PureRecord r = Comp (I (Y (Record r)))
{-# COMPLETE PureRecord #-}

pattern PureVariant :: Variant (I :.: Y I g) t -> (I :.: Y I g) (Node Sum t)
pattern PureVariant r = Comp (I (Y (Variant r)))
{-# COMPLETE PureVariant #-}

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
bar = Record $ insert @"foo" (PureAtom 'a')
             . insert @"bar" (PureVariant $ inject @"sub1" (PureAtom 'a'))
             $ unit

-- These didn't work so well
-- insertIc :: forall k t' t g. Insertable k t' t => Multilevel I g t' -> Record (I :.: Y I g) t -> Record (I :.: Y I g) (Insert k t' t)
-- insertIc v = insert @k @t' @t (Comp (I (Y v)))
-- 
-- projectIc :: forall k t g. Key k t => Record (I :.: Y I g) t -> Multilevel I g (Value k t)
-- projectIc = unY . unI . unComp . project @k
-- 
-- injectIc :: forall k t g. Key k t => Multilevel I g (Value k t) -> Variant (I :.: Y I g) t
-- injectIc = inject @k @t . Comp . I . Y

barz :: Char
barz = case bar of
    Record thebar -> case (project @"foo" thebar) of
        PureAtom c -> c

