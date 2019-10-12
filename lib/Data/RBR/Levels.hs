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

import           Data.SOP (I(I),unI,(:.:)(Comp),unComp)
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
newtype Y (f :: Type -> Type) (g :: Type -> Type) (ls :: Levels Operation Symbol Type) = Y { unY :: Multi f g ls }

-- f wraps every named field
-- g wraps every atomic value
data Multi (f :: Type -> Type) (g :: Type -> Type) (levels :: Levels Operation Symbol Type)  where
    Atom ::    g v                      -> Multi f g (Leaf v)
    Record ::  Record  (f :.: Y f g) t  -> Multi f g (Node Product t)
    Variant :: Variant (f :.: Y f g) t  -> Multi f g (Node Sum t)

-- syntactic sugar for the type level
type Of o pairs = Node o (FromList pairs)

type (::.) a b = '(a, Leaf b)
infixr 0 ::.
type (::>) a b = '(a, b)
infixr 0 ::>

-- 
type IY g = I :.: Y I g

-- syntactic sugar for the term level
-- https://stackoverflow.com/questions/56821863/writing-a-complete-pragma-for-a-polymorphic-pattern-synonym
pattern PureAtom :: x -> Multi f I (Leaf x)
pattern PureAtom v = Atom (I v)
{-# COMPLETE PureAtom #-}

-- type IY = I :.: Y I I

-- -- syntactic sugar for the term level
-- -- https://stackoverflow.com/questions/56821863/writing-a-complete-pragma-for-a-polymorphic-pattern-synonym
-- pattern PureAtom :: x -> IY (Leaf x)
-- pattern PureAtom v = Comp (I (Y (Atom (I v))))
-- {-# COMPLETE PureAtom #-}
-- pattern PureRecord :: Record IY t -> IY (Node Product t)
-- pattern PureRecord r = Comp (I (Y (Record r)))
-- {-# COMPLETE PureRecord #-}
-- 
-- pattern PureVariant :: Variant IY t -> IY (Node Sum t)
-- pattern PureVariant r = Comp (I (Y (Variant r)))
-- {-# COMPLETE PureVariant #-}
-- 
-- bar :: Multi I I (Product `Of` [
--                             "foo" ::. Char,
--                             "bar" ::> Sum `Of`
--                                 [
--                                     "sub1" ::. Char,
--                                     "sub2" ::> Sum `Of`
--                                         [
--                                             "subsub1" ::. Int,
--                                             "subsub2" ::. Char
--                                         ]
--                                 ]
--                       ])
-- bar = Record $ insert @"foo" (PureAtom 'a')
--              . insert @"bar" (PureVariant $ inject @"sub1" (PureAtom 'a'))
--              $ unit


baz :: Multi I I (Product `Of` [
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
baz = Record $ insertIY @"foo" (PureAtom 'a')
             . insertIY @"bar" (Variant $ injectIY @"sub1" (PureAtom 'a'))
             $ unit


-- These didn't work so well
insertIY :: forall k t' t g. Insertable k t' t => Multi I g t' -> Record (IY g) t -> Record (IY g) (Insert k t' t)
insertIY v = insert @k @t' @t (Comp (I (Y v)))

projectIY :: forall k t g. Key k t => Record (IY g) t -> Multi I g (Value k t)
projectIY = unY . unI . unComp . project @k

injectIY :: forall k t g. Key k t => Multi I g (Value k t) -> Variant (IY g) t
injectIY = inject @k @t . Comp . I . Y

barz :: Char
barz = case baz of
    Record thebaz -> case (projectIY @"foo" thebaz) of
        PureAtom c -> c

