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

class Peel (start :: Map Symbol Type)
           (result :: Map Symbol (Levels Symbol Type)) | start -> result, result -> start where

instance Peel E E

instance (Peel left' left, Peel right' right) =>
         Peel (N color left' k (Multilevel sublevel) right')
              (N color left  k sublevel              right )

data Multilevel (levels :: Levels Symbol Type)  where
    Atom :: v -> Multilevel (Leaf v)
    Record :: Peel t' t => Record I t' -> Multilevel (Product t)
    Variant :: Peel t' t => Variant I t' -> Multilevel (Sum t)


foo :: Multilevel (Product (FromList '[ '("foo", Leaf Char) ]))
foo = Record $ insertI @"foo" (Atom 'a') 
             $ unit

-- This doesn't work. 
-- foodo :: Char
-- foodo = case foo of
--     Record thefoo -> case getFieldI @"foo" thefoo of
--         Atom c -> c
