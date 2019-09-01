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

import Data.RBR.Internal

data Levels k v = Product (Map k (Levels k v))
                | Sum (Map k (Levels k v))
                | Leaf v
                deriving (Show,Eq)

-- data Multilevel (levels : Levels Symbol Type)  where
--     Record I (Map k (Multilevel levelsbelow)) -> Multilevel (Product   
