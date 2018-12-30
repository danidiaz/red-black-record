{-# LANGUAGE DataKinds,
             ConstraintKinds,
             TypeFamilies,
             GADTs,
             MultiParamTypeClasses,
             FunctionalDependencies,
             FlexibleInstances,
             FlexibleContexts,
             UndecidableInstances,
             TypeApplications,
             ScopedTypeVariables,
             AllowAmbiguousTypes #-}
module RBR where

import Data.Kind
import GHC.TypeLits

data Color = R
           | B
    deriving (Eq,Ord,Show)

data RBT k v = E 
             | N Color (RBT k v) k v (RBT k v)
    deriving Show

data Record (f :: Type -> Type) (kv :: RBT Symbol Type)  where
    Empty :: Record f E 
    Node  :: Record f left -> f v -> Record f right -> Record f (N color left k v right)

class HasField (kv :: RBT Symbol Type) (k :: Symbol) (v :: Type) | kv k -> v where 
    getField :: Record f kv -> f v 

instance ((CmpSymbol k' k) ~ flag, HasFieldHelper flag (N color left k' v' right) k v) => HasField (N color left k' v' right) k v where
    getField = getField' @flag @_ @k @v 

class HasFieldHelper (flag :: Ordering) (kv :: RBT Symbol Type) (k :: Symbol) (v :: Type) | kv k -> v where 
    getField' :: Record f kv -> f v 

instance HasFieldHelper EQ (N color left k v right) k v where
    getField' (Node _ fv _) = fv
 
instance HasField right k v => HasFieldHelper LT (N color left k' v' right) k v where
    getField' (Node _ _ right) = getField @right @k @v right

instance HasField left k v => HasFieldHelper GT (N color left k' v' right) k v where
    getField' (Node left _ _) = getField @left @k @v left

