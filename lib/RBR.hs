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

class HasField (k :: Symbol) (kv :: RBT Symbol Type) (v :: Type) | kv k -> v where 
    getField :: Record f kv -> f v 

instance ((CmpSymbol k' k) ~ flag, HasFieldHelper flag k (N color left k' v' right) v) => HasField k (N color left k' v' right) v where
    getField = getField' @flag @k @_ @v 

class HasFieldHelper (flag :: Ordering) (k :: Symbol) (kv :: RBT Symbol Type) (v :: Type) | kv k -> v where 
    getField' :: Record f kv -> f v 

instance HasFieldHelper EQ k (N color left k v right) v where
    getField' (Node _ fv _) = fv
 
instance HasField k right v => HasFieldHelper LT k (N color left k' v' right) v where
    getField' (Node _ _ right) = getField @k @right @v right

instance HasField k left v => HasFieldHelper GT k (N color left k' v' right) v where
    getField' (Node left _ _) = getField @k @left @v left

