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
             AllowAmbiguousTypes,
             ExplicitForAll #-}
module RBR where

import Data.Kind
import GHC.TypeLits

--
-- The TYPE level
--

data Color = R
           | B
    deriving (Eq,Ord,Show)

data RBT k v = E 
             | N Color (RBT k v) k v (RBT k v)
    deriving Show

type family Insert (k :: Symbol) (v :: Type) (t :: RBT Symbol Type) :: RBT Symbol Type where
    Insert k v t = MakeBlack (InsertHelper1 k v t)

type family MakeBlack (t :: RBT Symbol Type) where
    MakeBlack (N color left k v right) = N B left k v right

type family InsertHelper1 (k :: Symbol) 
                          (v :: Type) 
                          (t :: RBT Symbol Type) :: RBT Symbol Type where
    InsertHelper1 k v E = N R E k v E
    InsertHelper1 k v (N color left k' v' right) = InsertHelper2  (CmpSymbol k k') k v color left k' v' right  

type family InsertHelper2 (ordering :: Ordering) 
                          (k :: Symbol) 
                          (v :: Type) 
                          (color :: Color) 
                          (left :: RBT Symbol Type) 
                          (k' :: Symbol) 
                          (v' :: Type) 
                          (right :: RBT Symbol Type) :: RBT Symbol Type where
    InsertHelper2 LT k v color left k' v' right = Balance color (Insert k v left) k' v' right
    InsertHelper2 EQ k v color left k' v' right = N color left k v right
    InsertHelper2 GT k v color left k' v' right = Balance color left k' v' (Insert k v right)

-- shamelessly copied from
-- https://abhiroop.github.io/Haskell-Red-Black-Tree/
-- insert :: (Ord a) => a -> Tree a -> Tree a
-- insert x s = makeBlack $ ins s
--   where ins E  = T R E x E
--         ins (T color a y b)
--           | x < y  = balance color (ins a) y b
--           | x == y = T color a y b
--           | x > y  = balance color a y (ins b)
--         makeBlack (T _ a y b) = T B a y b


type family Balance (color :: Color) (left :: RBT k' v') (k :: k') (v :: v') (right :: RBT k' v') :: RBT k' v' where
    Balance B (N R (N R a k1 v1 b) k2 v2 c) k3 v3 d = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    Balance B (N R a k1 v1 (N R b k2 v2 c)) k3 v3 d = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    Balance B a k1 v1 (N R (N R b k2 v2 c) k3 v3 d) = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    Balance B a k1 v1 (N R b k2 v2 (N R c k3 v3 d)) = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    Balance color a k v b = N color a k v b 

-- shamelessly copied from
-- https://abhiroop.github.io/Haskell-Red-Black-Tree/
-- balance :: Color -> Tree a -> a -> Tree a -> Tree a
-- balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
-- balance B (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
-- balance B a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
-- balance B a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
-- balance color a x b = T color a x b

--
-- The TERM level
--
data Record (f :: Type -> Type) (kv :: RBT Symbol Type)  where
    Empty :: Record f E 
    Node  :: Record f left -> f v -> Record f right -> Record f (N color left k v right)

insert :: forall (k :: Symbol) (v :: Type) (f :: Type -> Type) (kv :: RBT Symbol Type) 
        . f v 
       -> Record f kv 
       -> Record f (Insert k v kv)
insert fv =
    let insert' Empty = Node Empty fv Empty 
        insert' (Node left fv' right) = undefined
     in insert'

-- Accessing fields

class HasField (k :: Symbol) 
               (kv :: RBT Symbol Type) 
               (v :: Type)            | kv k -> v where 
    getField :: Record f kv -> f v 

instance ((CmpSymbol k' k) ~ ordering, 
          HasFieldHelper ordering k (N color left k' v' right) v) 
      => HasField k (N color left k' v' right) v where
    getField = getField' @ordering @k @_ @v 

class HasFieldHelper (ordering :: Ordering) 
                     (k :: Symbol) 
                     (kv :: RBT Symbol Type) 
                     (v :: Type)            | kv k -> v where 
    getField' :: Record f kv -> f v 

instance HasFieldHelper EQ k (N color left k v right) v where
    getField' (Node _ fv _) = fv
 
instance HasField k right v => HasFieldHelper LT k (N color left k' v' right) v where
    getField' (Node _ _ right) = getField @k @right @v right

instance HasField k left v => HasFieldHelper GT k (N color left k' v' right) v where
    getField' (Node left _ _) = getField @k @left @v left

