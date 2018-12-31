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
    deriving Show

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
    InsertHelper2 LT k v color left k' v' right = Balance color (InsertHelper1 k v left) k' v' right
    InsertHelper2 EQ k v color left k' v' right = N color left k v right
    InsertHelper2 GT k v color left k' v' right = Balance color left k' v' (InsertHelper1 k v right)

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

-- experiment
class InsertableHelper1 (k :: Symbol) 
                        (v :: Type) 
                        (t :: RBT Symbol Type) where
    type InsertResult1 k v t :: RBT Symbol Type 
    insertR1 :: f v -> Record f t -> Record f (InsertResult1 k v t)

instance InsertableHelper1 k v E where
    type InsertResult1 k v E = N R E k v E
    insertR1 fv Empty = Node Empty fv Empty 

instance (CmpSymbol k k' ~ ordering, 
          InsertableHelper2 ordering k v color left k' v' right
         )
         => InsertableHelper1 k v (N color left k' v' right) where
    -- FIXME duplicate work with CmpSymbol: both in constraint and in associated type family. 
    -- How to avoid it?
    type InsertResult1 k v (N color left k' v' right) = InsertResult2 (CmpSymbol k k') k v color left k' v' right  
    insertR1 = insertR2 @ordering @k @v @color @left @k' @v' @right

class InsertableHelper2 (ordering :: Ordering) 
                        (k :: Symbol) 
                        (v :: Type) 
                        (color :: Color) 
                        (left :: RBT Symbol Type) 
                        (k' :: Symbol) 
                        (v' :: Type) 
                        (right :: RBT Symbol Type) where
    type InsertResult2 ordering k v color left k' v' right :: RBT Symbol Type 
    insertR2 :: f v -> Record f (N color left k' v' right) -> Record f (InsertResult2 ordering k v color left k' v' right)

instance (InsertableHelper1 k v left,
          Balanceable color (InsertResult1 k v left) k' v' right
         )
         => InsertableHelper2 LT k v color left k' v' right where
    type InsertResult2 LT k v color left k' v' right = BalanceResult color (InsertResult1 k v left) k' v' right
    insertR2 fv (Node left fv' right) = balanceR @color @_ @k' @v' @right (Node (insertR1 @k @v fv left) fv' right) 

instance InsertableHelper2 EQ k v color left k' v' right where
    type InsertResult2 EQ k v color left k' v' right = N color left k v right
    insertR2 fv (Node left _ right) = Node left fv right

instance (InsertableHelper1 k v right,
          Balanceable color left  k' v' (InsertResult1 k v right)
         )
         => InsertableHelper2 GT k v color left k' v' right where
    type InsertResult2 GT k v color left k' v' right = BalanceResult color left  k' v' (InsertResult1 k v right)
    insertR2 fv (Node left fv' right) = balanceR @color @left @k' @v' @_ (Node left  fv' (insertR1 @k @v fv right)) 

data BalanceAction = BalanceLL
                   | BalanceLR
                   | BalanceRL
                   | BalanceRR
                   | DoNotBalance
                   deriving Show

type family ShouldBalance (color :: Color) (left :: RBT k' v') (right :: RBT k' v') :: BalanceAction where
    ShouldBalance B (N R (N R a k1 v1 b) k2 v2 c) d = BalanceLL
    ShouldBalance B (N R a k1 v1 (N R b k2 v2 c)) d = BalanceLR
    ShouldBalance B a (N R (N R b k2 v2 c) k3 v3 d) = BalanceRL
    ShouldBalance B a (N R b k2 v2 (N R c k3 v3 d)) = BalanceRR
    ShouldBalance color a  b                        = DoNotBalance

class Balanceable (color :: Color) (left :: RBT Symbol Type) (k :: Symbol) (v :: Type) (right :: RBT Symbol Type) where
    type BalanceResult color left k v right :: RBT Symbol Type
    balanceR :: Record f (N color left k v right) -> Record f (BalanceResult color left k v right)

instance (ShouldBalance color left right ~ action, 
          BalanceableHelper action color left k v right
         ) 
         => Balanceable color left k v right where
    -- FIXME duplicate work with ShouldBalance: both in constraint and in associated type family. 
    -- How to avoid it?
    type BalanceResult color left k v right = BalanceResult' (ShouldBalance color left right) color left k v right
    balanceR = balanceR' @action @color @left @k @v @right
    
class BalanceableHelper (action :: BalanceAction) 
                        (color :: Color) 
                        (left :: RBT Symbol Type) 
                        (k :: Symbol) 
                        (v :: Type) 
                        (right :: RBT Symbol Type) where
    type BalanceResult' action color left k v right :: RBT Symbol Type
    balanceR' :: Record f (N color left k v right) -> Record f (BalanceResult' action color left k v right)

instance BalanceableHelper BalanceLL B (N R (N R a k1 v1 b) k2 v2 c) k3 v3 d where
    type BalanceResult' BalanceLL B (N R (N R a k1 v1 b) k2 v2 c) k3 v3 d = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d)
    balanceR' (Node (Node (Node a fv1 b) fv2 c) fv3 d) = Node (Node a fv1 b) fv2 (Node c fv3 d)

instance BalanceableHelper BalanceLR B (N R a k1 v1 (N R b k2 v2 c)) k3 v3 d where
    type BalanceResult' BalanceLR B (N R a k1 v1 (N R b k2 v2 c)) k3 v3 d = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    balanceR' (Node (Node a fv1 (Node b fv2 c)) fv3 d) = Node (Node a fv1 b) fv2 (Node c fv3 d)

instance BalanceableHelper BalanceRL B a k1 v1 (N R (N R b k2 v2 c) k3 v3 d) where
    type BalanceResult' BalanceRL B a k1 v1 (N R (N R b k2 v2 c) k3 v3 d) = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    balanceR' (Node a fv1 (Node (Node b fv2 c) fv3 d)) = Node (Node a fv1 b) fv2 (Node c fv3 d)

instance BalanceableHelper BalanceRR B a k1 v1 (N R b k2 v2 (N R c k3 v3 d)) where
    type BalanceResult' BalanceRR B a k1 v1 (N R b k2 v2 (N R c k3 v3 d)) = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    balanceR' (Node a fv1 (Node b fv2 (Node c fv3 d))) = Node (Node a fv1 b) fv2 (Node c fv3 d)

instance BalanceableHelper DoNotBalance color a k v b where
    type BalanceResult' DoNotBalance color a k v b = N color a k v b 
    balanceR' = id
-- end experiment

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

instance (CmpSymbol k' k ~ ordering, 
          HasFieldHelper ordering k (N color left k' v' right) v
         ) 
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

