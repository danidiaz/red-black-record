{-# LANGUAGE DataKinds,
             ConstraintKinds,
             PolyKinds,
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
module Data.RBR.Internal where

import Data.Kind
import GHC.TypeLits

data Color = R
           | B
    deriving Show

data RBT k v = E 
             | N Color (RBT k v) k v (RBT k v)
    deriving Show

data Record (f :: Type -> Type) (kv :: RBT Symbol Type)  where
    Empty :: Record f E 
    Node  :: Record f left -> f v -> Record f right -> Record f (N color left k v right)

unit :: Record f E
unit = Empty

--
--
-- Insertion
class Insertable (k :: Symbol) (v :: Type) (t :: RBT Symbol Type) where
    type Insert k v t :: RBT Symbol Type
    insert :: f v -> Record f t -> Record f (Insert k v t)

instance (InsertableHelper1 k v t, CanMakeBlack (Insert1 k v t)) => Insertable k v t where
    type Insert k v t = MakeBlack (Insert1 k v t)
    insert fv r = makeBlackR (insert1 @k @v fv r) 

class CanMakeBlack (t :: RBT Symbol Type) where
    type MakeBlack t :: RBT Symbol Type
    makeBlackR :: Record f t -> Record f (MakeBlack t)

instance CanMakeBlack (N color left k v right) where
    type MakeBlack (N color left k v right) = N B left k v right
    makeBlackR (Node left fv right) = Node left fv right

class InsertableHelper1 (k :: Symbol) 
                        (v :: Type) 
                        (t :: RBT Symbol Type) where
    type Insert1 k v t :: RBT Symbol Type 
    insert1 :: f v -> Record f t -> Record f (Insert1 k v t)

instance InsertableHelper1 k v E where
    type Insert1 k v E = N R E k v E
    insert1 fv Empty = Node Empty fv Empty 

instance (CmpSymbol k k' ~ ordering, 
          InsertableHelper2 ordering k v color left k' v' right
         )
         => InsertableHelper1 k v (N color left k' v' right) where
    -- FIXME duplicate work with CmpSymbol: both in constraint and in associated type family. 
    -- How to avoid it?
    type Insert1 k v (N color left k' v' right) = Insert2 (CmpSymbol k k') k v color left k' v' right  
    insert1 = insert2 @ordering @k @v @color @left @k' @v' @right

class InsertableHelper2 (ordering :: Ordering) 
                        (k :: Symbol) 
                        (v :: Type) 
                        (color :: Color) 
                        (left :: RBT Symbol Type) 
                        (k' :: Symbol) 
                        (v' :: Type) 
                        (right :: RBT Symbol Type) where
    type Insert2 ordering k v color left k' v' right :: RBT Symbol Type 
    insert2 :: f v -> Record f (N color left k' v' right) -> Record f (Insert2 ordering k v color left k' v' right)

instance (InsertableHelper1 k v left,
          Balanceable color (Insert1 k v left) k' v' right
         )
         => InsertableHelper2 LT k v color left k' v' right where
    type Insert2 LT k v color left k' v' right = Balance color (Insert1 k v left) k' v' right
    insert2 fv (Node left fv' right) = balance @color @_ @k' @v' @right (Node (insert1 @k @v fv left) fv' right) 

instance InsertableHelper2 EQ k v color left k' v' right where
    type Insert2 EQ k v color left k' v' right = N color left k v right
    insert2 fv (Node left _ right) = Node left fv right

instance (InsertableHelper1 k v right,
          Balanceable color left  k' v' (Insert1 k v right)
         )
         => InsertableHelper2 GT k v color left k' v' right where
    type Insert2 GT k v color left k' v' right = Balance color left  k' v' (Insert1 k v right)
    insert2 fv (Node left fv' right) = balance @color @left @k' @v' @_ (Node left  fv' (insert1 @k @v fv right)) 

data BalanceAction = BalanceLL
                   | BalanceLR
                   | BalanceRL
                   | BalanceRR
                   | DoNotBalance
                   deriving Show

type family ShouldBalance (color :: Color) 
                          (left :: RBT k' v') 
                          (right :: RBT k' v') :: BalanceAction where
    ShouldBalance B (N R (N R a k1 v1 b) k2 v2 c) d = BalanceLL
    ShouldBalance B (N R a k1 v1 (N R b k2 v2 c)) d = BalanceLR
    ShouldBalance B a (N R (N R b k2 v2 c) k3 v3 d) = BalanceRL
    ShouldBalance B a (N R b k2 v2 (N R c k3 v3 d)) = BalanceRR
    ShouldBalance color a  b                        = DoNotBalance

class Balanceable (color :: Color) 
                  (left :: RBT Symbol Type) 
                  (k :: Symbol) 
                  (v :: Type) 
                  (right :: RBT Symbol Type) where
    type Balance color left k v right :: RBT Symbol Type
    balance :: Record f (N color left k v right) -> Record f (Balance color left k v right)

instance (ShouldBalance color left right ~ action, 
          BalanceableHelper action color left k v right
         ) 
         => Balanceable color left k v right where
    -- FIXME duplicate work with ShouldBalance: both in constraint and in associated type family. 
    -- How to avoid it?
    type Balance color left k v right = Balance' (ShouldBalance color left right) color left k v right
    balance = balance' @action @color @left @k @v @right
    
class BalanceableHelper (action :: BalanceAction) 
                        (color :: Color) 
                        (left :: RBT Symbol Type) 
                        (k :: Symbol) 
                        (v :: Type) 
                        (right :: RBT Symbol Type) where
    type Balance' action color left k v right :: RBT Symbol Type
    balance' :: Record f (N color left k v right) -> Record f (Balance' action color left k v right)

instance BalanceableHelper BalanceLL B (N R (N R a k1 v1 b) k2 v2 c) k3 v3 d where
    type Balance' BalanceLL B (N R (N R a k1 v1 b) k2 v2 c) k3 v3 d = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d)
    balance' (Node (Node (Node a fv1 b) fv2 c) fv3 d) = Node (Node a fv1 b) fv2 (Node c fv3 d)

instance BalanceableHelper BalanceLR B (N R a k1 v1 (N R b k2 v2 c)) k3 v3 d where
    type Balance' BalanceLR B (N R a k1 v1 (N R b k2 v2 c)) k3 v3 d = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    balance' (Node (Node a fv1 (Node b fv2 c)) fv3 d) = Node (Node a fv1 b) fv2 (Node c fv3 d)

instance BalanceableHelper BalanceRL B a k1 v1 (N R (N R b k2 v2 c) k3 v3 d) where
    type Balance' BalanceRL B a k1 v1 (N R (N R b k2 v2 c) k3 v3 d) = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    balance' (Node a fv1 (Node (Node b fv2 c) fv3 d)) = Node (Node a fv1 b) fv2 (Node c fv3 d)

instance BalanceableHelper BalanceRR B a k1 v1 (N R b k2 v2 (N R c k3 v3 d)) where
    type Balance' BalanceRR B a k1 v1 (N R b k2 v2 (N R c k3 v3 d)) = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    balance' (Node a fv1 (Node b fv2 (Node c fv3 d))) = Node (Node a fv1 b) fv2 (Node c fv3 d)

instance BalanceableHelper DoNotBalance color a k v b where
    type Balance' DoNotBalance color a k v b = N color a k v b 
    balance' = id

--
--
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

