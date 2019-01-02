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
             ExplicitForAll,
             EmptyCase #-}
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

{-| A Record without components is a boring, uninformative type whose single value can be conjured out of thin air.
-}
unit :: Record f E
unit = Empty

data Variant (f :: Type -> Type) (kv :: RBT Symbol Type)  where
    Here       :: f v -> Variant f (N color left k v right)
    LookRight  :: Variant f t -> Variant f (N color' left' k' v' t)
    LookLeft   :: Variant f t -> Variant f (N color' t k' v' right')

{-| A Variant without branches doesn't have any values. From an impossible thing, anything can come out. 
-}
ludicrous :: Variant f E -> b
ludicrous v = case v of

--
--
-- Insertion
class Insertable (k :: Symbol) (v :: Type) (t :: RBT Symbol Type) where
    type Insert k v t :: RBT Symbol Type
    insert :: f v -> Record f t -> Record f (Insert k v t)
    widen :: Variant f t -> Variant f (Insert k v t)

instance (InsertableHelper1 k v t, CanMakeBlack (Insert1 k v t)) => Insertable k v t where
    type Insert k v t = MakeBlack (Insert1 k v t)
    insert fv r = makeBlackR (insert1 @k @v fv r) 
    widen v = makeBlackV (widen1 @k @v v)

class CanMakeBlack (t :: RBT Symbol Type) where
    type MakeBlack t :: RBT Symbol Type
    makeBlackR :: Record f t -> Record f (MakeBlack t)
    makeBlackV :: Variant f t -> Variant f (MakeBlack t)

instance CanMakeBlack (N color left k v right) where
    type MakeBlack (N color left k v right) = N B left k v right
    makeBlackR (Node left fv right) = Node left fv right
    makeBlackV (Here fv) = Here fv

class InsertableHelper1 (k :: Symbol) 
                        (v :: Type) 
                        (t :: RBT Symbol Type) where
    type Insert1 k v t :: RBT Symbol Type 
    insert1 :: f v -> Record f t -> Record f (Insert1 k v t)
    widen1 :: Variant f t -> Variant f (Insert1 k v t)

instance InsertableHelper1 k v E where
    type Insert1 k v E = N R E k v E
    insert1 fv Empty = Node Empty fv Empty 
    widen1 v = undefined

instance (CmpSymbol k k' ~ ordering, 
          InsertableHelper2 ordering k v color left k' v' right
         )
         => InsertableHelper1 k v (N color left k' v' right) where
    -- FIXME possible duplicate work with CmpSymbol: both in constraint and in associated type family. 
    -- Is that bad? How to avoid it?
    type Insert1 k v (N color left k' v' right) = Insert2 (CmpSymbol k k') k v color left k' v' right  
    insert1 = insert2 @ordering @k @v @color @left @k' @v' @right
    widen1 v = undefined

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
    widen2 :: Variant f (N color left k' v' right) -> Variant f (Insert2 ordering k v color left k' v' right)

instance (InsertableHelper1 k v left,
          Balanceable color (Insert1 k v left) k' v' right
         )
         => InsertableHelper2 LT k v color left k' v' right where
    type Insert2 LT k v color left k' v' right = Balance color (Insert1 k v left) k' v' right
    insert2 fv (Node left fv' right) = balanceR @color @_ @k' @v' @right (Node (insert1 @k @v fv left) fv' right) 
    widen2 v = undefined

instance InsertableHelper2 EQ k v color left k' v' right where
    type Insert2 EQ k v color left k' v' right = N color left k v right
    insert2 fv (Node left _ right) = Node left fv right
    widen2 v = undefined

instance (InsertableHelper1 k v right,
          Balanceable color left  k' v' (Insert1 k v right)
         )
         => InsertableHelper2 GT k v color left k' v' right where
    type Insert2 GT k v color left k' v' right = Balance color left  k' v' (Insert1 k v right)
    insert2 fv (Node left fv' right) = balanceR @color @left @k' @v' @_ (Node left  fv' (insert1 @k @v fv right)) 
    widen2 v = undefined

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
    balanceR :: Record f (N color left k v right) -> Record f (Balance color left k v right)
    balanceV :: Variant f (N color left k v right) -> Variant f (N color left k v right)

instance (ShouldBalance color left right ~ action, 
          BalanceableHelper action color left k v right
         ) 
         => Balanceable color left k v right where
    -- FIXME possible duplicate work with ShouldBalance: both in constraint and in associated type family. 
    -- Is that bad? How to avoid it?
    type Balance color left k v right = Balance' (ShouldBalance color left right) color left k v right
    balanceR = balanceR' @action @color @left @k @v @right
    balanceV = undefined
    
class BalanceableHelper (action :: BalanceAction) 
                        (color :: Color) 
                        (left :: RBT Symbol Type) 
                        (k :: Symbol) 
                        (v :: Type) 
                        (right :: RBT Symbol Type) where
    type Balance' action color left k v right :: RBT Symbol Type
    balanceR' :: Record f (N color left k v right) -> Record f (Balance' action color left k v right)
    balanceV' :: Variant f (N color left k v right) -> Variant f (N color left k v right)

instance BalanceableHelper BalanceLL B (N R (N R a k1 v1 b) k2 v2 c) k3 v3 d where
    type Balance' BalanceLL B (N R (N R a k1 v1 b) k2 v2 c) k3 v3 d = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d)
    balanceR' (Node (Node (Node a fv1 b) fv2 c) fv3 d) = Node (Node a fv1 b) fv2 (Node c fv3 d)
    balanceV' = undefined

instance BalanceableHelper BalanceLR B (N R a k1 v1 (N R b k2 v2 c)) k3 v3 d where
    type Balance' BalanceLR B (N R a k1 v1 (N R b k2 v2 c)) k3 v3 d = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    balanceR' (Node (Node a fv1 (Node b fv2 c)) fv3 d) = Node (Node a fv1 b) fv2 (Node c fv3 d)
    balanceV' = undefined

instance BalanceableHelper BalanceRL B a k1 v1 (N R (N R b k2 v2 c) k3 v3 d) where
    type Balance' BalanceRL B a k1 v1 (N R (N R b k2 v2 c) k3 v3 d) = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    balanceR' (Node a fv1 (Node (Node b fv2 c) fv3 d)) = Node (Node a fv1 b) fv2 (Node c fv3 d)
    balanceV' = undefined

instance BalanceableHelper BalanceRR B a k1 v1 (N R b k2 v2 (N R c k3 v3 d)) where
    type Balance' BalanceRR B a k1 v1 (N R b k2 v2 (N R c k3 v3 d)) = N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    balanceR' (Node a fv1 (Node b fv2 (Node c fv3 d))) = Node (Node a fv1 b) fv2 (Node c fv3 d)
    balanceV' = undefined

instance BalanceableHelper DoNotBalance color a k v b where
    type Balance' DoNotBalance color a k v b = N color a k v b 
    balanceR' = id
    balanceV' = id

--
--
-- Accessing fields

class Member (k :: Symbol) 
             (v :: Type)            
             (kv :: RBT Symbol Type) | kv k -> v where 
    -- should be a lens. "projected?"
    project :: Record f kv -> f v 
    -- should be a prism. "injected?"
    inject  :: f v -> Variant f kv

instance (CmpSymbol k' k ~ ordering, 
          MemberHelper ordering k v (N color left k' v' right)
         ) 
         => Member k v (N color left k' v' right) where
    project = project' @ordering @k @v 
    inject  = inject'  @ordering @k @v 

class MemberHelper (ordering :: Ordering) 
                     (k :: Symbol) 
                     (v :: Type) 
                     (kv :: RBT Symbol Type) | kv k -> v where 
    project' :: Record f kv -> f v 
    inject'  :: f v -> Variant f kv

instance MemberHelper EQ k v (N color left k v right) where
    project' (Node _ fv _) = fv
    inject'  fv = Here fv
 
instance Member k v right => MemberHelper LT k v (N color left k' v' right) where
    project' (Node _ _ right) = project @k @v @right right
    inject' fv = LookRight (inject @k @v @right fv)

instance Member k v left => MemberHelper GT k v (N color left k' v' right) where
    project' (Node left _ _) = project @k @v @left left
    inject' fv = LookLeft (inject @k @v @left fv)

