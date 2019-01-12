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
             LambdaCase,
             EmptyCase #-}
-- UndecidableSuperClasses and RankNTypes seem to be required by KeysAllF.
module Data.RBR.Internal where

import           Data.Proxy
import           Data.Kind
import           Data.Monoid
import           GHC.TypeLits
import           GHC.Generics (D1,C1,S1(..),M1(..),K1(..),Rec0(..))
import qualified GHC.Generics as G

import           Data.SOP (I(..),K(..),unI,NP(..),NS(..),All,SListI)
import           Data.SOP.NP (collapse_NP,liftA2_NP)

data Color = R
           | B
    deriving Show

data RBT k v = E 
             | N Color (RBT k v) k v (RBT k v)
    deriving Show

--
--
-- This code has been copied and adapted from the corresponding Data.SOP code (the All constraint).
--

-- Why is this KeysValuesAllF type family needed at all? Why is not KeysValuesAll sufficient by itself?
-- In fact, if I delete KeysValuesAllF and use eclusively KeysValuesAll, functions like demoteKeys seem to still work fine.
type family
  KeysValuesAllF (c :: k -> v -> Constraint) (t :: RBT k v) :: Constraint where
  KeysValuesAllF  _ E                        = ()
  KeysValuesAllF  c (N color left k v right) = (c k v, KeysValuesAll c left, KeysValuesAll c right)

class KeysValuesAllF c t => KeysValuesAll (c :: k -> v -> Constraint) (t :: RBT k v) where
  cpara_RBT ::
       proxy c
    -> r E
    -> (forall left k v right color . (c k v, KeysValuesAll c left, KeysValuesAll c right) 
                                   => r left -> r right -> r (N color left k v right))
    -> r t

instance KeysValuesAll c E where
  cpara_RBT _p nil _step = nil

instance (c k v, KeysValuesAll c left, KeysValuesAll c right) => KeysValuesAll c (N color left k v right) where
  cpara_RBT p nil cons =
    cons (cpara_RBT p nil cons) (cpara_RBT p nil cons)

demoteKeys :: KeysValuesAll KnownKey t => Record (K String) t
demoteKeys = cpara_RBT (Proxy @KnownKey) unit go
    where
    go :: forall left k v right color. (KnownKey k v, KeysValuesAll KnownKey left, KeysValuesAll KnownKey right) 
       => Record (K String) left 
       -> Record (K String) right 
       -> Record (K String) (N color left k v right)
    go left right = Node left (K (symbolVal (Proxy @k))) right 

-- the "class synonym" trick. https://www.reddit.com/r/haskell/comments/ab8ypl/monthly_hask_anything_january_2019/edk1ot3/
class KnownSymbol k => KnownKey (k :: Symbol) (v :: z)
instance KnownSymbol k => KnownKey k v 

--
--

data Record (f :: Type -> Type) (t :: RBT Symbol Type)  where
    Empty :: Record f E 
    Node  :: Record f left -> f v -> Record f right -> Record f (N color left k v right)

instance (PrefixNP '[] t result, Show (NP f result)) => Show (Record f t) where
    show x = "fromNP (" ++ show (toNP x) ++ ")"

{-| A Record without components is a boring, uninformative type whose single value can be conjured out of thin air.
-}
unit :: Record f E
unit = Empty

data Variant (f :: Type -> Type) (t :: RBT Symbol Type)  where
    Here       :: f v -> Variant f (N color left k v right)
    LookRight  :: Variant f t -> Variant f (N color' left' k' v' t)
    LookLeft   :: Variant f t -> Variant f (N color' t k' v' right')

instance (PrefixNS '[] t result, Show (NS f result)) => Show (Variant f t) where
    show x = "fromNS (" ++ show (toNS x) ++ ")"

{-| A Variant without branches doesn't have any values. From an impossible thing, anything can come out. 
-}
impossible :: Variant f E -> b
impossible v = case v of

--
--
-- Insertion

type family InsertAll (es :: [(Symbol,Type)]) (t :: RBT Symbol Type) :: RBT Symbol Type where
    InsertAll '[] t = t
    InsertAll ( '(name,fieldType) ': es ) t = Insert name fieldType (InsertAll es t)

type FromList (es :: [(Symbol,Type)]) = InsertAll es E

addField :: forall k v t f . Insertable k v t => f v -> Record f t -> Record f (Insert k v t)
addField = insert @k @v @t @f

insertI :: forall k v t . Insertable k v t => v -> Record I t -> Record I (Insert k v t)
insertI = insert @k @v @t . I

addFieldI :: forall k v t . Insertable k v t => v -> Record I t -> Record I (Insert k v t)
addFieldI = insertI @k @v @t

--
--
-- The original term-level code, from the post "Persistent Red Black Trees in Haskell"
-- 
-- https://abhiroop.github.io/Haskell-Red-Black-Tree/
-- 
-- insert :: (Ord a) => a -> Tree a -> Tree a
-- insert x s = makeBlack $ ins s
--   where ins E  = T R E x E
--         ins (T color a y b)
--           | x < y  = balance color (ins a) y b
--           | x == y = T color a y b
--           | x > y  = balance color a y (ins b)
--         makeBlack (T _ a y b) = T B a y b
-- 
-- balance :: Color -> Tree a -> a -> Tree a -> Tree a
-- balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
-- balance B (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
-- balance B a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
-- balance B a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
-- balance color a x b = T color a x b

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
    widen1 = impossible 
 
instance (CmpSymbol k k' ~ ordering, 
          InsertableHelper2 ordering k v color left k' v' right
         )
         => InsertableHelper1 k v (N color left k' v' right) where
    -- FIXME possible duplicate work with CmpSymbol: both in constraint and in associated type family. 
    -- Is that bad? How to avoid it?
    type Insert1 k v (N color left k' v' right) = Insert2 (CmpSymbol k k') k v color left k' v' right  
    insert1 = insert2 @ordering @k @v @color @left @k' @v' @right
    widen1  = widen2 @ordering @k @v @color @left @k' @v' @right

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
    widen2 v = balanceV @color @(Insert1 k v left) @k' @v' @right $ case v of
        Here x -> Here x
        LookLeft x -> LookLeft (widen1 @k @v x)
        LookRight x -> LookRight x


-- This instance implies that we can't change the type associated to an
-- existing key. If we did that, we wouldn't be able to widen Variants that
-- happen to match that key!
instance InsertableHelper2 EQ k v color left k v right where
    type Insert2 EQ k v color left k v right = N color left k v right
    insert2 fv (Node left _ right) = Node left fv right
    widen2 = id

instance (InsertableHelper1 k v right,
          Balanceable color left  k' v' (Insert1 k v right)
         )
         => InsertableHelper2 GT k v color left k' v' right where
    type Insert2 GT k v color left k' v' right = Balance color left  k' v' (Insert1 k v right)
    insert2 fv (Node left fv' right) = balanceR @color @left @k' @v' @_ (Node left  fv' (insert1 @k @v fv right)) 
    widen2 v = balanceV @color @left @k' @v' @(Insert1 k v right) $ case v of
        Here x -> Here x
        LookLeft x -> LookLeft x
        LookRight x -> LookRight (widen1 @k @v x)

data BalanceAction = BalanceLL
                   | BalanceLR
                   | BalanceRL
                   | BalanceRR
                   | DoNotBalance
                   deriving Show

type family ShouldBalance (color :: Color) 
                          (left :: RBT k' v') 
                          (right :: RBT k' v') :: BalanceAction where
    ShouldBalance B (N R (N R _ _ _ _) _ _ _) _ = BalanceLL
    ShouldBalance B (N R _ _ _ (N R _ _ _ _)) _ = BalanceLR
    ShouldBalance B _ (N R (N R _ _ _ _) _ _ _) = BalanceRL
    ShouldBalance B _ (N R _ _ _ (N R _ _ _ _)) = BalanceRR
    ShouldBalance _ _ _                         = DoNotBalance

class Balanceable (color :: Color) 
                  (left :: RBT Symbol Type) 
                  (k :: Symbol) 
                  (v :: Type) 
                  (right :: RBT Symbol Type) where
    type Balance color left k v right :: RBT Symbol Type
    balanceR :: Record f (N color left k v right) -> Record f (Balance color left k v right)
    balanceV :: Variant f (N color left k v right) -> Variant f (Balance color left k v right)

instance (ShouldBalance color left right ~ action, 
          BalanceableHelper action color left k v right
         ) 
         => Balanceable color left k v right where
    -- FIXME possible duplicate work with ShouldBalance: both in constraint and in associated type family. 
    -- Is that bad? How to avoid it?
    type Balance color left k v right = Balance' (ShouldBalance color left right) color left k v right
    balanceR = balanceR' @action @color @left @k @v @right
    balanceV = balanceV' @action @color @left @k @v @right
    
class BalanceableHelper (action :: BalanceAction) 
                        (color :: Color) 
                        (left :: RBT Symbol Type) 
                        (k :: Symbol) 
                        (v :: Type) 
                        (right :: RBT Symbol Type) where
    type Balance' action color left k v right :: RBT Symbol Type
    balanceR' :: Record f (N color left k v right) -> Record f (Balance' action color left k v right)
    balanceV' :: Variant f (N color left k v right) -> Variant f (Balance' action color left k v right)

instance BalanceableHelper BalanceLL B (N R (N R a k1 v1 b) k2 v2 c) k3 v3 d where
    type Balance'          BalanceLL B (N R (N R a k1 v1 b) k2 v2 c) k3 v3 d = 
                                   N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d)
    balanceR' (Node (Node (Node a fv1 b) fv2 c) fv3 d) = Node (Node a fv1 b) fv2 (Node c fv3 d)
    balanceV' v = case v of
        LookLeft (LookLeft x)  -> LookLeft (case x of LookLeft y  -> LookLeft y
                                                      Here y      -> Here y
                                                      LookRight y -> LookRight y)
        LookLeft (Here x)      -> Here x
        LookLeft (LookRight x) -> LookRight (LookLeft x)
        Here x                 -> LookRight (Here x)
        LookRight x            -> LookRight (LookRight x)

instance BalanceableHelper BalanceLR B (N R a k1 v1 (N R b k2 v2 c)) k3 v3 d where
    type Balance'          BalanceLR B (N R a k1 v1 (N R b k2 v2 c)) k3 v3 d = 
                                   N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    balanceR' (Node (Node a fv1 (Node b fv2 c)) fv3 d) = Node (Node a fv1 b) fv2 (Node c fv3 d)
    balanceV' v = case v of
        LookLeft (LookLeft x)   -> LookLeft (LookLeft x)
        LookLeft (Here x)       -> LookLeft (Here x) 
        LookLeft (LookRight x)  -> case x of LookLeft y  -> LookLeft (LookRight y)
                                             Here y      -> Here y
                                             LookRight y -> LookRight (LookLeft y)
        Here x                  -> LookRight (Here x)
        LookRight x             -> LookRight (LookRight x)

instance BalanceableHelper BalanceRL B a k1 v1 (N R (N R b k2 v2 c) k3 v3 d) where
    type Balance'          BalanceRL B a k1 v1 (N R (N R b k2 v2 c) k3 v3 d) = 
                                   N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    balanceR' (Node a fv1 (Node (Node b fv2 c) fv3 d)) = Node (Node a fv1 b) fv2 (Node c fv3 d)
    balanceV' v = case v of
        LookLeft x              -> LookLeft (LookLeft x)
        Here x                  -> LookLeft (Here x)
        LookRight (LookLeft x)  -> case x of LookLeft y  -> LookLeft (LookRight y)
                                             Here y      -> Here y
                                             LookRight y -> LookRight (LookLeft y)
        LookRight (Here x)      -> LookRight (Here x) 
        LookRight (LookRight x) -> LookRight (LookRight x)

instance BalanceableHelper BalanceRR B a k1 v1 (N R b k2 v2 (N R c k3 v3 d)) where
    type Balance'          BalanceRR B a k1 v1 (N R b k2 v2 (N R c k3 v3 d)) = 
                                   N R (N B a k1 v1 b) k2 v2 (N B c k3 v3 d) 
    balanceR' (Node a fv1 (Node b fv2 (Node c fv3 d))) = Node (Node a fv1 b) fv2 (Node c fv3 d)
    balanceV' v = case v of
        LookLeft x              -> LookLeft (LookLeft x)
        Here x                  -> LookLeft (Here x)
        LookRight (LookLeft x)  -> LookLeft (LookRight x)    
        LookRight (Here x)      -> Here x
        LookRight (LookRight x) -> LookRight (case x of LookLeft y  -> LookLeft y
                                                        Here y      -> Here y
                                                        LookRight y -> LookRight y)

instance BalanceableHelper DoNotBalance color a k v b where
    type Balance' DoNotBalance color a k v b = N color a k v b 
    balanceR' = id
    balanceV' = id

--
--
-- Accessing fields

class Key (k :: Symbol) (t :: RBT Symbol Type) where
    type Value k t :: Type
    field :: Record f t -> (f (Value k t) -> Record f t, f (Value k t))
    branch :: (Variant f t -> Maybe (f (Value k t)), f (Value k t) -> Variant f t)

class KeyHelper (ordering :: Ordering) (k :: Symbol) (t :: RBT Symbol Type) where 
    type Value' ordering k t :: Type
    field' :: Record f t -> (f (Value' ordering k t) -> Record f t, f (Value' ordering k t))
    branch' :: (Variant f t -> Maybe (f (Value' ordering k t)), f (Value' ordering k t) -> Variant f t)

instance (CmpSymbol k' k ~ ordering, KeyHelper ordering k (N color left k' v' right)) 
         => Key k (N color left k' v' right) where
    type Value k (N color left k' v' right) = Value' (CmpSymbol k' k) k (N color left k' v' right)
    field = field' @ordering @k
    branch = branch' @ordering @k

instance Key k right => KeyHelper LT k (N color left k' v' right) where
    type Value' LT k (N color left k' v' right) = Value k right
    field' (Node left fv right) = 
        let (setter,x) = field @k right
         in (\z -> Node left fv (setter z),x)
    branch' = 
        let (match,inj) = branch @k @right
         in (\case LookRight x -> match x
                   _ -> Nothing,
             \fv -> LookRight (inj fv))

instance Key k left => KeyHelper GT k (N color left k' v' right) where
    type Value' GT k (N color left k' v' right) = Value k left
    field' (Node left fv right) = 
        let (setter,x) = field @k left
         in (\z -> Node (setter z) fv right,x)
    branch' =
        let (match,inj) = branch @k @left
         in (\case LookLeft x -> match x
                   _ -> Nothing,
             \fv -> LookLeft (inj fv))

instance KeyHelper EQ k (N color left k v right) where
    type Value' EQ k (N color left k v right) = v
    field' (Node left fv right) = (\x -> Node left x right, fv)
    branch' = (\case Here x -> Just x
                     _ -> Nothing,
               Here)

project :: forall k t f . Key k t => Record f t -> f (Value k t)
project = snd . field @k @t

getField :: forall k t f . Key k t => Record f t -> f (Value k t)
getField = project @k @t @f

setField :: forall k t f . Key k t => f (Value k t) -> Record f t -> Record f t
setField fv r = fst (field @k @t @f r) fv

modifyField :: forall k t f . Key k t => (f (Value k t) -> f (Value k t)) -> Record f t -> Record f t
modifyField f r = uncurry ($) (fmap f (field @k @t @f r))

inject :: forall k t f. Key k t => f (Value k t) -> Variant f t
inject = snd (branch @k @t)

match :: forall k t f. Key k t => Variant f t -> Maybe (f (Value k t))
match = fst (branch @k @t)

projectI :: forall k t . Key k t => Record I t -> Value k t
projectI = unI . snd . field @k @t

getFieldI :: forall k t . Key k t => Record I t -> Value k t
getFieldI = projectI @k @t

setFieldI :: forall k t . Key k t => Value k t -> Record I t -> Record I t
setFieldI v r = fst (field @k @t r) (I v)

modifyFieldI :: forall k t . Key k t => (Value k t -> Value k t) -> Record I t -> Record I t
modifyFieldI f = modifyField @k @t (I . f . unI)

injectI :: forall k v t. Key k t => Value k t -> Variant I t
injectI = snd (branch @k @t) . I

matchI :: forall k t . Key k t => Variant I t ->  Maybe (Value k t)
matchI v = unI <$> fst (branch @k @t) v

--
--
-- Subsetting

newtype SetField f a b = SetField { getSetField :: f b -> a -> a }
 
-- this odd trick again...
class (Key k t, Value k t ~ v) => PresentIn (t :: RBT Symbol Type) (k :: Symbol) (v :: Type) 
instance (Key k t, Value k t ~ v) => PresentIn (t :: RBT Symbol Type) (k :: Symbol) (v :: Type)

fieldSubset :: forall subset whole f flat. 
                    (PrefixNP '[] subset flat,
                     SListI flat,
                     KeysValuesAll (PresentIn whole) subset)
                 => Record f whole -> (Record f subset -> Record f whole, Record f subset)
fieldSubset r = 
    (,)
    (let goset :: forall left k v right color. (PresentIn whole k v, KeysValuesAll (PresentIn whole) left, 
                                                                     KeysValuesAll (PresentIn whole) right) 
               => Record (SetField f (Record f whole)) left 
               -> Record (SetField f (Record f whole)) right 
               -> Record (SetField f (Record f whole)) (N color left k v right)
         goset left right = Node left (SetField (\v w -> fst (field @k @whole w) v)) right
         setters = toNP @subset @_ @(SetField f (Record f whole)) (cpara_RBT (Proxy @(PresentIn whole)) unit goset)
         appz (SetField func) fv = K (Endo (func fv))
      in \toset -> appEndo (mconcat (collapse_NP (liftA2_NP appz setters (toNP toset)))) r)
    (let goget :: forall left k v right color. (PresentIn whole k v, KeysValuesAll (PresentIn whole) left, 
                                                                     KeysValuesAll (PresentIn whole) right) 
               => Record f left 
               -> Record f right 
               -> Record f (N color left k v right)
         goget left right = Node left (project @k @whole r) right
      in cpara_RBT (Proxy @(PresentIn whole)) unit goget)

projectSubset :: forall subset whole f flat. 
                 (PrefixNP '[] subset flat,
                  SListI flat,
                  KeysValuesAll (PresentIn whole) subset)
              => Record f whole 
              -> Record f subset
projectSubset =  snd . fieldSubset

getFieldSubset :: forall subset whole f flat. 
                  (PrefixNP '[] subset flat,
                   SListI flat,
                   KeysValuesAll (PresentIn whole) subset)
               => Record f whole 
               -> Record f subset
getFieldSubset = projectSubset

setFieldSubset :: forall subset whole f flat. 
                  (PrefixNP '[] subset flat,
                   SListI flat,
                   KeysValuesAll (PresentIn whole) subset)
               => Record f subset
               -> Record f whole 
               -> Record f whole
setFieldSubset subset whole = fst (fieldSubset whole) subset 

modifyFieldSubset :: forall subset whole f flat. 
                     (PrefixNP '[] subset flat,
                      SListI flat,
                      KeysValuesAll (PresentIn whole) subset)
                  => (Record f subset -> Record f subset)
                  -> Record f whole 
                  -> Record f whole
modifyFieldSubset f r = uncurry ($) (fmap f (fieldSubset @subset @whole @f r))

--
--
-- Interaction with Data.SOP

class PrefixNP (start :: [Type])
                  (t :: RBT Symbol Type) 
                  (result :: [Type]) | start t -> result, result t -> start where
    prefixNP:: Record f t -> NP f start -> NP f result
    breakNP :: NP f result -> (Record f t, NP f start)

instance PrefixNP start E start where
    prefixNP _ start = start  
    breakNP start = (Empty, start) 

instance (PrefixNP start right middle, 
          PrefixNP (v ': middle) left result)
          => PrefixNP start (N color left k v right) result where
    prefixNP (Node left fv right) start = 
        prefixNP @_ @left @result left (fv :* prefixNP @start @right @middle right start)
    breakNP result =
        let (left, fv :* middle) = breakNP @_ @left @result result
            (right, start) = breakNP @start @right middle
         in (Node left fv right, start)

toNP :: forall t result f. PrefixNP '[] t result => Record f t -> NP f result
toNP r = prefixNP r Nil

fromNP :: forall t result f. PrefixNP '[] t result => NP f result -> Record f t
fromNP np = let (r,Nil) = breakNP np in r

class PrefixNS (start :: [Type]) 
              (t :: RBT Symbol Type) 
              (result :: [Type]) | start t -> result, result t -> start where
    prefixNS :: Either (NS f start) (Variant f t) -> NS f result
    breakNS :: NS f result -> Either (NS f start) (Variant f t)

instance PrefixNS start 
                 (N color E k v E)
                 (v ': start) where
    prefixNS = \case
        Left  l -> S l
        Right x -> case x of Here fv -> Z @_ @v @start fv
    breakNS = \case 
        Z x -> Right (Here x)
        S x -> Left x

instance (PrefixNS start (N colorR leftR kR vR rightR) middle,
          PrefixNS (v ': middle) (N colorL leftL kL vL rightL) result)
         => PrefixNS start 
                    (N color (N colorL leftL kL vL rightL) k v (N colorR leftR kR vR rightR)) 
                    result where
    prefixNS = \case
        Left x -> 
            prefixNS @_ @(N colorL leftL kL vL rightL) (Left (S (prefixNS @_ @(N colorR leftR kR vR rightR) (Left x))))
        Right x -> 
            case x of LookLeft x  -> prefixNS @(v ': middle) @(N colorL leftL kL vL rightL) @result (Right x) 
                      Here x      -> prefixNS @_ @(N colorL leftL kL vL rightL) (Left (Z x))
                      LookRight x -> prefixNS @_ @(N colorL leftL kL vL rightL) (Left (S (prefixNS (Right x))))
    breakNS ns = case breakNS @(v ': middle) @(N colorL leftL kL vL rightL) ns of
        Left x -> case x of
            Z x -> Right (Here x)
            S x -> case breakNS @start @(N colorR leftR kR vR rightR) x of
                Left ns  -> Left ns
                Right v  -> Right (LookRight v)
        Right v -> Right (LookLeft v)

instance PrefixNS (v ': start) (N colorL leftL kL vL rightL) result
         => PrefixNS start (N color (N colorL leftL kL vL rightL) k v E) result where
    prefixNS = \case
        Left x  -> 
            prefixNS @_ @(N colorL leftL kL vL rightL) (Left (S x))
        Right x -> 
            case x of LookLeft x  -> prefixNS @(v ': start) @(N colorL leftL kL vL rightL) @result (Right x)
                      Here x      -> prefixNS @_ @(N colorL leftL kL vL rightL) (Left (Z x))
    breakNS ns = case breakNS @(v ': start) @(N colorL leftL kL vL rightL) ns of
        Left x -> case x of
            Z x -> Right (Here x)
            S x -> Left x 
        Right v -> Right (LookLeft v)

instance PrefixNS start (N colorR leftR kR vR rightR) middle
         => PrefixNS start (N color E k v (N colorR leftR kR vR rightR)) (v ': middle) where
    prefixNS = \case
        Left x  -> S (prefixNS @_ @(N colorR leftR kR vR rightR) (Left x))
        Right x -> 
            case x of Here x      -> Z x
                      LookRight x -> S (prefixNS @_ @(N colorR leftR kR vR rightR) (Right x))
    breakNS = \case 
        Z x -> Right (Here x)
        S x -> case breakNS @_ @(N colorR leftR kR vR rightR) x of
            Left  ns     -> Left ns
            Right v      -> Right (LookRight v)

toNS :: forall t result f. PrefixNS '[] t result => Variant f t -> NS f result
toNS = prefixNS . Right

fromNS :: forall t result f. PrefixNS '[] t result => NS f result -> Variant f t
fromNS ns = case breakNS ns of 
    Left _ -> error "this never happens"
    Right x -> x

-- Interfacing with normal records
--

-- Pending: give generic-based default implementations for these typeclasses.

newtype P (p :: (a, Type)) = P (Snd p)

type family Snd (p :: (a, b)) :: b where
    Snd '(a, b) = b


class ToRecord (r :: Type) where
    type RecordCode r :: RBT Symbol Type
    -- https://stackoverflow.com/questions/22087549/defaultsignatures-and-associated-type-families/22088808
    type RecordCode r = RecordCode' E (G.Rep r)
    toRecord :: r -> Record I (RecordCode r)
    default toRecord :: (G.Generic r,ToRecordHelper E (G.Rep r),RecordCode r ~ RecordCode' E (G.Rep r)) => r -> Record I (RecordCode r)
    toRecord r = toRecord' unit (G.from r)

class ToRecordHelper (start :: RBT Symbol Type) (g :: Type -> Type) where
    type RecordCode' start g :: RBT Symbol Type
    toRecord' :: Record I start -> g x -> Record I (RecordCode' start g)
    --breakNamedNP :: NP P result -> (t x, NP P start)
    --
instance ToRecordHelper E fields => ToRecordHelper E (D1 meta (C1 metacons fields)) where
    type RecordCode' E (D1 meta (C1 metacons fields)) = RecordCode' E fields
    toRecord' r (M1 (M1 g)) = toRecord' @E @fields r g

-- instance NamedFieldsProduct start E start where
--     toRecord' _ start = start  
--     breakNamedNP start = (Empty, start) 
-- 
-- instance (NamedFieldsProduct start right middle, 
--           NamedFieldsProduct ('(k,v) ': middle) left result)
--           => NamedFieldsProduct start (N color left k v right) result where
--     toRecord' (Node left (I v) right) start = 
--         toRecord' @_ @left @result left (P v :* toRecord' @start @right @middle right start)
--     breakNamedNP result =
--         let (left, (P v) :* middle) = breakNamedNP @_ @left @result result
--             (right, start) = breakNamedNP @start @right middle
--          in (Node left (I v) right, start)

instance (Insertable k v start) =>
         ToRecordHelper start
                        (S1 ('G.MetaSel ('Just k)
                                        unpackedness
                                        strictness
                                        laziness)
                            (Rec0 v)) 
  where
    type RecordCode'    start
                        (S1 ('G.MetaSel ('Just k)
                                        unpackedness
                                        strictness
                                        laziness)
                            (Rec0 v))                           = Insert k v start
    toRecord' start (M1 (K1 v)) = insertI @k v start

instance ( ToRecordHelper start  t2,
           RecordCode'    start  t2 ~ middle,
           ToRecordHelper middle t1 
         ) =>
         ToRecordHelper start (t1 G.:*: t2)
  where
    type RecordCode'    start (t1 G.:*: t2) = RecordCode' (RecordCode' start t2) t1 
    toRecord'           start (t1 G.:*: t2) = toRecord' @middle (toRecord' @start start t2) t1 
--    breakNamedNP result =
--       let (t1, middle) = breakNamedNP @middle @t1 result
--           (t2, start) = breakNamedNP @start @t2 middle
--        in (t1 G.:*: t2, start) 


--
--
--

class FromRecord (r :: Type) where
    fromRecord :: Record I t -> r

class FromRecordHelper (t :: RBT Symbol Type) (g :: Type -> Type) where
    fromRecord' :: Record I t -> g x

instance (Key k t, Value k t ~ v) =>
         FromRecordHelper t
                          (S1 ('G.MetaSel ('Just k)
                                         unpackedness
                                         strictness
                                         laziness)
                              (Rec0 v)) 
 where
   fromRecord' r = let v = projectI @k r in M1 (K1 v)

instance ( FromRecordHelper t t1,
           FromRecordHelper t t2
         ) => 
         FromRecordHelper t (t1 G.:*: t2) 
  where 
   fromRecord' r = 
        let v1 = fromRecord' @_ @t1 r
            v2 = fromRecord' @_ @t2 r
         in v1 G.:*: v2

class NominalSum (s :: Type) where
    type SumCode s :: RBT Symbol Type
    toVariant :: s -> Variant I (SumCode s)
    fromVariant :: Variant I (SumCode s) -> s

