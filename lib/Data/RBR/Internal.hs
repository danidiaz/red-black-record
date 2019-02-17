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

module Data.RBR.Internal where

import           Data.Proxy
import           Data.Kind
import           Data.Monoid (Endo(..))
import           Data.List (intersperse)
import           Data.Foldable (asum)
import           GHC.TypeLits
import           GHC.Generics (D1,C1,S1(..),M1(..),K1(..),Rec0(..))
import qualified GHC.Generics as G

import           Data.SOP (I(..),K(..),unI,unK,NP(..),NS(..),All,SListI,type (-.->)(Fn,apFn),mapKIK)
import           Data.SOP.NP (collapse_NP,liftA_NP,liftA2_NP,cliftA_NP,cliftA2_NP,pure_NP)
import           Data.SOP.NS (collapse_NS,ap_NS,injections,Injection)

-- | The color of a node.
data Color = R
           | B
    deriving Show

-- | The Red-Black tree. It will be used, as a kind, to index the 'Record' and 'Variant' types.
data RBT k v = E 
             | N Color (RBT k v) k v (RBT k v)
    deriving Show

--
--
-- This code has been copied and adapted from the corresponding Data.SOP code (the All constraint).
--

-- Why is this KeysValuesAllF type family needed at all? Why is not KeysValuesAll sufficient by itself?
-- In fact, if I delete KeysValuesAllF and use eclusively KeysValuesAll, functions like demoteKeys seem to still work fine.
--
-- UndecidableSuperClasses and RankNTypes seem to be required by KeysValuesAllF.
type family
  KeysValuesAllF (c :: k -> v -> Constraint) (t :: RBT k v) :: Constraint where
  KeysValuesAllF  _ E                        = ()
  KeysValuesAllF  c (N color left k v right) = (c k v, KeysValuesAll c left, KeysValuesAll c right)

{- | Require a constraint for every key-value pair in a tree. This is a generalization of 'Data.SOP.All' from "Data.SOP".
 
     'cpara_RBT' constructs a 'Record' by means of a constraint for producing
     the nodes of the tree. The constraint is passed as a 'Data.Proxy.Proxy'.
     This function seldom needs to be called directly.
-}
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

{- | Create a 'Record' containing the names of each field. 
    
     The names are represented by a constant functor 'K' carrying an annotation
     of type 'String'. This means that there aren't actually any values of the
     type that corresponds to each field, only the 'String' annotations.
-} 
demoteKeys :: forall t. KeysValuesAll KnownKey t => Record (K String) t
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

-- class KeyValueTop (k :: Symbol) (v :: z)
-- instance KeyValueTop k v

--
--

{- | An extensible product-like type with named fields.
 
     The values in the 'Record' come wrapped in a type constructor @f@, which
     por pure records will be the identity functor 'I'.
-}
data Record (f :: Type -> Type) (t :: RBT Symbol Type)  where
    Empty :: Record f E 
    Node  :: Record f left -> f v -> Record f right -> Record f (N color left k v right)

instance (Productlike '[] t result, Show (NP f result)) => Show (Record f t) where
    show x = "fromNP (" ++ show (toNP x) ++ ")"

{- | Show a 'Record' in a friendlier way than the default 'Show' instance. The
     function argument will usually be 'show', but it can be used to unwrap the
     value of each field before showing it.
-}
prettyShowRecord :: forall t flat f. (KeysValuesAll KnownKey t,Productlike '[] t flat, All Show flat, SListI flat) 
                 => (forall x. Show x => f x -> String) 
                 -> Record f t 
                 -> String
prettyShowRecord showf r = 
    let keysflat = toNP @t (demoteKeys @t)
        valuesflat = toNP @t r
        entries = cliftA2_NP (Proxy @Show) (\(K key) fv -> K (key ++ " = " ++ showf fv))
                                           keysflat 
                                           valuesflat
     in "{" ++ mconcat (intersperse ", " (collapse_NP entries)) ++ "}"


{- | Like 'prettyShowRecord' but specialized to pure records.
-}
prettyShowRecordI :: forall t flat. (KeysValuesAll KnownKey t,Productlike '[] t flat, All Show flat, SListI flat) => Record I t -> String
prettyShowRecordI r = prettyShowRecord (show . unI) r 

{-| A Record without components is a boring, uninformative type whose single value can be conjured out of thin air.
-}
unit :: Record f E
unit = Empty

{- | An extensible sum-like type with named branches.
 
     The values in the 'Variant' come wrapped in a type constructor @f@, which
     por pure variants will be the identity functor 'I'.
-}
data Variant (f :: Type -> Type) (t :: RBT Symbol Type)  where
    Here       :: f v -> Variant f (N color left k v right)
    LookRight  :: Variant f t -> Variant f (N color' left' k' v' t)
    LookLeft   :: Variant f t -> Variant f (N color' t k' v' right')

instance (Sumlike '[] t result, Show (NS f result)) => Show (Variant f t) where
    show x = "fromNS (" ++ show (toNS x) ++ ")"

{-| A Variant without branches doesn't have any values. From an impossible thing, anything can come out. 
-}
impossible :: Variant f E -> b
impossible v = case v of

{- | Show a 'Variant' in a friendlier way than the default 'Show' instance. The
     function argument will usually be 'show', but it can be used to unwrap the
     value of the branch before showing it.
-}
prettyShowVariant :: forall t flat f. (KeysValuesAll KnownKey t,Productlike '[] t flat, Sumlike '[] t flat, All Show flat, SListI flat)
                  => (forall x. Show x => f x -> String) 
                  -> Variant f t 
                  -> String
prettyShowVariant showf v = 
    let keysflat = toNP @t (demoteKeys @t)
        eliminators = cliftA_NP (Proxy @Show) (\(K k) -> Fn (\fv -> (K (k ++ " (" ++ showf fv ++ ")")))) keysflat
        valuesflat = toNS @t v
     in collapse_NS (ap_NS eliminators valuesflat)

{- | Like 'prettyShowVariant' but specialized to pure variants.
-}
prettyShowVariantI :: forall t flat. (KeysValuesAll KnownKey t,Productlike '[] t flat, Sumlike '[] t flat, All Show flat, SListI flat) 
                   => Variant I t -> String
prettyShowVariantI v = prettyShowVariant (show . unI) v 

--
--
-- Insertion

{- | Insert a list of type level key / value pairs into a type-level tree. 
-}
type family InsertAll (es :: [(Symbol,Type)]) (t :: RBT Symbol Type) :: RBT Symbol Type where
    InsertAll '[] t = t
    InsertAll ( '(name,fieldType) ': es ) t = Insert name fieldType (InsertAll es t)

{- | Build a type-level tree out of a list of type level key / value pairs. 
-}
type FromList (es :: [(Symbol,Type)]) = InsertAll es E

{- | Alias for 'insert'. 
-}
addField :: forall k v t f . Insertable k v t => f v -> Record f t -> Record f (Insert k v t)
addField = insert @k @v @t @f

{- | Like 'insert' but specialized to pure 'Record's.
-}
insertI :: forall k v t . Insertable k v t => v -> Record I t -> Record I (Insert k v t)
insertI = insert @k @v @t . I

{- | Like 'addField' but specialized to pure 'Record's.
-}
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

{- | Class that determines if the pair of a 'Symbol' key and a 'Type' can
     be inserted into a type-level tree.
 
     The associated type family 'Insert' produces the resulting tree.

     At the term level, this manifests in 'insert', which adds a new field to a
     record, and in 'widen', which lets you use a 'Variant' in a bigger context
     than the one in which is was defined. 'insert' tends to be more useful in
     practice.

     If the tree already has the key but with a /different/ type, the insertion
     fails to compile.
 -}
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
    balanceR' (Node (Node (Node a fv1 b) fv2 c) fv3 d) = 
               Node (Node a fv1 b) fv2 (Node c fv3 d)
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
    balanceR' (Node (Node a fv1 (Node b fv2 c)) fv3 d) = 
               Node (Node a fv1 b) fv2 (Node c fv3 d)
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
    balanceR' (Node a fv1 (Node (Node b fv2 c) fv3 d)) = 
               Node (Node a fv1 b) fv2 (Node c fv3 d)
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
    balanceR' (Node a fv1 (Node b fv2 (Node c fv3 d))) = 
               Node (Node a fv1 b) fv2 (Node c fv3 d)
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

--
-- These two type families exist to avoid duplicating expensive type-level
-- computations, in particular the Value' computations.
--
-- Record accessors are compiled WAY slower without them!
--
-- TODO: Whould sharing be preserved if I made them type synonyms? Benchmark that.

{- | Auxiliary type family to avoid repetition and help improve compilation times.
 -}
type family Field (f :: Type -> Type) (t :: RBT Symbol Type) (v :: Type) where
    Field f t v = Record f t -> (f v -> Record f t, f v)

{- | Auxiliary type family to avoid repetition and help improve compilation times.
 -}
type family Branch (f :: Type -> Type) (t :: RBT Symbol Type) (v :: Type) where
    Branch f t v = (Variant f t -> Maybe (f v), f v -> Variant f t)

--
{- | 
     Class that determines if a given 'Symbol' key is present in a type-level
     tree.

     The 'Value' type family gives the 'Type' corresponding to the key.

     'field' takes a field name (given through @TypeApplications@) and a
     'Record', and returns a pair of a setter for the field and the original
     value of the field.
     
     'branch' takes a branch name (given through @TypeApplications@) and
     returns a pair of a match function and a constructor.
-} 
class Key (k :: Symbol) (t :: RBT Symbol Type) where
    type Value k t :: Type
    field  :: Field  f t (Value k t)
    branch :: Branch f t (Value k t)

class KeyHelper (ordering :: Ordering) (k :: Symbol) (left :: RBT Symbol Type) (v :: Type) (right :: RBT Symbol Type) where 
    type Value' ordering k left v right :: Type
    field'  :: Field  f (N colorx left kx v right) (Value' ordering k left v right)
    branch' :: Branch f (N colorx left kx v right) (Value' ordering k left v right)

instance (CmpSymbol k' k ~ ordering, KeyHelper ordering k left v' right) => Key k (N color left k' v' right) where
    type Value k (N color left k' v' right) = Value' (CmpSymbol k' k) k left v' right
    field = field' @ordering @k @left @v' @right
    branch = branch' @ordering @k @left @v' @right

instance (CmpSymbol k2 k ~ ordering, KeyHelper ordering k left2 v2 right2) 
      => KeyHelper LT k left v (N color2 left2 k2 v2 right2) where
    type Value'    LT k left v (N color2 left2 k2 v2 right2) = Value' (CmpSymbol k2 k) k left2 v2 right2
    field' (Node left fv right) = 
        let (setter,x) = field' @ordering @k @left2 @v2 @right2 right
         in (\z -> Node left fv (setter z),x)
    branch' = 
        let (match,inj) = branch' @ordering @k @left2 @v2 @right2 
         in (\case LookRight x -> match x
                   _ -> Nothing,
             \fv -> LookRight (inj fv))

instance (CmpSymbol k2 k ~ ordering, KeyHelper ordering k left2 v2 right2) 
      => KeyHelper GT k (N color2 left2 k2 v2 right2) v' right where
    type    Value' GT k (N color2 left2 k2 v2 right2) v' right = Value' (CmpSymbol k2 k) k left2 v2 right2
    field' (Node left fv right) = 
        let (setter,x) = field' @ordering @k @left2 @v2 @right2 left
         in (\z -> Node (setter z) fv right,x)
    branch' =
        let (match,inj) = branch' @ordering @k @left2 @v2 @right2 
         in (\case LookLeft x -> match x
                   _ -> Nothing,
             \fv -> LookLeft (inj fv))

instance KeyHelper EQ k left v right where
    type Value' EQ k left v right = v
    field' (Node left fv right) = (\x -> Node left x right, fv)
    branch' = (\case Here x -> Just x
                     _ -> Nothing,
               Here)

{- | Get the value of a field for a 'Record'. 
-}
project :: forall k t f . Key k t => Record f t -> f (Value k t)
project = snd . field @k @t

{- | Alias for 'project'.
-}
getField :: forall k t f . Key k t => Record f t -> f (Value k t)
getField = project @k @t @f

{- | Set the value of a field for a 'Record'. 
-}
setField :: forall k t f . Key k t => f (Value k t) -> Record f t -> Record f t
setField fv r = fst (field @k @t @f r) fv

{- | Modify the value of a field for a 'Record'. 
-}
modifyField :: forall k t f . Key k t => (f (Value k t) -> f (Value k t)) -> Record f t -> Record f t
modifyField f r = uncurry ($) (fmap f (field @k @t @f r))

{- | Put a value into the branch of a 'Variant'.
-}
inject :: forall k t f. Key k t => f (Value k t) -> Variant f t
inject = snd (branch @k @t)

{- | Check if a 'Variant' value is the given branch.
-}
match :: forall k t f. Key k t => Variant f t -> Maybe (f (Value k t))
match = fst (branch @k @t)

{- | Like 'project' but specialized to pure 'Record's.
-}
projectI :: forall k t . Key k t => Record I t -> Value k t
projectI = unI . snd . field @k @t

{- | Like 'getField' but specialized to pure 'Record's.
-}
getFieldI :: forall k t . Key k t => Record I t -> Value k t
getFieldI = projectI @k @t

{- | Like 'setField' but specialized to pure 'Record's.
-}
setFieldI :: forall k t . Key k t => Value k t -> Record I t -> Record I t
setFieldI v r = fst (field @k @t r) (I v)

{- | Like 'modifyField' but specialized to pure 'Record's.
-}
modifyFieldI :: forall k t . Key k t => (Value k t -> Value k t) -> Record I t -> Record I t
modifyFieldI f = modifyField @k @t (I . f . unI)

{- | Like 'inject' but specialized to pure 'Variant's.
-}
injectI :: forall k t. Key k t => Value k t -> Variant I t
injectI = snd (branch @k @t) . I

{- | Like 'match' but specialized to pure 'Variants's.
-}
matchI :: forall k t . Key k t => Variant I t ->  Maybe (Value k t)
matchI v = unI <$> fst (branch @k @t) v

{- | Process a 'Variant' using a eliminator 'Record' that carries
     handlers for each possible branch of the 'Variant'.
-}
eliminate :: (Productlike '[] t result, Sumlike '[] t result, SListI result) => Record (Case f r) t -> Variant f t -> r
eliminate cases variant = 
    let adapt (Case e) = Fn (\fv -> K (e fv))
     in collapse_NS (ap_NS (liftA_NP adapt (toNP cases)) (toNS variant)) 

{- | Represents a handler for a branch of a 'Variant'.  
-}
newtype Case f a b = Case (f b -> a)

{- | A form of 'addField' for creating eliminators for 'Variant's.
-}
addCase :: forall k v t f a. Insertable k v t => (f v -> a) -> Record (Case f a) t -> Record (Case f a) (Insert k v t)
addCase f = addField @k @v @t (Case f)

{- | A pure version of 'addCase'.
-}
addCaseI :: forall k v t a. Insertable k v t => (v -> a) -> Record (Case I a) t -> Record (Case I a) (Insert k v t)
addCaseI f = addField @k @v @t (Case (f . unI))

--
--
-- Subsetting

newtype SetField f a b = SetField { getSetField :: f b -> a -> a }
 
-- this odd trick again...
class (Key k t, Value k t ~ v) => PresentIn (t :: RBT Symbol Type) (k :: Symbol) (v :: Type) 
instance (Key k t, Value k t ~ v) => PresentIn (t :: RBT Symbol Type) (k :: Symbol) (v :: Type)

{- | Constraint for trees that represent subsets of fields of 'Record'-like types.
-}
type ProductlikeSubset (subset :: RBT Symbol Type) (whole :: RBT Symbol Type) (flat :: [Type]) = 
                       (KeysValuesAll (PresentIn whole) subset,
                        Productlike '[] subset flat,
                        SListI flat)

{- | Like 'field', but targets multiple fields at the same time 
-}
fieldSubset :: forall subset whole flat f. (ProductlikeSubset subset whole flat) 
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

{- | Like 'project', but extracts multiple fields at the same time.
 
     Can also be used to convert between structurally dissimilar trees that
     nevertheless have the same entries. 
-}
projectSubset :: forall subset whole flat f. (ProductlikeSubset subset whole flat) 
              => Record f whole 
              -> Record f subset
projectSubset =  snd . fieldSubset

{- | Alias for 'projectSubset'.
-}
getFieldSubset :: forall subset whole flat f. (ProductlikeSubset subset whole flat)  
               => Record f whole 
               -> Record f subset
getFieldSubset = projectSubset

{- | Like 'setField', but sets multiple fields at the same time.
 
-}
setFieldSubset :: forall subset whole flat f.  (ProductlikeSubset subset whole flat) 
               => Record f subset
               -> Record f whole 
               -> Record f whole
setFieldSubset subset whole = fst (fieldSubset whole) subset 

{- | Like 'modifyField', but modifies multiple fields at the same time.
 
-}
modifyFieldSubset :: forall subset whole flat f.  (ProductlikeSubset subset whole flat) 
                  => (Record f subset -> Record f subset)
                  -> Record f whole 
                  -> Record f whole
modifyFieldSubset f r = uncurry ($) (fmap f (fieldSubset @subset @whole r))


{- | Constraint for trees that represent subsets of branches of 'Variant'-like types.
-}
type SumlikeSubset (subset :: RBT Symbol Type) (whole :: RBT Symbol Type) (subflat :: [Type]) (wholeflat :: [Type]) = 
                   (KeysValuesAll (PresentIn whole) subset,
                    Productlike '[] whole  wholeflat,
                    Sumlike '[] whole  wholeflat,
                    SListI wholeflat,
                    Productlike '[] subset subflat,
                    Sumlike '[] subset subflat,
                    SListI subflat)

{- | Like 'branch', but targets multiple branches at the same time.
-}
branchSubset :: forall subset whole subflat wholeflat f. (SumlikeSubset subset whole subflat wholeflat)
             => (Variant f whole -> Maybe (Variant f subset), Variant f subset -> Variant f whole)
branchSubset = 
    let inj2case :: forall t flat f v. Sumlike '[] t flat => (_ -> _) -> Injection _ flat v -> Case _ _ v
        inj2case = \adapt -> \fn -> Case (\fv -> adapt (fromNS @t (unK (apFn fn fv))))
        -- The intuition is that getting the setter and the getter together might be faster at compile-time.
        -- The intuition might be wrong.
        subs :: forall f. Record f whole -> (Record f subset -> Record f whole, Record f subset)
        subs = fieldSubset @subset @whole
     in
     (,)
     (let injs :: Record (Case f (Maybe (Variant f subset))) subset 
          injs = fromNP @subset (liftA_NP (inj2case Just) (injections @subflat))
          wholeinjs :: Record (Case f (Maybe (Variant f subset))) whole 
          wholeinjs = fromNP @whole (pure_NP (Case (\_ -> Nothing)))
          mixedinjs = fst (subs wholeinjs) injs
       in eliminate mixedinjs)
     (let wholeinjs :: Record (Case f (Variant f whole)) whole
          wholeinjs = fromNP @whole (liftA_NP (inj2case id) (injections @wholeflat))
          injs = snd (subs wholeinjs)
       in eliminate injs)

{- | Like 'inject', but injects one of several possible branches.
-}
injectSubset :: forall subset whole subflat wholeflat f. (SumlikeSubset subset whole subflat wholeflat)
             => Variant f subset -> Variant f whole
injectSubset = snd (branchSubset @subset @whole @subflat @wholeflat)

{- | Like 'match', but matches more than one branch.
-}
matchSubset :: forall subset whole subflat wholeflat f. (SumlikeSubset subset whole subflat wholeflat)
            => Variant f whole -> Maybe (Variant f subset)
matchSubset = fst (branchSubset @subset @whole @subflat @wholeflat)

{- | 
     Like 'eliminate', but allows the eliminator 'Record' to have more fields
     than there are branches in the 'Variant'.
-}
eliminateSubset :: forall subset whole subflat wholeflat f r. (SumlikeSubset subset whole subflat wholeflat)
                => Record (Case f r) whole -> Variant f subset -> r
eliminateSubset cases = 
    let reducedCases = getFieldSubset @subset @whole cases
     in eliminate reducedCases 

--
--
-- Interaction with Data.SOP

{- | Class from converting 'Record's to and from the n-ary product type 'NP' from "Data.SOP".
    
     'prefixNP' flattens a 'Record' and adds it to the initial part of the product.

     'breakNP' reconstructs a 'Record' from the initial part of the product and returns the unconsumed part.

     The functions 'toNP' and 'fromNP' are usually easier to use. 
-}
class Productlike (start :: [Type])
                  (t :: RBT Symbol Type) 
                  (result :: [Type]) | start t -> result, result t -> start where
    prefixNP:: Record f t -> NP f start -> NP f result
    breakNP :: NP f result -> (Record f t, NP f start)

instance Productlike start E start where
    prefixNP _ start = start  
    breakNP start = (Empty, start) 

instance (Productlike start right middle, 
          Productlike (v ': middle) left result)
          => Productlike start (N color left k v right) result where
    prefixNP (Node left fv right) start = 
        prefixNP @_ @left @result left (fv :* prefixNP @start @right @middle right start)
    breakNP result =
        let (left, fv :* middle) = breakNP @_ @left @result result
            (right, start) = breakNP @start @right middle
         in (Node left fv right, start)

{- | Convert a 'Record' into a n-ary product. 
-}
toNP :: forall t result f. Productlike '[] t result => Record f t -> NP f result
toNP r = prefixNP r Nil

{- | Convert a n-ary product into a compatible 'Record'. 
-}
fromNP :: forall t result f. Productlike '[] t result => NP f result -> Record f t
fromNP np = let (r,Nil) = breakNP np in r

{- | Class from converting 'Variant's to and from the n-ary sum type 'NS' from "Data.SOP".
    
     'prefixNS' flattens a 'Variant' and adds it to the initial part of the sum.

     'breakNS' reconstructs a 'Variant' from the initial part of the sum and returns the unconsumed part.

     The functions 'toNS' and 'fromNS' are usually easier to use. 
-}
class Sumlike (start :: [Type]) 
              (t :: RBT Symbol Type) 
              (result :: [Type]) | start t -> result, result t -> start where
    prefixNS :: Either (NS f start) (Variant f t) -> NS f result
    breakNS :: NS f result -> Either (NS f start) (Variant f t)

instance Sumlike start 
                  (N color E k v E)
                  (v ': start) where
    prefixNS = \case
        Left  l -> S l
        Right x -> case x of Here fv -> Z @_ @v @start fv
    breakNS = \case 
        Z x -> Right (Here x)
        S x -> Left x

instance (Sumlike start (N colorR leftR kR vR rightR) middle,
          Sumlike (v ': middle) (N colorL leftL kL vL rightL) result)
         => Sumlike start 
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

instance Sumlike (v ': start) (N colorL leftL kL vL rightL) result
         => Sumlike start (N color (N colorL leftL kL vL rightL) k v E) result where
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

instance Sumlike start (N colorR leftR kR vR rightR) middle
         => Sumlike start (N color E k v (N colorR leftR kR vR rightR)) (v ': middle) where
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

{- | Convert a 'Variant' into a n-ary sum. 
-}
toNS :: forall t result f. Sumlike '[] t result => Variant f t -> NS f result
toNS = prefixNS . Right

{- | Convert a n-ary sum into a compatible 'Variant'. 
-}
fromNS :: forall t result f. Sumlike '[] t result => NS f result -> Variant f t
fromNS ns = case breakNS ns of 
    Left _ -> error "this never happens"
    Right x -> x

--
--
-- Interfacing with normal records

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

instance ToRecordHelper E fields => ToRecordHelper E (D1 meta (C1 metacons fields)) where
    type RecordCode' E (D1 meta (C1 metacons fields)) = RecordCode' E fields
    toRecord' r (M1 (M1 g)) = toRecord' @E @fields r g

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

--
--
class ToRecord r => FromRecord (r :: Type) where
    fromRecord :: Record I (RecordCode r) -> r
    default fromRecord :: (G.Generic r, FromRecordHelper (RecordCode r) (G.Rep r)) => Record I (RecordCode r) -> r
    fromRecord r = G.to (fromRecord' @(RecordCode r) @(G.Rep r) r)

class FromRecordHelper (t :: RBT Symbol Type) (g :: Type -> Type) where
    fromRecord' :: Record I t -> g x

instance FromRecordHelper t fields => FromRecordHelper t (D1 meta (C1 metacons fields)) where
    fromRecord' r = M1 (M1 (fromRecord' @t @fields r))

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

--
--
--
type family VariantCode (s :: Type) :: RBT Symbol Type where
    VariantCode s = VariantCode' E (G.Rep s)

type family VariantCode' (acc :: RBT Symbol Type) (g :: Type -> Type) :: RBT Symbol Type where
    VariantCode' acc (D1 meta fields) = VariantCode' acc fields
    VariantCode' acc (t1 G.:+: t2) = VariantCode' (VariantCode' acc t2) t1
    VariantCode' acc (C1 (G.MetaCons k _ _) (S1 ('G.MetaSel Nothing unpackedness strictness laziness) (Rec0 v))) = Insert k v acc
     
class FromVariant (s :: Type) where
    fromVariant :: Variant I (VariantCode s) -> s
    default fromVariant :: (G.Generic s, FromVariantHelper (VariantCode s) (G.Rep s)) => Variant I (VariantCode s) -> s
    fromVariant v = case fromVariant' @(VariantCode s) v of
        Just x -> G.to x
        Nothing -> error "fromVariant match fail. Should not happen."

class FromVariantHelper (t :: RBT Symbol Type) (g :: Type -> Type) where
    fromVariant' :: Variant I t -> Maybe (g x)

instance FromVariantHelper t fields => FromVariantHelper t (D1 meta fields) where
    fromVariant' v = M1 <$> fromVariant' @t v

instance (Key k t, Value k t ~ v) 
         => FromVariantHelper t (C1 (G.MetaCons k x y) (S1 ('G.MetaSel Nothing unpackedness strictness laziness) (Rec0 v)))
  where
    fromVariant' v = case matchI @k @t v of
        Just x -> Just (M1 (M1 (K1 x)) )
        Nothing -> Nothing

instance ( FromVariantHelper t t1,
           FromVariantHelper t t2 
         ) =>
         FromVariantHelper t (t1 G.:+: t2)
  where
    fromVariant' v = case fromVariant' @t @t1 v of
        Just x1 -> Just (G.L1 x1)
        Nothing -> case fromVariant' @t @t2 v of
            Just x2 -> Just (G.R1 x2)
            Nothing -> Nothing

--
--
class ToVariant (s :: Type) where
    toVariant :: s -> Variant I (VariantCode s)
    default toVariant :: (G.Generic s, ToVariantHelper (VariantCode s) (G.Rep s)) => s -> Variant I (VariantCode s)
    toVariant s = toVariant' @(VariantCode s) @(G.Rep s) (G.from s)

class ToVariantHelper (t :: RBT Symbol Type) (g :: Type -> Type) where
    toVariant' :: g x -> Variant I t 

instance ToVariantHelper t fields => ToVariantHelper t (D1 meta fields) where
    toVariant' (M1 fields) = toVariant' @t fields

instance (Key k t, Value k t ~ v) =>
    ToVariantHelper t (C1 (G.MetaCons k x y) (S1 ('G.MetaSel Nothing unpackedness strictness laziness) (Rec0 v))) 
  where
    toVariant' (M1 (M1 (K1 v))) = injectI @k v

instance ( ToVariantHelper t t1,
           ToVariantHelper t t2 
         ) =>
         ToVariantHelper t (t1 G.:+: t2)
  where
    toVariant' = \case
        G.L1 l -> toVariant' @t l
        G.R1 r -> toVariant' @t r

--
--
-- deletion
--
--
--
-- delete :: (Ord a) => a -> Tree a -> Tree a
-- delete x t = makeBlack $ del x t
--   where makeBlack (T _ a y b) = T B a y b
--         makeBlack E           = E
-- 
-- del :: (Ord a) => a -> Tree a -> Tree a
-- del x t@(T _ l y r)
--   | x < y = delL x t
--   | x > y = delR x t
--   | otherwise = fuse l r
-- 
-- delL :: (Ord a) => a -> Tree a -> Tree a
-- delL x t@(T B t1 y t2) = balL $ T B (del x t1) y t2
-- delL x t@(T R t1 y t2) = T R (del x t1) y t2
-- 
-- balL :: Tree a -> Tree a
-- balL (T B (T R t1 x t2) y t3) = T R (T B t1 x t2) y t3
-- balL (T B t1 y (T B t2 z t3)) = balance' (T B t1 y (T R t2 z t3))
-- balL (T B t1 y (T R (T B t2 u t3) z t4@(T B l value r))) =
--   T R (T B t1 y t2) u (balance' (T B t3 z (T R l value r)))
-- 
-- delR :: (Ord a) => a -> Tree a -> Tree a
-- delR x t@(T B t1 y t2) = balR $ T B t1 y (del x t2)
-- delR x t@(T R t1 y t2) = T R t1 y (del x t2)
-- 
-- balR :: Tree a -> Tree a
-- balR (T B t1 y (T R t2 x t3)) = T R t1 y (T B t2 x t3)
-- balR (T B (T B t1 z t2) y t3) = balance' (T B (T R t1 z t2) y t3)
-- balR (T B (T R t1@(T B l value r) z (T B t2 u t3)) y t4) =
--   T R (balance' (T B (T R l value r) z t2)) u (T B t3 y t4)
-- 
-- fuse :: Tree a -> Tree a -> Tree a
-- fuse E t = t
-- fuse t E = t
-- fuse t1@(T B _ _ _) (T R t3 y t4) = T R (fuse t1 t3) y t4
-- fuse (T R t1 x t2) t3@(T B _ _ _) = T R t1 x (fuse t2 t3)
-- fuse (T R t1 x t2) (T R t3 y t4)  =
--   let s = fuse t2 t3
--   in case s of
--        (T R s1 z s2) -> (T R (T R t1 x s1) z (T R s2 y t4))
--        (T B _ _ _)   -> (T R t1 x (T R s y t4))
-- fuse (T B t1 x t2) (T B t3 y t4)  =
--   let s = fuse t2 t3
--   in case s of
--        (T R s1 z s2) -> (T R (T B t1 x s1) z (T B s2 y t4))
--        (T B s1 z s2) -> balL (T B t1 x (T B s y t4))


class BalanceableTree (t :: RBT Symbol Type) where
    type BalanceTree t :: RBT Symbol Type
    balanceTreeR :: Record f t -> Record f (BalanceTree t)
    balanceTreeV :: Variant f t -> Variant f (BalanceTree t)

instance Balanceable color left k v right => BalanceableTree (N color left k v right) where
    type BalanceTree (N color left k v right) = Balance color left k v right
    balanceTreeR = balanceR @color @left @k @v @right
    balanceTreeV = balanceV @color @left @k @v @right

type family DiscriminateBalL (t :: RBT k v) :: Bool where
    DiscriminateBalL (N B (N R _ _ _ _) _ _ _) = False
    DiscriminateBalL _ = True

class BalanceableL (t :: RBT Symbol Type) where
    type BalL t :: RBT Symbol Type
    balLR :: Record f t -> Record f (BalL t)
    balLV :: Variant f t -> Variant f (BalL t)

class BalanceableHelperL (b :: Bool) (t :: RBT Symbol Type) where
    type BalL' b t :: RBT Symbol Type
    balLR' :: Record f t -> Record f (BalL' b t)
    balLV' :: Variant f t -> Variant f (BalL' b t)

instance (DiscriminateBalL t ~ b, BalanceableHelperL b t) => BalanceableL t where
    type BalL t = BalL' (DiscriminateBalL t) t
    balLR = balLR' @b @t
    balLV = balLV' @b @t

-- balL (T B (T R t1 x t2) y t3) = T R (T B t1 x t2) y t3
instance BalanceableHelperL False (N B (N R left1 k1 v1 right1) k2 v2 right2) where
    type BalL'              False (N B (N R left1 k1 v1 right1) k2 v2 right2) =
                                  (N R (N B left1 k1 v1 right1) k2 v2 right2)
    balLR' (Node (Node left' v' right') v right) = Node (Node left' v' right') v right
    balLV' v = case v of LookLeft x  -> LookLeft (case x of LookLeft y  -> LookLeft y
                                                            Here y      -> Here y
                                                            LookRight y -> LookRight y)
                         Here x      -> Here x
                         LookRight x -> LookRight x

-- missing: two more cases for BalL'

-- balL (T B t1 y (T B t2 z t3)) = balance' (T B t1 y (T R t2 z t3))

instance (BalanceableHelper    (ShouldBalance 
                               B t1 (N B t2 z zv t3)) 
                               B t1 y yv (N B t2 z zv t3)) => 
    BalanceableHelperL True (N B t1 y yv (N B t2 z zv t3)) where
    type BalL'         True (N B t1 y yv (N B t2 z zv t3))     
             =  BalanceTree (N B t1 y yv (N B t2 z zv t3))
    balLR' = balanceTreeR  @(N B t1 y yv (N B t2 z zv t3))
    balLV' = balanceTreeV  @(N B t1 y yv (N B t2 z zv t3))


-- balL (T B t1 y (T R (T B t2 u t3) z (T B l value r))) =
--   T R (T B t1 y t2) u (balance' (T B t3 z (T R l value r)))

instance (BalanceableHelper    (ShouldBalance 
                               B t3 (N R l k kv r)) 
                               B t3 z zv  (N R l k kv r)) => 
    BalanceableHelperL True (N B t1 y yv (N R (N B t2 u uv t3) z zv (N B l k kv r))) where
    type BalL'         True (N B t1 y yv (N R (N B t2 u uv t3) z zv (N B l k kv r))) =
                             N R (N B t1 y yv t2) u uv (BalanceTree (N B t3 z zv (N R l k kv r)))          
    balLR' (Node left1 v1 (Node (Node left2 v2 right2) vx (Node left3 v3 right3))) = 
            Node (Node left1 v1 left2) v2 (balanceTreeR @(N B t3 z zv (N R l k kv r)) (Node right2 vx (Node left3 v3 right3)))
    balLV' v = case v of LookLeft left1                          -> LookLeft (LookLeft left1)
                         Here v1                                 -> LookLeft (Here v1)
                         LookRight (LookLeft (LookLeft left2))   -> LookLeft (LookRight left2)
                         LookRight (LookLeft (Here v2))          -> Here v2
                         LookRight (LookLeft (LookRight right2)) -> LookRight (balanceTreeV @(N B t3 z zv (N R l k kv r)) (LookLeft right2))
                         LookRight (Here vx)                     -> LookRight (balanceTreeV @(N B t3 z zv (N R l k kv r)) (Here vx))
                         LookRight (LookRight rr)                -> LookRight (balanceTreeV @(N B t3 z zv (N R l k kv r)) (LookRight (case rr of
                                                                        LookLeft left3 -> LookLeft left3
                                                                        Here v3 -> Here v3
                                                                        LookRight right3 -> LookRight right3)))

-- balR :: Tree a -> Tree a
-- balR (T B t1 y (T R t2 x t3)) = T R t1 y (T B t2 x t3)
-- balR (T B (T B t1 z t2) y t3) = balance' (T B (T R t1 z t2) y t3)
-- balR (T B (T R t1@(T B l value r) z (T B t2 u t3)) y t4) =
--   T R (balance' (T B (T R l value r) z t2)) u (T B t3 y t4)

type family DiscriminateBalR (t :: RBT k v) :: Bool where
    DiscriminateBalR (N B _ _ _ (N R _ _ _ _)) = False
    DiscriminateBalR _ = True

class BalanceableR (t :: RBT Symbol Type) where
    type BalR t :: RBT Symbol Type
    balRR :: Record f t -> Record f (BalR t)
    balRV :: Variant f t -> Variant f (BalR t)

class BalanceableHelperR (b :: Bool) (t :: RBT Symbol Type) where
    type BalR' b t :: RBT Symbol Type
    balRR' :: Record f t -> Record f (BalR' b t)
    balRV' :: Variant f t -> Variant f (BalR' b t)

instance (DiscriminateBalR t ~ b, BalanceableHelperR b t) => BalanceableR t where
    type BalR t = BalR' (DiscriminateBalR t) t
    balRR = balRR' @b @t
    balRV = balRV' @b @t

-- balR (T B t1 y (T R t2 x t3)) = T R t1 y (T B t2 x t3)
instance BalanceableHelperR False (N B right2 k2 v2 (N R left1 k1 v1 right1)) where
    type BalR'              False (N B right2 k2 v2 (N R left1 k1 v1 right1)) =
                                  (N R right2 k2 v2 (N B left1 k1 v1 right1))
    balRR' (Node right v (Node left' v' right')) = Node  right v (Node left' v' right')
    balRV' v = case v of LookLeft x   -> LookLeft x
                         Here x       -> Here x
                         LookRight x  -> LookRight (case x of LookLeft y  -> LookLeft y
                                                              Here y      -> Here y
                                                              LookRight y -> LookRight y)

-- balR (T B (T B t1 z t2) y t3) = balance' (T B (T R t1 z t2) y t3)
instance (BalanceableHelper    (ShouldBalance 
                               B (N B t2 z zv t3) t1) 
                               B (N B t2 z zv t3) y yv t1) => 
    BalanceableHelperR True (N B (N B t2 z zv t3) y yv t1) where
    type BalR'         True (N B (N B t2 z zv t3) y yv t1)     
             =  BalanceTree (N B (N B t2 z zv t3) y yv t1)
    balRR' = balanceTreeR  @(N B (N B t2 z zv t3) y yv t1)
    balRV' = balanceTreeV  @(N B (N B t2 z zv t3) y yv t1)

-- balR (T B (T R t1@(T B l value r) z (T B t2 u t3)) y t4) =
--   T R (balance' (T B (T R l value r) z t2)) u (T B t3 y t4)
instance (BalanceableHelper    (ShouldBalance 
                               B (N R t2 u uv t3) l) 
                               B (N R t2 u uv t3) z zv l) => 
    BalanceableHelperR True (N B (N R (N B t2 u uv t3) z zv (N B l k kv r)) y yv t1) where
    type BalR'         True (N B (N R (N B t2 u uv t3) z zv (N B l k kv r)) y yv t1) =
                             N R (BalanceTree (N B (N R t2 u uv t3) z zv l)) k kv (N B r y yv t1) 
    balRR' (Node (Node (Node left2 v2 right2) vx (Node left3 v3 right3)) v1 left1) = 
            Node (balanceTreeR @(N B (N R t2 u uv t3) z zv l) (Node (Node left2 v2 right2) vx left3)) v3 (Node right3 v1 left1)
    balRV' v = case v of
        LookLeft  (LookLeft rr)                 -> LookLeft (balanceTreeV @(N B (N R t2 u uv t3) z zv l) (LookLeft (case rr of
                                                        LookLeft t2 -> LookLeft t2
                                                        Here uv -> Here uv
                                                        LookRight t3 -> LookRight t3)))
        LookLeft  (Here zv)                     -> LookLeft (balanceTreeV @(N B (N R t2 u uv t3) z zv l) (Here zv))
        LookLeft  (LookRight (LookLeft l))      -> LookLeft (balanceTreeV @(N B (N R t2 u uv t3) z zv l) (LookRight l))
        LookLeft  (LookRight (Here kv))         -> Here kv
        LookLeft  (LookRight (LookRight r))     -> LookRight (LookLeft r)
        Here      yv                            -> LookRight (Here yv) 
        LookRight t1                            -> LookRight (LookRight t1)

-- fuse :: Tree a -> Tree a -> Tree a
-- fuse E t = t
-- fuse t E = t
-- fuse t1@(T B _ _ _) (T R t3 y t4) = T R (fuse t1 t3) y t4
-- fuse (T R t1 x t2) t3@(T B _ _ _) = T R t1 x (fuse t2 t3)
-- fuse (T R t1 x t2) (T R t3 y t4)  =
--   let s = fuse t2 t3
--   in case s of
--        (T R s1 z s2) -> (T R (T R t1 x s1) z (T R s2 y t4))
--        (T B _ _ _)   -> (T R t1 x (T R s y t4))
-- fuse (T B t1 x t2) (T B t3 y t4)  =
--   let s = fuse t2 t3
--   in case s of
--        (T R s1 z s2) -> (T R (T B t1 x s1) z (T B s2 y t4))
--        (T B s1 z s2) -> balL (T B t1 x (T B s y t4))


class Fuseable (l :: RBT Symbol Type) (r :: RBT Symbol Type) where
    type Fuse l r :: RBT Symbol Type
    fuseRecord :: Record f l -> Record f r -> Record f (Fuse l r)
    fuseVariant :: Either (Variant f l) (Variant f r) -> Variant f (Fuse l r)

instance Fuseable E E where
    type Fuse E E = E
    fuseRecord _ _ = unit
    fuseVariant v = case v of

instance Fuseable E (N color left k v right) where
    type Fuse E (N color left k v right) = N color left k v right
    fuseRecord _ r = r
    fuseVariant e = case e of
        Right v -> v

instance Fuseable (N color left k v right) E where
    type Fuse (N color left k v right) E = N color left k v right
    fuseRecord r _ = r
    fuseVariant e = case e of
        Left v -> v

-- fuse t1@(T B _ _ _) (T R t3 y t4) = T R (fuse t1 t3) y t4

instance Fuseable (N B left1 k1 v1 right1) left2 => Fuseable (N B left1 k1 v1 right1) (N R left2 k2 v2 right2) where
    type Fuse (N B left1 k1 v1 right1) (N R left2 k2 v2 right2) = N R (Fuse (N B left1 k1 v1 right1) left2) k2 v2 right2
    fuseRecord (Node left1 v1 right1) (Node left2 v2 right2) = Node (fuseRecord @(N B left1 k1 v1 right1) (Node left1 v1 right1) left2) v2 right2 
    fuseVariant e = case e of 
        Left l  -> case l of
            LookLeft left1   -> LookLeft  (fuseVariant @(N B left1 k1 v1 right1) @left2 (Left (LookLeft left1)))
            Here v1          -> LookLeft  (fuseVariant @(N B left1 k1 v1 right1) @left2 (Left (Here v1)))
            LookRight right1 -> LookLeft  (fuseVariant @(N B left1 k1 v1 right1) @left2 (Left (LookRight right1)))
        Right r -> case r of
            LookLeft left2   -> LookLeft  (fuseVariant @(N B left1 k1 v1 right1) @left2 (Right left2))
            Here v2          -> Here      v2
            LookRight right2 -> LookRight right2

-- fuse (T R t1 x t2) t3@(T B _ _ _) = T R t1 x (fuse t2 t3)
instance Fuseable right1 (N B left2 k2 v2 right2) => Fuseable (N R left1 k1 v1 right1) (N B left2 k2 v2 right2) where
    type Fuse (N R left1 k1 v1 right1) (N B left2 k2 v2 right2) = N R left1 k1 v1 (Fuse right1 (N B left2 k2 v2 right2))
    fuseRecord (Node left1 v1 right1) (Node left2 v2 right2) = Node left1 v1 (fuseRecord @_ @(N B left2 k2 v2 right2) right1 (Node left2 v2 right2))
    fuseVariant e = case e of
        Left l  -> case l of
            LookLeft left1   -> LookLeft left1
            Here v1          -> Here v1
            LookRight right1 -> LookRight (fuseVariant @right1 @(N B left2 k2 v2 right2) (Left right1))
        Right r -> case r of
            LookLeft left2   -> LookRight (fuseVariant @right1 @(N B left2 k2 v2 right2) (Right (LookLeft left2)))
            Here v2          -> LookRight (fuseVariant @right1 @(N B left2 k2 v2 right2) (Right (Here v2)))
            LookRight right2 -> LookRight (fuseVariant @right1 @(N B left2 k2 v2 right2) (Right (LookRight right2)))

-- fuse (T R t1 x t2) (T R t3 y t4)  =
--   let s = fuse t2 t3
--   in case s of
--        (T R s1 z s2) -> (T R (T R t1 x s1) z (T R s2 y t4))
--        (T B _ _ _)   -> (T R t1 x (T R s y t4))

instance (Fuseable right1 left2, Fuse right1 left2 ~ fused, FuseableHelper1 fused (N R left1 k1 v1 right1) (N R left2 k2 v2 right2)) => Fuseable (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) where
    type Fuse (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) = Fuse1 (Fuse right1 left2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) 
    fuseRecord = fuseRecord1 @(Fuse right1 left2) 
    fuseVariant = fuseVariant1 @(Fuse right1 left2)

class FuseableHelper1 (fused :: RBT Symbol Type) (l :: RBT Symbol Type) (r :: RBT Symbol Type) where
    type Fuse1 fused l r :: RBT Symbol Type
    fuseRecord1 :: Record f l -> Record f r -> Record f (Fuse l r)
    fuseVariant1 :: Either (Variant f l) (Variant f r) -> Variant f (Fuse l r)

-- FIXME: The Fuseable constraint is repeated from avobe :(
instance Fuseable right1 left2 => FuseableHelper1 (N R s1 z zv s2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) where
    type Fuse1 (N R s1 z zv s2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) = N R (N R left1 k1 v1 s1) z zv (N R s2 k2 v2 right2)
    fuseRecord1 (Node left1 v1 right1) (Node left2 v2 right2) = 
        case fuseRecord right1 left2 of
            Node s1 zv s2 -> _ -- Node (Node left1 v1 s1) zv (Node s2 v2 right2)
    fuseVariant1 = undefined

instance Fuseable right1 left2 => FuseableHelper1 (N B s1 z zv s2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) where
    type Fuse1 (N B s1 z zv s2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) = N R left1 k1 v1 (N R (N B s1 z zv s2) k2 v2 right2)
    fuseRecord1  = undefined
    fuseVariant1 = undefined

