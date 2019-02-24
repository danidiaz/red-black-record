-- | See <https://www.cs.kent.ac.uk/people/staff/smk/redblack/rb.html here> for
-- the original term-level code by Stefan Kahrs. It is also copied at the end
-- of this file.  Some parts of the type-level code include the correspondign
-- term-level parts in their comments.
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
import           Data.Typeable
import           Data.Coerce
import           Data.Bifunctor (first)
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
    deriving (Show,Eq)

-- | A Red-Black tree. It will be used as a kind, to index the 'Record' and 'Variant' types.
data Map k v = E 
             | N Color (Map k v) k v (Map k v)
    deriving (Show,Eq)

-- | A map without entries. See also 'unit' and 'impossible'.
type Empty = E

{-# DEPRECATED EmptyMap "Use Empty instead." #-}
type EmptyMap = E

--
--
-- This code has been copied and adapted from the corresponding Data.SOP code (the All constraint).
--

-- Why is this KeysValuesAllF type family needed at all? Why is not KeysValuesAll sufficient by itself?
-- In fact, if I delete KeysValuesAllF and use eclusively KeysValuesAll, functions like demoteKeys seem to still work fine.
--
-- UndecidableSuperClasses and RankNTypes seem to be required by KeysValuesAllF.
type family
  KeysValuesAllF (c :: k -> v -> Constraint) (t :: Map k v) :: Constraint where
  KeysValuesAllF  _ E                        = ()
  KeysValuesAllF  c (N color left k v right) = (c k v, KeysValuesAll c left, KeysValuesAll c right)

{- | Require a constraint for every key-value pair in a tree. This is a generalization of 'Data.SOP.All' from "Data.SOP".
 
     'cpara_Map' constructs a 'Record' by means of a constraint for producing
     the nodes of the tree. The constraint is passed as a 'Data.Proxy.Proxy'.
     
-}
class KeysValuesAllF c t => KeysValuesAll (c :: k -> v -> Constraint) (t :: Map k v) where
  cpara_Map ::
       proxy c
    -> r E
    -> (forall left k v right color . (c k v, KeysValuesAll c left, KeysValuesAll c right) 
                                   => r left -> r right -> r (N color left k v right))
    -> r t

instance KeysValuesAll c E where
  cpara_Map _p nil _step = nil

instance (c k v, KeysValuesAll c left, KeysValuesAll c right) => KeysValuesAll c (N color left k v right) where
  cpara_Map p nil cons =
    cons (cpara_Map p nil cons) (cpara_Map p nil cons)

{- |
    Create a 'Record', knowing that both keys and values satisfy a 2-place constraint. The constraint is passed as a 'Data.Proxy.Proxy'.

    The naming scheme follows that of 'Data.SOP.NP.cpure_NP'.
 -}
cpure_Record :: forall c t f. KeysValuesAll c t => (Proxy c) -> (forall k v. c k v => f v) -> Record f t
cpure_Record _ fpure = cpara_Map (Proxy @c) unit go
    where
    go :: forall left k' v' right color. (c k' v', KeysValuesAll c left, KeysValuesAll c right) 
       => Record f left
       -> Record f right
       -> Record f (N color left k' v' right)
    go left right = Node left (fpure @k' @v') right 

{- | Create a 'Record' containing the names of each field. 
    
     The names are represented by a constant functor 'K' carrying an annotation
     of type 'String'. This means that there aren't actually any values of the
     type that corresponds to each field, only the 'String' annotations.
-} 
demoteKeys :: forall t. KeysValuesAll KnownKey t => Record (K String) t
demoteKeys = cpara_Map (Proxy @KnownKey) unit go
    where
    go :: forall left k v right color. (KnownKey k v, KeysValuesAll KnownKey left, KeysValuesAll KnownKey right) 
       => Record (K String) left 
       -> Record (K String) right 
       -> Record (K String) (N color left k v right)
    go left right = Node left (K (symbolVal (Proxy @k))) right 

{- |
  Two-place constraint saying that a 'Symbol' key can be demoted to 'String'. Nothing is required from the corresponding value.

  Defined using the "class synonym" <https://www.reddit.com/r/haskell/comments/ab8ypl/monthly_hask_anything_january_2019/edk1ot3/ trick>.
-}
class KnownSymbol k => KnownKey (k :: Symbol) (v :: z)
instance KnownSymbol k => KnownKey k v 

{- | 
  Create a record containing the names of each field along with a term-level
  representation of each type.

  See also 'collapse_Record' for getting the entries as a list.
-}
demoteEntries :: forall t. KeysValuesAll KnownKeyTypeableValue t => Record (K (String,TypeRep)) t
demoteEntries = cpara_Map (Proxy @KnownKeyTypeableValue) unit go
    where
    go :: forall left k v right color. (KnownKeyTypeableValue k v, KeysValuesAll KnownKeyTypeableValue left, KeysValuesAll KnownKeyTypeableValue right) 
       => Record (K (String,TypeRep)) left 
       -> Record (K (String,TypeRep)) right 
       -> Record (K (String,TypeRep)) (N color left k v right)
    go left right = Node left (K (symbolVal (Proxy @k),typeRep (Proxy @v))) right 

{- |
  Two-place constraint saying that a 'Symbol' key can be demoted to 'String', and that the corresponding value 'Type' has a term-level representation. 

  Defined using the "class synonym" <https://www.reddit.com/r/haskell/comments/ab8ypl/monthly_hask_anything_january_2019/edk1ot3/ trick>.
-}
class (KnownSymbol k, Typeable v) => KnownKeyTypeableValue (k :: Symbol) (v :: Type)
instance (KnownSymbol k, Typeable v) => KnownKeyTypeableValue k v 

-- class KeyValueTop (k :: Symbol) (v :: z)
-- instance KeyValueTop k v

--
--

{- | An extensible product-like type with named fields.
 
     The values in the 'Record' come wrapped in a type constructor @f@, which
     por pure records will be the identity functor 'I'.

     See also 'insert', 'delete' and 'project'.
-}
data Record (f :: Type -> Type) (t :: Map Symbol Type)  where
    Empty :: Record f E 
    Node  :: Record f left -> f v -> Record f right -> Record f (N color left k v right)

instance (Productlike '[] t result, Show (NP f result)) => Show (Record f t) where
    show x = "fromNP (" ++ show (toNP x) ++ ")"


{- | Collapse a 'Record' composed of 'K' annotations.
    
     The naming scheme follows that of 'Data.SOP.NP.collapse_NP'.

-}
collapse_Record :: forall t result a. (Productlike '[] t result) => Record (K a) t -> [a]
collapse_Record = collapse_NP . toNP

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
unit :: Record f Empty
unit = Empty

{- | An extensible sum-like type with named branches.
 
     The values in the 'Variant' come wrapped in a type constructor @f@, which
     por pure variants will be the identity functor 'I'.

     See also 'widen', 'winnow' and 'inject'.
-}
data Variant (f :: Type -> Type) (t :: Map Symbol Type)  where
    Here       :: f v -> Variant f (N color left k v right)
    LookRight  :: Variant f t -> Variant f (N color' left' k' v' t)
    LookLeft   :: Variant f t -> Variant f (N color' t k' v' right')

instance (Sumlike '[] t result, Show (NS f result)) => Show (Variant f t) where
    show x = "fromNS (" ++ show (toNS x) ++ ")"

{-| A Variant without branches doesn't have any values. From an impossible thing, anything can come out. 
-}
impossible :: Variant f Empty -> b
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

{- | Insert a list of type level key / value pairs into a type-level map. 
-}
type family InsertAll (es :: [(Symbol,Type)]) (t :: Map Symbol Type) :: Map Symbol Type where
    InsertAll '[] t = t
    InsertAll ( '(name,fieldType) ': es ) t = Insert name fieldType (InsertAll es t)

{- | Build a type-level map out of a list of type level key / value pairs. 
-}
type FromList (es :: [(Symbol,Type)]) = InsertAll es Empty

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

{- | Class that determines if the pair of a 'Symbol' key and a 'Type' can
     be inserted into a type-level map.
 
     The associated type family 'Insert' produces the resulting map.

     At the term level, this manifests in 'insert', which adds a new field to a
     record, and in 'widen', which lets you use a 'Variant' in a bigger context
     than the one in which is was defined. 'insert' tends to be more useful in
     practice.

     If the map already has the key but with a /different/ 'Type', the
     insertion fails to compile.
 -}
class Insertable (k :: Symbol) (v :: Type) (t :: Map Symbol Type) where
    type Insert k v t :: Map Symbol Type
    insert :: f v -> Record f t -> Record f (Insert k v t)
    widen :: Variant f t -> Variant f (Insert k v t)

-- insert x s =
--  T B a z b
--  where
--  T _ a z b = ins s
instance (InsertableHelper1 k v t, CanMakeBlack (Insert1 k v t)) => Insertable k v t where
    type Insert k v t = MakeBlack (Insert1 k v t)
    insert fv r = makeBlackR (insert1 @k @v fv r) 
    widen v = makeBlackV (widen1 @k @v v)

class CanMakeBlack (t :: Map Symbol Type) where
    type MakeBlack t :: Map Symbol Type
    makeBlackR :: Record f t -> Record f (MakeBlack t)
    makeBlackV :: Variant f t -> Variant f (MakeBlack t)

instance CanMakeBlack (N color left k v right) where
    type MakeBlack (N color left k v right) = N B left k v right
    makeBlackR (Node left fv right) = Node left fv right
    makeBlackV v = case v of
        LookLeft l -> LookLeft l
        Here v -> Here v
        LookRight r -> LookRight r

instance CanMakeBlack E where
    type MakeBlack E = E
    makeBlackR Empty = Empty
    makeBlackV = impossible

class InsertableHelper1 (k :: Symbol) 
                        (v :: Type) 
                        (t :: Map Symbol Type) where
    type Insert1 k v t :: Map Symbol Type 
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
                        (left :: Map Symbol Type) 
                        (k' :: Symbol) 
                        (v' :: Type) 
                        (right :: Map Symbol Type) where
    type Insert2 ordering k v color left k' v' right :: Map Symbol Type 
    insert2 :: f v -> Record f (N color left k' v' right) -> Record f (Insert2 ordering k v color left k' v' right)
    widen2 :: Variant f (N color left k' v' right) -> Variant f (Insert2 ordering k v color left k' v' right)

--  ins s@(T B a y b)
--      | x<y = balance (ins a) y b
instance (InsertableHelper1 k v left,
          Balanceable (Insert1 k v left) k' v' right -- TODO remove B here
         )
         => InsertableHelper2 LT k v B left k' v' right where
    type Insert2 LT k v B left k' v' right = Balance (Insert1 k v left) k' v' right
    insert2 fv (Node left fv' right) = balanceR @_ @k' @v' @right (Node (insert1 @k @v fv left) fv' right) 
    widen2 v = balanceV @(Insert1 k v left) @k' @v' @right $ case v of
        Here x -> Here x
        LookLeft x -> LookLeft (widen1 @k @v x)
        LookRight x -> LookRight x

--  ins s@(T B a y b)
--      | x<y = balance (ins a) y b
instance (InsertableHelper1 k v left,
          Balanceable (Insert1 k v left) k' v' right-- TODO remove B here
         )
         => InsertableHelper2 LT k v R left k' v' right where
    type Insert2 LT k v R left k' v' right = N R (Insert1 k v left) k' v' right
    insert2 fv (Node left fv' right) = Node (insert1 @k @v fv left) fv' right 
    widen2 v = case v of
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

--  ins s@(T B a y b)
--      | ...
--      | x>y = balance a y (ins b)
instance (InsertableHelper1 k v right,
          Balanceable left  k' v' (Insert1 k v right)
         )
         => InsertableHelper2 GT k v B left k' v' right where
    type Insert2 GT k v B left k' v' right = Balance left  k' v' (Insert1 k v right)
    insert2 fv (Node left fv' right) = balanceR @left @k' @v' @_ (Node left  fv' (insert1 @k @v fv right)) 
    widen2 v = balanceV @left @k' @v' @(Insert1 k v right) $ case v of
        Here x -> Here x
        LookLeft x -> LookLeft x
        LookRight x -> LookRight (widen1 @k @v x)

--  ins s@(T R a y b)
--      | ...
--      | x>y = T R a y (ins b)
instance (InsertableHelper1 k v right,
          Balanceable left  k' v' (Insert1 k v right)
         )
         => InsertableHelper2 GT k v R left k' v' right where
    type Insert2 GT k v R left k' v' right = N R left k' v' (Insert1 k v right)
    insert2 fv (Node left fv' right) = Node left fv' (insert1 @k @v fv right) 
    widen2 v = case v of
        Here x -> Here x
        LookLeft x -> LookLeft x
        LookRight x -> LookRight (widen1 @k @v x)

data BalanceAction = BalanceSpecial
                   | BalanceLL
                   | BalanceLR
                   | BalanceRL
                   | BalanceRR
                   | DoNotBalance
                   deriving Show

type family ShouldBalance (left :: Map k' v') (right :: Map k' v') :: BalanceAction where
    ShouldBalance (N R _ _ _ _) (N R _ _ _ _) = BalanceSpecial
    ShouldBalance (N R (N R _ _ _ _) _ _ _) _ = BalanceLL
    ShouldBalance (N R _ _ _ (N R _ _ _ _)) _ = BalanceLR
    ShouldBalance _ (N R (N R _ _ _ _) _ _ _) = BalanceRL
    ShouldBalance _ (N R _ _ _ (N R _ _ _ _)) = BalanceRR
    ShouldBalance _ _                         = DoNotBalance

class Balanceable (left :: Map Symbol Type) (k :: Symbol) (v :: Type) (right :: Map Symbol Type) where
    type Balance left k v right :: Map Symbol Type
    balanceR :: Record f (N color left k v right) -> Record f (Balance left k v right)
    balanceV :: Variant f (N color left k v right) -> Variant f (Balance left k v right)

instance (ShouldBalance left right ~ action, 
          BalanceableHelper action left k v right
         ) 
         => Balanceable left k v right where
    -- FIXME possible duplicate work with ShouldBalance: both in constraint and in associated type family. 
    -- Is that bad? How to avoid it?
    type Balance left k v right = Balance' (ShouldBalance left right) left k v right
    balanceR = balanceR' @action @left @k @v @right
    balanceV = balanceV' @action @left @k @v @right
    
class BalanceableHelper (action :: BalanceAction) 
                        (left :: Map Symbol Type) 
                        (k :: Symbol) 
                        (v :: Type) 
                        (right :: Map Symbol Type) where
    type Balance' action left k v right :: Map Symbol Type
    balanceR' :: Record f (N color left k v right) -> Record f (Balance' action left k v right)
    balanceV' :: Variant f (N color left k v right) -> Variant f (Balance' action left k v right)

-- balance (T R a x b) y (T R c z d) = T R (T B a x b) y (T B c z d)
instance BalanceableHelper BalanceSpecial (N R left1 k1 v1 right1) kx vx (N R left2 k2 v2 right2) where
    type Balance'          BalanceSpecial (N R left1 k1 v1 right1) kx vx (N R left2 k2 v2 right2) = 
                                        N R (N B left1 k1 v1 right1) kx vx (N B left2 k2 v2 right2)
    balanceR' (Node (Node left1 v1 right1) vx (Node left2 v2 right2)) = 
              (Node (Node left1 v1 right1) vx (Node left2 v2 right2))
    balanceV' v = case v of
        LookLeft (LookLeft x)   -> LookLeft (LookLeft x)
        LookLeft (Here x)       -> LookLeft (Here x)
        LookLeft (LookRight x)  -> LookLeft (LookRight x)
        Here x -> Here x
        LookRight (LookLeft x)  -> LookRight (LookLeft x)
        LookRight (Here x)      -> LookRight (Here x)
        LookRight (LookRight x) -> LookRight (LookRight x)

-- balance (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
instance BalanceableHelper BalanceLL (N R (N R a k1 v1 b) k2 v2 c) k3 v3 d where
    type Balance'          BalanceLL (N R (N R a k1 v1 b) k2 v2 c) k3 v3 d = 
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

-- balance (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
instance BalanceableHelper BalanceLR (N R a k1 v1 (N R b k2 v2 c)) k3 v3 d where
    type Balance'          BalanceLR (N R a k1 v1 (N R b k2 v2 c)) k3 v3 d = 
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

-- balance a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
instance BalanceableHelper BalanceRL a k1 v1 (N R (N R b k2 v2 c) k3 v3 d) where
    type Balance'          BalanceRL a k1 v1 (N R (N R b k2 v2 c) k3 v3 d) = 
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


-- balance a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
instance BalanceableHelper BalanceRR a k1 v1 (N R b k2 v2 (N R c k3 v3 d)) where
    type Balance'          BalanceRR a k1 v1 (N R b k2 v2 (N R c k3 v3 d)) = 
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

-- balance a x b = T B a x b
instance BalanceableHelper DoNotBalance a k v b where
    type Balance' DoNotBalance a k v b = N B a k v b 
    balanceR' (Node left v right) = (Node left v right)
    balanceV' v = case v of
        LookLeft l -> LookLeft l
        Here v -> Here v
        LookRight r -> LookRight r

--
--
-- Accessing fields

--
-- These two type families exist to avoid duplicating expensive type-level
-- computations, in particular the Value' computations.
--
-- Record accessors are compiled WAY slower without them!
--
{- | Auxiliary type family to avoid repetition and help improve compilation times.
 -}
type family Field (f :: Type -> Type) (t :: Map Symbol Type) (v :: Type) where
    Field f t v = Record f t -> (f v -> Record f t, f v)

{- | Auxiliary type family to avoid repetition and help improve compilation times.
 -}
type family Branch (f :: Type -> Type) (t :: Map Symbol Type) (v :: Type) where
    Branch f t v = (Variant f t -> Maybe (f v), f v -> Variant f t)

--
{- | 
     Class that determines if a given 'Symbol' key is present in a type-level
     map.

     The 'Value' type family gives the 'Type' corresponding to the key.

     'field' takes a field name (given through @TypeApplications@) and a
     'Record', and returns a pair of a setter for the field and the original
     value of the field.
     
     'branch' takes a branch name (given through @TypeApplications@) and
     returns a pair of a match function and a constructor.
-} 
class Key (k :: Symbol) (t :: Map Symbol Type) where
    type Value k t :: Type
    field  :: Field  f t (Value k t)
    branch :: Branch f t (Value k t)

-- member :: Ord a => a -> RB a -> Bool
class KeyHelper (ordering :: Ordering) (k :: Symbol) (left :: Map Symbol Type) (v :: Type) (right :: Map Symbol Type) where 
    type Value' ordering k left v right :: Type
    field'  :: Field  f (N colorx left kx v right) (Value' ordering k left v right)
    branch' :: Branch f (N colorx left kx v right) (Value' ordering k left v right)

instance (CmpSymbol k' k ~ ordering, KeyHelper ordering k left v' right) => Key k (N color left k' v' right) where
    type Value k (N color left k' v' right) = Value' (CmpSymbol k' k) k left v' right
    field = field' @ordering @k @left @v' @right
    branch = branch' @ordering @k @left @v' @right

--  | x<y = member x a
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

--  | x>y = member x b
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

--  | otherwise = True
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
class (Key k t, Value k t ~ v) => PresentIn (t :: Map Symbol Type) (k :: Symbol) (v :: Type) 
instance (Key k t, Value k t ~ v) => PresentIn (t :: Map Symbol Type) (k :: Symbol) (v :: Type)

{- | Constraint for maps that represent subsets of fields of 'Record'-like types.
-}
type ProductlikeSubset (subset :: Map Symbol Type) (whole :: Map Symbol Type) (flat :: [Type]) = 
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
         setters = toNP @subset @_ @(SetField f (Record f whole)) (cpara_Map (Proxy @(PresentIn whole)) unit goset)
         appz (SetField func) fv = K (Endo (func fv))
      in \toset -> appEndo (mconcat (collapse_NP (liftA2_NP appz setters (toNP toset)))) r)
    (let goget :: forall left k v right color. (PresentIn whole k v, KeysValuesAll (PresentIn whole) left, 
                                                                     KeysValuesAll (PresentIn whole) right) 
               => Record f left 
               -> Record f right 
               -> Record f (N color left k v right)
         goget left right = Node left (project @k @whole r) right
      in cpara_Map (Proxy @(PresentIn whole)) unit goget)

{- | Like 'project', but extracts multiple fields at the same time.
 
     Can also be used to convert between 'Record's with structurally dissimilar
     type-level maps that nevertheless hold the same entries. 
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


{- | Constraint for maps that represent subsets of branches of 'Variant'-like types.
-}
type SumlikeSubset (subset :: Map Symbol Type) (whole :: Map Symbol Type) (subflat :: [Type]) (wholeflat :: [Type]) = 
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
 
     Can also be used to convert between 'Variant's with structurally
     dissimilar type-level maps that nevertheless hold the same entries. 
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
                  (t :: Map Symbol Type) 
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
              (t :: Map Symbol Type) 
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
    type RecordCode r :: Map Symbol Type
    -- https://stackoverflow.com/questions/22087549/defaultsignatures-and-associated-type-families/22088808
    type RecordCode r = RecordCode' E (G.Rep r)
    toRecord :: r -> Record I (RecordCode r)
    default toRecord :: (G.Generic r,ToRecordHelper E (G.Rep r),RecordCode r ~ RecordCode' E (G.Rep r)) => r -> Record I (RecordCode r)
    toRecord r = toRecord' unit (G.from r)

class ToRecordHelper (start :: Map Symbol Type) (g :: Type -> Type) where
    type RecordCode' start g :: Map Symbol Type
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

class FromRecordHelper (t :: Map Symbol Type) (g :: Type -> Type) where
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
type family VariantCode (s :: Type) :: Map Symbol Type where
    VariantCode s = VariantCode' E (G.Rep s)

type family VariantCode' (acc :: Map Symbol Type) (g :: Type -> Type) :: Map Symbol Type where
    VariantCode' acc (D1 meta fields) = VariantCode' acc fields
    VariantCode' acc (t1 G.:+: t2) = VariantCode' (VariantCode' acc t2) t1
    VariantCode' acc (C1 (G.MetaCons k _ _) (S1 ('G.MetaSel Nothing unpackedness strictness laziness) (Rec0 v))) = Insert k v acc
     
class FromVariant (s :: Type) where
    fromVariant :: Variant I (VariantCode s) -> s
    default fromVariant :: (G.Generic s, FromVariantHelper (VariantCode s) (G.Rep s)) => Variant I (VariantCode s) -> s
    fromVariant v = case fromVariant' @(VariantCode s) v of
        Just x -> G.to x
        Nothing -> error "fromVariant match fail. Should not happen."

class FromVariantHelper (t :: Map Symbol Type) (g :: Type -> Type) where
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

class ToVariantHelper (t :: Map Symbol Type) (g :: Type -> Type) where
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

type family DiscriminateBalL (l :: Map k v) (r :: Map k v) :: Bool where
    DiscriminateBalL (N R _ _ _ _) _ = False
    DiscriminateBalL _             _ = True

class BalanceableL (l :: Map Symbol Type) (k :: Symbol) (v :: Type) (r :: Map Symbol Type) where
    type BalL l k v r :: Map Symbol Type
    balLR :: Record f (N color l k v r) -> Record f (BalL l k v r)
    balLV :: Variant f (N color l k v r) -> Variant f (BalL l k v r)

class BalanceableHelperL (b :: Bool) (l :: Map Symbol Type) (k :: Symbol) (v :: Type) (r :: Map Symbol Type) where
    type BalL' b l k v r :: Map Symbol Type
    balLR' :: Record f (N color l k v r) -> Record f (BalL' b l k v r)
    balLV' :: Variant f (N color l k v r) -> Variant f (BalL' b l k v r)

instance (DiscriminateBalL l r ~ b, BalanceableHelperL b l k v r) => BalanceableL l k v r where
    type BalL l k v r = BalL' (DiscriminateBalL l r) l k v r
    balLR = balLR' @b @l @k @v @r
    balLV = balLV' @b @l @k @v @r

-- balleft :: RB a -> a -> RB a -> RB a
-- balleft (T R a x b) y c = T R (T B a x b) y c
instance BalanceableHelperL False (N R left1 k1 v1 right1) k2 v2 right2 where
    type BalL'              False (N R left1 k1 v1 right1) k2 v2 right2 =
                                  (N R (N B left1 k1 v1 right1) k2 v2 right2)
    balLR' (Node (Node left' v' right') v right) = Node (Node left' v' right') v right
    balLV' v = case v of LookLeft x  -> LookLeft (case x of LookLeft y  -> LookLeft y
                                                            Here y      -> Here y
                                                            LookRight y -> LookRight y)
                         Here x      -> Here x
                         LookRight x -> LookRight x

-- balleft bl x (T B a y b) = balance bl x (T R a y b)
-- the @(N B in the call to balance tree is misleading, as it is ingored...
instance (BalanceableHelper (ShouldBalance t1 (N R t2 z zv t3)) t1 y yv (N R t2 z zv t3)) => 
    BalanceableHelperL True t1 y yv (N B t2 z zv t3) where
    type BalL'         True t1 y yv (N B t2 z zv t3)     
             =  Balance t1 y yv (N R t2 z zv t3)
    balLR' (Node left1 v1 (Node left2 v2 right2)) = 
        balanceR @t1 @y @yv @(N R t2 z zv t3) (Node left1 v1 (Node left2 v2 right2))
    balLV' v = balanceV @t1 @y @yv @(N R t2 z zv t3) (case v of
        LookLeft l -> LookLeft l
        Here x -> Here x
        LookRight r -> LookRight (case r of
                            LookLeft l' -> LookLeft l'
                            Here x' -> Here x'
                            LookRight r' -> LookRight r'))

-- balleft bl x (T R (T B a y b) z c) = T R (T B bl x a) y (balance b z (sub1 c))
instance (BalanceableHelper    (ShouldBalance t3 (N R l k kv r)) t3 z zv  (N R l k kv r)) => 
    BalanceableHelperL True t1 y yv (N R (N B t2 u uv t3) z zv (N B l k kv r)) where
    type BalL'         True t1 y yv (N R (N B t2 u uv t3) z zv (N B l k kv r)) =
                             N R (N B t1 y yv t2) u uv (Balance t3 z zv (N R l k kv r))          
    balLR' (Node left1 v1 (Node (Node left2 v2 right2) vx (Node left3 v3 right3))) = 
            Node (Node left1 v1 left2) v2 (balanceR @t3 @z @zv @(N R l k kv r) (Node right2 vx (Node left3 v3 right3)))
    balLV' v = case v of LookLeft left1                          -> LookLeft (LookLeft left1)
                         Here v1                                 -> LookLeft (Here v1)
                         LookRight (LookLeft (LookLeft left2))   -> LookLeft (LookRight left2)
                         LookRight (LookLeft (Here v2))          -> Here v2
                         LookRight (LookLeft (LookRight right2)) -> LookRight (balanceV @t3 @z @zv @(N R l k kv r) (LookLeft right2))
                         LookRight (Here vx)                     -> LookRight (balanceV @t3 @z @zv @(N R l k kv r) (Here vx))
                         LookRight (LookRight rr)                -> LookRight (balanceV @t3 @z @zv @(N R l k kv r) (LookRight (case rr of
                                                                        LookLeft left3 -> LookLeft left3
                                                                        Here v3 -> Here v3
                                                                        LookRight right3 -> LookRight right3)))


-- balright :: RB a -> a -> RB a -> RB a
-- balright a x (T R b y c) = T R a x (T B b y c)
-- balright (T B a x b) y bl = balance (T R a x b) y bl
-- balright (T R a x (T B b y c)) z bl = T R (balance (sub1 a) x b) y (T B c z bl)
type family DiscriminateBalR (l :: Map k v) (r :: Map k v) :: Bool where
    DiscriminateBalR _ (N R _ _ _ _) = False
    DiscriminateBalR _ _             = True

class BalanceableR (l :: Map Symbol Type) (k :: Symbol) (v :: Type) (r :: Map Symbol Type) where
    type BalR l k v r :: Map Symbol Type
    balRR :: Record f (N color l k v r) -> Record f (BalR l k v r)
    balRV :: Variant f (N color l k v r) -> Variant f (BalR l k v r)

class BalanceableHelperR (b :: Bool) (l :: Map Symbol Type) (k :: Symbol) (v :: Type) (r :: Map Symbol Type) where
    type BalR' b l k v r :: Map Symbol Type
    balRR' :: Record f (N color l k v r) -> Record f (BalR' b l k v r)
    balRV' :: Variant f (N color l k v r) -> Variant f (BalR' b l k v r)

instance (DiscriminateBalR l r ~ b, BalanceableHelperR b l k v r) => BalanceableR l k v r where
    type BalR l k v r = BalR' (DiscriminateBalR l r) l k v r
    balRR = balRR' @b @l @k @v @r
    balRV = balRV' @b @l @k @v @r

-- balright :: RB a -> a -> RB a -> RB a
-- balright a x (T R b y c) = T R a x (T B b y c)
instance BalanceableHelperR False right2 k2 v2 (N R left1 k1 v1 right1) where
    type BalR'              False right2 k2 v2 (N R left1 k1 v1 right1) =
                                  (N R right2 k2 v2 (N B left1 k1 v1 right1))
    balRR' (Node right v (Node left' v' right')) = Node  right v (Node left' v' right')
    balRV' v = case v of LookLeft x   -> LookLeft x
                         Here x       -> Here x
                         LookRight x  -> LookRight (case x of LookLeft y  -> LookLeft y
                                                              Here y      -> Here y
                                                              LookRight y -> LookRight y)

-- balright (T B a x b) y bl = balance (T R a x b) y bl
instance (BalanceableHelper    (ShouldBalance (N R t2 z zv t3) t1) (N R t2 z zv t3) y yv t1) => 
    BalanceableHelperR True (N B t2 z zv t3) y yv t1 where
    type BalR'         True (N B t2 z zv t3) y yv t1     
             =  Balance (N R t2 z zv t3) y yv t1
    balRR' (Node (Node left1 v1 right1) v2 right2) = balanceR @(N R t2 z zv t3) @y @yv @t1 
           (Node (Node left1 v1 right1) v2 right2)
    balRV' v = balanceV @(N R t2 z zv t3) @y @yv @t1 (case v of
        LookLeft l -> LookLeft (case l of 
            LookLeft l' -> LookLeft l'
            Here x' -> Here x'
            LookRight r' -> LookRight r')
        Here x -> Here x
        LookRight r -> LookRight r)

-- balright (T R a x (T B b y c)) z bl = T R (balance (sub1 a) x b) y (T B c z bl)
instance (BalanceableHelper    (ShouldBalance (N R t2 u uv t3) l) (N R t2 u uv t3) z zv l) => 
    BalanceableHelperR True (N R (N B t2 u uv t3) z zv (N B l k kv r)) y yv t1 where
    type BalR'         True (N R (N B t2 u uv t3) z zv (N B l k kv r)) y yv t1 =
                             N R (Balance (N R t2 u uv t3) z zv l) k kv (N B r y yv t1) 
    balRR' (Node (Node (Node left2 v2 right2) vx (Node left3 v3 right3)) v1 left1) = 
            Node (balanceR @(N R t2 u uv t3) @z @zv @l (Node (Node left2 v2 right2) vx left3)) v3 (Node right3 v1 left1)
    balRV' v = case v of
        LookLeft  (LookLeft rr)                 -> LookLeft (balanceV @(N R t2 u uv t3) @z @zv @l (LookLeft (case rr of
                                                        LookLeft t2 -> LookLeft t2
                                                        Here uv -> Here uv
                                                        LookRight t3 -> LookRight t3)))
        LookLeft  (Here zv)                     -> LookLeft (balanceV @(N R t2 u uv t3) @z @zv @l (Here zv))
        LookLeft  (LookRight (LookLeft l))      -> LookLeft (balanceV @(N R t2 u uv t3) @z @zv @l (LookRight l))
        LookLeft  (LookRight (Here kv))         -> Here kv
        LookLeft  (LookRight (LookRight r))     -> LookRight (LookLeft r)
        Here      yv                            -> LookRight (Here yv) 
        LookRight t1                            -> LookRight (LookRight t1)

-- app :: RB a -> RB a -> RB a
-- app E x = x
-- app x E = x
-- app (T R a x b) (T R c y d) =
--  case app b c of
--      T R b' z c' -> T R(T R a x b') z (T R c' y d)
--      bc -> T R a x (T R bc y d)
-- app (T B a x b) (T B c y d) = 
--  case app b c of
--      T R b' z c' -> T R(T B a x b') z (T B c' y d)
--      bc -> balleft a x (T B bc y d)
-- app a (T R b x c) = T R (app a b) x c
-- app (T R a x b) c = T R a x (app b c)


class Fuseable (l :: Map Symbol Type) (r :: Map Symbol Type) where
    type Fuse l r :: Map Symbol Type
    fuseRecord :: Record f l -> Record f r -> Record f (Fuse l r)
    fuseVariant :: Either (Variant f l) (Variant f r) -> Variant f (Fuse l r)

instance Fuseable E E where
    type Fuse E E = E
    fuseRecord _ _ = unit
    fuseVariant v = case v of

-- app E x = x
instance Fuseable E (N color left k v right) where
    type Fuse E (N color left k v right) = N color left k v right
    fuseRecord _ r = r
    fuseVariant e = case e of
        Right v -> v

-- app x E = x
instance Fuseable (N color left k v right) E where
    type Fuse (N color left k v right) E = N color left k v right
    fuseRecord r _ = r
    fuseVariant e = case e of
        Left v -> v

-- app a (T R b x c) = T R (app a b) x c
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


-- app (T R a x b) c = T R a x (app b c)
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


-- app (T R a x b) (T R c y d) =
instance (Fuseable right1 left2, Fuse right1 left2 ~ fused, FuseableHelper1 fused (N R left1 k1 v1 right1) (N R left2 k2 v2 right2)) => Fuseable (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) where
    type Fuse (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) = Fuse1 (Fuse right1 left2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) 
    fuseRecord = fuseRecord1 @(Fuse right1 left2) 
    fuseVariant = fuseVariant1 @(Fuse right1 left2)

class FuseableHelper1 (fused :: Map Symbol Type) (l :: Map Symbol Type) (r :: Map Symbol Type) where
    type Fuse1 fused l r :: Map Symbol Type
    fuseRecord1 :: Record f l -> Record f r -> Record f (Fuse l r)
    fuseVariant1 :: Either (Variant f l) (Variant f r) -> Variant f (Fuse l r)

-- app (T R a x b) (T R c y d) =
--  case app b c of
--      T R b' z c' -> T R (T R a x b') z (T R c' y d)
-- FIXME: The Fuseable constraint is repeated from avobe :(
instance (Fuseable right1 left2, Fuse right1 left2 ~ N R s1 z zv s2) => FuseableHelper1 (N R s1 z zv s2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) where
    type Fuse1 (N R s1 z zv s2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) = N R (N R left1 k1 v1 s1) z zv (N R s2 k2 v2 right2)
    fuseRecord1 (Node left1 v1 right1) (Node left2 v2 right2) = 
        case fuseRecord right1 left2 of
            Node s1 zv s2 -> Node (Node left1 v1 s1) zv (Node s2 v2 right2)
    fuseVariant1 e = 
        case e of
            Left l  -> case l of
                            LookLeft  left1  -> LookLeft (LookLeft left1)
                            Here      v1     -> LookLeft (Here v1)
                            LookRight right1 -> case fuseVariant @right1 @left2 (Left right1) of
                                                    LookLeft s1  -> LookLeft (LookRight s1)
                                                    Here zv      -> Here zv
                                                    LookRight s2 -> LookRight (LookLeft s2)
            Right r -> case r of 
                            LookLeft  left2  -> case fuseVariant @right1 @left2 (Right left2) of
                                                    LookLeft s1  -> LookLeft (LookRight s1)
                                                    Here zv      -> Here zv
                                                    LookRight s2 -> LookRight (LookLeft s2)
                            Here      v2     -> LookRight (Here v2)
                            LookRight right2 -> LookRight (LookRight right2)


-- app (T R a x b) (T R c y d) =
--  case app b c of
--      ...
--      bc -> T R a x (T R bc y d)
-- FIXME: The Fuseable constraint is repeated from above :(
instance (Fuseable right1 left2, Fuse right1 left2 ~ N B s1 z zv s2) => FuseableHelper1 (N B s1 z zv s2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) where
    type Fuse1 (N B s1 z zv s2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) = N R left1 k1 v1 (N R (N B s1 z zv s2) k2 v2 right2)
    fuseRecord1 (Node left1 v1 right1) (Node left2 v2 right2) = 
        case fuseRecord right1 left2 of
            Node s1 zv s2 -> Node left1 v1 (Node (Node s1 zv s2) v2 right2)
    fuseVariant1 e = 
        case e of
            Left l  -> case l of
                            LookLeft  left1  -> LookLeft left1
                            Here      v1     -> Here v1
                            LookRight right1 -> case fuseVariant @right1 @left2 (Left right1) of
                                                    LookLeft s1  -> LookRight (LookLeft (LookLeft s1))
                                                    Here zv      -> LookRight (LookLeft (Here zv))
                                                    LookRight s2 -> LookRight (LookLeft (LookRight s2))
            Right r -> case r of 
                            LookLeft  left2  -> case fuseVariant @right1 @left2 (Right left2) of
                                                    LookLeft s1  -> LookRight (LookLeft (LookLeft s1))
                                                    Here zv      -> LookRight (LookLeft (Here zv))
                                                    LookRight s2 -> LookRight (LookLeft (LookRight s2))
                            Here      v2     -> LookRight (Here v2)
                            LookRight right2 -> LookRight (LookRight right2)

-- app (T R a x b) (T R c y d) =
--  case app b c of
--      ...
--      bc -> T R a x (T R bc y d)
instance FuseableHelper1 E (N R left1 k1 v1 E) (N R E k2 v2 right2) where
    type Fuse1 E (N R left1 k1 v1 E) (N R E k2 v2 right2) = N R left1 k1 v1 (N R E k2 v2 right2)
    fuseRecord1 (Node left1 v1 right1) (Node left2 v2 right2) = Node left1 v1 (Node Empty v2 right2)
    fuseVariant1 e = 
        case e of
            Left l  -> case l of
                            LookLeft  left1  -> LookLeft left1
                            Here      v1     -> Here v1
            Right r -> case r of 
                            Here      v2     -> LookRight (Here v2)
                            LookRight right2 -> LookRight (LookRight right2)

-- app (T B a x b) (T B c y d) = 
instance (Fuseable right1 left2, Fuse right1 left2 ~ fused, FuseableHelper2 fused (N B left1 k1 v1 right1) (N B left2 k2 v2 right2)) => Fuseable (N B left1 k1 v1 right1) (N B left2 k2 v2 right2) where
    type Fuse (N B left1 k1 v1 right1) (N B left2 k2 v2 right2) = Fuse2 (Fuse right1 left2) (N B left1 k1 v1 right1) (N B left2 k2 v2 right2) 
    fuseRecord = fuseRecord2 @(Fuse right1 left2) 
    fuseVariant = fuseVariant2 @(Fuse right1 left2)

-- could FuseableHelper1 and FuseableHelper2 be, well... fused?
class FuseableHelper2 (fused :: Map Symbol Type) (l :: Map Symbol Type) (r :: Map Symbol Type) where
    type Fuse2 fused l r :: Map Symbol Type
    fuseRecord2 :: Record f l -> Record f r -> Record f (Fuse l r)
    fuseVariant2 :: Either (Variant f l) (Variant f r) -> Variant f (Fuse l r)

-- app (T B a x b) (T B c y d) = 
--  case app b c of
--      T R b' z c' -> T R (T B a x b') z (T B c' y d)
instance (Fuseable right1 left2, Fuse right1 left2 ~ N R s1 z zv s2) => FuseableHelper2 (N R s1 z zv s2) (N B left1 k1 v1 right1) (N B left2 k2 v2 right2) where
    type Fuse2 (N R s1 z zv s2) (N B left1 k1 v1 right1) (N B left2 k2 v2 right2) = N R (N B left1 k1 v1 s1) z zv (N B s2 k2 v2 right2)
    fuseRecord2 (Node left1 v1 right1) (Node left2 v2 right2) = 
        case fuseRecord right1 left2 of
            Node s1 zv s2 -> Node (Node left1 v1 s1) zv (Node s2 v2 right2) 
    fuseVariant2 e =
        case e of
            Left l  -> case l of
                            LookLeft  left1  -> LookLeft (LookLeft left1)
                            Here      v1     -> LookLeft (Here v1)
                            LookRight right1 -> case fuseVariant @right1 @left2 (Left right1) of
                                                    LookLeft s1  -> LookLeft (LookRight s1)
                                                    Here zv      -> Here zv
                                                    LookRight s2 -> LookRight (LookLeft s2)
            Right r -> case r of 
                            LookLeft  left2  -> case fuseVariant @right1 @left2 (Right left2) of
                                                    LookLeft s1  -> LookLeft (LookRight s1)
                                                    Here zv      -> Here zv
                                                    LookRight s2 -> LookRight (LookLeft s2)
                            Here      v2     -> LookRight (Here v2)
                            LookRight right2 -> LookRight (LookRight right2)

-- app (T B a x b) (T B c y d) = 
--  case app b c of
--      ...
--      bc -> balleft a x (T B bc y d)
instance (Fuseable right1 left2, Fuse right1 left2 ~ N B s1 z zv s2, BalanceableL left1 k1 v1 (N B (N B s1 z zv s2) k2 v2 right2)) => FuseableHelper2 (N B s1 z zv s2) (N B left1 k1 v1 right1) (N B left2 k2 v2 right2) where
    type Fuse2 (N B s1 z zv s2) (N B left1 k1 v1 right1) (N B left2 k2 v2 right2) = BalL left1 k1 v1 (N B (N B s1 z zv s2) k2 v2 right2)
    fuseRecord2 (Node left1 v1 right1) (Node left2 v2 right2) = 
        case fuseRecord @right1 @left2 right1 left2 of
            Node s1 zv s2 -> balLR @left1 @k1 @v1 @(N B (N B s1 z zv s2) k2 v2 right2) (Node left1 v1 (Node (Node s1 zv s2) v2 right2))
    fuseVariant2 e = balLV @left1 @k1 @v1 @(N B (N B s1 z zv s2) k2 v2 right2) (case e of
            Left l  -> case l of
                            LookLeft  left1  -> LookLeft left1
                            Here      v1     -> Here v1
                            LookRight right1 -> case fuseVariant @right1 @left2 (Left right1) of
                                                    LookLeft s1  -> LookRight (LookLeft (LookLeft s1))
                                                    Here zv      -> LookRight (LookLeft (Here zv))
                                                    LookRight s2 -> LookRight (LookLeft (LookRight s2))
            Right r -> case r of 
                            LookLeft  left2  -> case fuseVariant @right1 @left2 (Right left2) of
                                                    LookLeft s1  -> LookRight (LookLeft (LookLeft s1))
                                                    Here zv      -> LookRight (LookLeft (Here zv))
                                                    LookRight s2 -> LookRight (LookLeft (LookRight s2))
                            Here      v2     -> LookRight (Here v2)
                            LookRight right2 -> LookRight (LookRight right2))

-- app (T B a x b) (T B c y d) = 
--  case app b c of
--      ...
--      bc -> balleft a x (T B bc y d)
instance (BalanceableL left1 k1 v1 (N B E k2 v2 right2)) => FuseableHelper2 E (N B left1 k1 v1 E) (N B E k2 v2 right2) where
    type Fuse2  E (N B left1 k1 v1 E) (N B E k2 v2 right2) = BalL left1 k1 v1 (N B E k2 v2 right2)
    fuseRecord2 (Node left1 v1 right1) (Node left2 v2 right2) = 
            balLR @left1 @k1 @v1 @(N B E k2 v2 right2) (Node left1 v1 (Node Empty v2 right2))
    fuseVariant2 e = balLV @left1 @k1 @v1 @(N B E k2 v2 right2) (case e of
            Left l  -> case l of
                            LookLeft  left1  -> LookLeft left1
                            Here      v1     -> Here v1
            Right r -> case r of 
                            Here      v2     -> LookRight (Here v2)
                            LookRight right2 -> LookRight (LookRight right2))


--  del E = E
--  del (T _ a y b)
--      | x<y = delformLeft a y b
--      | x>y = delformRight a y b
--      | otherwise = app a b
class Delable (k :: Symbol) (v :: Type) (t :: Map Symbol Type) where
    type Del k v t :: Map Symbol Type
    del :: Record f t -> Record f (Del k v t)
    win :: Variant f t -> Either (Variant f (Del k v t)) (f v) 

--  delformLeft a@(T B _ _ _) y b = balleft (del a) y b
--  delformLeft a y b = T R (del a) y b
--  In the term-level code, the k to delete is already on the environment.
class DelableL (k :: Symbol) (v :: Type) (l :: Map Symbol Type) (kx :: Symbol) (vx :: Type) (r :: Map Symbol Type) where
    type DelL k v l kx vx r :: Map Symbol Type
    delL :: Record f (N color l kx vx r) -> Record f (DelL k v l kx vx r)
    winL :: Variant f (N color l kx vx r) -> Either (Variant f (DelL k v l kx vx r)) (f v) 

--  delformLeft a@(T B _ _ _) y b = balleft (del a) y b
instance (Delable k v (N B leftz kz vz rightz), BalanceableL (Del k v (N B leftz kz vz rightz)) kx vx right) 
    => DelableL k v (N B leftz kz vz rightz) kx vx right where
    type DelL k v (N B leftz kz vz rightz) kx vx right = BalL (Del k v (N B leftz kz vz rightz)) kx vx right
    delL (Node left vx right) = balLR @(Del k v (N B leftz kz vz rightz)) @kx @vx @right (Node (del @k @v left) vx right)
    winL v = first (balLV @(Del k v (N B leftz kz vz rightz)) @kx @vx @right) (case v of
        LookLeft l -> first LookLeft (win @k @v l)
        Here vx -> Left $ Here vx
        LookRight r -> Left $ LookRight r)

--  delformLeft a y b = T R (del a) y b
instance (Delable k v (N R leftz kz vz rightz)) => DelableL k v (N R leftz kz vz rightz) kx vx right where
    type DelL k v (N R leftz kz vz rightz) kx vx right = N R (Del k v (N R leftz kz vz rightz)) kx vx right
    delL (Node left vx right) = Node (del @k @v left) vx right
    winL v = case v of
        LookLeft l -> first LookLeft (win @k @v l)
        Here vx -> Left (Here vx)
        LookRight r -> Left (LookRight r)

--  delformLeft a y b = T R (del a) y b
instance DelableL k v E kx vx right where
    type DelL k v E kx vx right = N R E kx vx right
    delL (Node left vx right) = Node Empty vx right
    winL v = case v of
        Here vx -> Left (Here vx)
        LookRight r -> Left (LookRight r)

--  delformRight a y b@(T B _ _ _) = balright a y (del b)
--  delformRight a y b = T R a y (del b)
class DelableR (k :: Symbol) (v :: Type) (l :: Map Symbol Type) (kx :: Symbol) (vx :: Type) (r :: Map Symbol Type) where
    type DelR k v l kx vx r :: Map Symbol Type
    delR :: Record f (N color l kx vx r) -> Record f (DelR k v l kx vx r)
    winR :: Variant f (N color l kx vx r) -> Either (Variant f (DelR k v l kx vx r)) (f v) 

--  delformRight a y b@(T B _ _ _) = balright a y (del b)
instance (Delable k v (N B leftz kz vz rightz), BalanceableR left kx vx (Del k v (N B leftz kz vz rightz))) => DelableR k v left kx vx (N B leftz kz vz rightz) where
    type DelR k v left kx vx (N B leftz kz vz rightz) = BalR left kx vx (Del k v (N B leftz kz vz rightz))
    delR (Node left vx right) = balRR @left @kx @vx @(Del k v (N B leftz kz vz rightz)) (Node left vx (del @k @v right))
    winR v = first (balRV @left @kx @vx @(Del k v (N B leftz kz vz rightz))) (case v of
        LookLeft l -> Left $ LookLeft l
        Here vx -> Left $ Here vx
        LookRight r -> first LookRight (win @k @v r))

--  delformRight a y b = T R a y (del b)
instance (Delable k v (N R leftz kz vz rightz)) => DelableR k v left kx vx (N R leftz kz vz rightz) where
    type DelR k v left kx vx (N R leftz kz vz rightz) = N R left kx vx (Del k v (N R leftz kz vz rightz))
    delR (Node left vx right) = Node left vx (del @k @v right)
    winR v = case v of
        LookLeft l -> Left (LookLeft l)
        Here vx -> Left (Here vx)
        LookRight r -> first LookRight (win @k @v r)

--  delformRight a y b = T R a y (del b)
instance DelableR k v left kx vx E where
    type DelR k v left kx vx E = N R left kx vx E
    delR (Node left vx right) = Node left vx Empty
    winR v = case v of
        LookLeft l -> Left (LookLeft l)
        Here vx -> Left (Here vx)

--  del E = E
instance Delable k v E where
    type Del k v E = E
    del _ = unit
    win = impossible

-- the color is discarded
--  del (T _ a y b)
--      | x<y = delformLeft a y b
--      | x>y = delformRight a y b
--      | otherwise = app a b
instance (CmpSymbol kx k ~ ordering, DelableHelper ordering k v left kx vx right) => Delable k v (N color left kx vx right) where
    type Del k v (N color left kx vx right) = Del' (CmpSymbol kx k) k v left kx vx right
    del = del' @(CmpSymbol kx k) @k @v @left @kx @vx @right
    win = win' @(CmpSymbol kx k) @k @v @left @kx @vx @right

class DelableHelper (ordering :: Ordering) (k :: Symbol) (v :: Type) (l :: Map Symbol Type) (kx :: Symbol) (vx :: Type) (r :: Map Symbol Type) where
    type Del' ordering k v l kx vx r :: Map Symbol Type
    del' :: Record f (N color l kx vx r) -> Record f (Del' ordering k v l kx vx r)
    win' :: Variant f (N color l kx vx r) -> Either (Variant f (Del' ordering k v l kx vx r)) (f v) 

--      | x<y = delformLeft a y b
instance DelableL k v left kx vx right => DelableHelper GT k v left kx vx right where
    type Del' GT k v left kx vx right = DelL k v left kx vx right
    del' = delL @k @v @left @kx @vx @right  
    win' = winL @k @v @left @kx @vx @right  

--      | otherwise = app a b
instance Fuseable left right => DelableHelper EQ k v left k v right where
    type Del' EQ k v left k v right = Fuse left right
    del' (Node left _ right) = fuseRecord @left @right left right 
    win' v = case v of
        LookLeft l  ->  Left $ fuseVariant @left @right (Left l)
        Here v      -> Right v 
        LookRight r -> Left $ fuseVariant @left @right (Right r)

--      | x>y = delformRight a y b
instance DelableR k v left kx vx right => DelableHelper LT k v left kx vx right where
    type Del' LT k v left kx vx right = DelR k v left kx vx right
    del' = delR @k @v @left @kx @vx @right  
    win' = winR @k @v @left @kx @vx @right  

{- | Class that determines if the pair of a 'Symbol' key and a 'Type' can
     be deleted from a type-level map.
 
     The associated type family 'Delete' produces the resulting map.

     At the term level, this manifests in 'delete', which removes a field from
     a record, and in 'winnow', which checks if a 'Variant' is of a given
     branch and returns the value in the branch if there's a match, or a
     reduced 'Variant' if there isn't. 'winnow' tends to be more useful in
     practice.

     If the map already has the key but with a /different/ 'Type', the deletion
     fails to compile.
 -}
class Deletable (k :: Symbol) (v :: Type) (t :: Map Symbol Type) where
    type Delete k v t :: Map Symbol Type
    delete :: Record f t -> Record f (Delete k v t)
    winnow :: Variant f t -> Either (Variant f (Delete k v t)) (f v) 

instance (Delable k v t, CanMakeBlack (Del k v t)) => Deletable k v t where
    type Delete k v t = MakeBlack (Del k v t)
    delete r = makeBlackR (del @k @v r) 
    winnow v = first makeBlackV (win @k @v v)


{- | Like 'winnow' but specialized to pure 'Variant's.
-}
winnowI :: forall k v t . Deletable k v t => Variant I t -> Either (Variant I (Delete k v t)) v
winnowI = fmap unI . winnow @k @v @t

-- The original term-level code, taken from:
-- https://www.cs.kent.ac.uk/people/staff/smk/redblack/rb.html
--
-- {- Version 1, 'untyped' -}
-- data Color = R | B deriving Show
-- data RB a = E | T Color (RB a) a (RB a) deriving Show
-- 
-- {- Insertion and membership test as by Okasaki -}
-- insert :: Ord a => a -> RB a -> RB a
-- insert x s =
--  T B a z b
--  where
--  T _ a z b = ins s
--  ins E = T R E x E
--  ins s@(T B a y b)
--      | x<y = balance (ins a) y b
--      | x>y = balance a y (ins b)
--      | otherwise = s
--  ins s@(T R a y b)
--      | x<y = T R (ins a) y b
--      | x>y = T R a y (ins b)
--      | otherwise = s
-- 
-- 
-- {- balance: first equation is new,
--    to make it work with a weaker invariant -}
-- balance :: RB a -> a -> RB a -> RB a
-- balance (T R a x b) y (T R c z d) = T R (T B a x b) y (T B c z d)
-- balance (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
-- balance (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
-- balance a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
-- balance a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
-- balance a x b = T B a x b
--
-- member :: Ord a => a -> RB a -> Bool
-- member x E = False
-- member x (T _ a y b)
--  | x<y = member x a
--  | x>y = member x b
--  | otherwise = True
-- 
-- {- deletion a la SMK -}
-- delete :: Ord a => a -> RB a -> RB a
-- delete x t =
--  case del t of {T _ a y b -> T B a y b; _ -> E}
--  where
--  del E = E
--  del (T _ a y b)
--      | x<y = delformLeft a y b
--      | x>y = delformRight a y b
--             | otherwise = app a b
--  delformLeft a@(T B _ _ _) y b = balleft (del a) y b
--  delformLeft a y b = T R (del a) y b
--
--  delformRight a y b@(T B _ _ _) = balright a y (del b)
--  delformRight a y b = T R a y (del b)
-- 
-- balleft :: RB a -> a -> RB a -> RB a
-- balleft (T R a x b) y c = T R (T B a x b) y c
-- balleft bl x (T B a y b) = balance bl x (T R a y b)
-- balleft bl x (T R (T B a y b) z c) = T R (T B bl x a) y (balance b z (sub1 c))
-- 
-- balright :: RB a -> a -> RB a -> RB a
-- balright a x (T R b y c) = T R a x (T B b y c)
-- balright (T B a x b) y bl = balance (T R a x b) y bl
-- balright (T R a x (T B b y c)) z bl = T R (balance (sub1 a) x b) y (T B c z bl)
-- 
-- sub1 :: RB a -> RB a
-- sub1 (T B a x b) = T R a x b
-- sub1 _ = error "invariance violation"
-- 
-- app :: RB a -> RB a -> RB a
-- app E x = x
-- app x E = x
-- app (T R a x b) (T R c y d) =
--  case app b c of
--      T R b' z c' -> T R (T R a x b') z (T R c' y d)
--      bc -> T R a x (T R bc y d)
-- app (T B a x b) (T B c y d) = 
--  case app b c of
--      T R b' z c' -> T R(T B a x b') z (T B c' y d)
--      bc -> balleft a x (T B bc y d)
-- app a (T R b x c) = T R (app a b) x c
-- app (T R a x b) c = T R a x (app b c)

