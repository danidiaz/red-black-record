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
             EmptyCase,
             StandaloneKindSignatures

#-}
{-#  OPTIONS_GHC -Wno-partial-type-signatures  #-}

module Data.RBR.Internal where

import           Data.Proxy
import           Data.Kind
import           Data.Typeable
import           Data.Coerce
import           Data.Functor.Contravariant (Contravariant(contramap))
import           Data.Bifunctor (first)
import           Data.Monoid (Endo(..))
import           Data.List (intersperse)
import           Data.Foldable (asum)
import           GHC.TypeLits
import           GHC.Generics (D1,C1,S1(..),M1(..),K1(..),Rec0(..), Generically(..))
import qualified GHC.Generics as G

import           Data.SOP (I(..),K(..),unI,unK,NP(..),NS(..),All,SListI,type (-.->)(Fn,apFn),mapKIK,(:.:)(..),Top)
import           Data.SOP.NP (collapse_NP,liftA_NP,liftA2_NP,cliftA_NP,cliftA2_NP,pure_NP,sequence_NP,sequence'_NP)
import           Data.SOP.NS (collapse_NS,ap_NS,injections,Injection)


{- $setup
 
>>> :set -XDataKinds -XTypeApplications -XPartialTypeSignatures -XFlexibleContexts -XTypeFamilies -XDeriveGeneric 
>>> :set -Wno-partial-type-signatures  
>>> import Data.RBR
>>> import Data.SOP
>>> import GHC.Generics

-}


-- | The color of a node.
data Color = R
           | B
    deriving (Show,Eq)

-- | A Red-Black tree. It will be used as a kind, to index the 'Record' and 'Variant' types.
data Map symbol q = E 
             | N Color (Map symbol q) symbol q (Map symbol q)
    deriving (Show,Eq)

-- | A map without entries. See also 'unit' and 'impossible'.
type Empty = E

--
--
-- This code has been copied and adapted from the corresponding Data.SOP code (the All constraint).
--

-- Why is this KeysValuesAllF type family needed at all? Why is not KeysValuesAll sufficient by itself?
-- In fact, if I delete KeysValuesAllF and use eclusively KeysValuesAll, functions like demoteKeys seem to still work fine.
--
-- UndecidableSuperClasses and RankNTypes seem to be required by KeysValuesAllF.
type KeysValuesAllF :: (symbol -> q -> Constraint) -> Map symbol q -> Constraint
type family
  KeysValuesAllF c t :: Constraint where
  KeysValuesAllF _ E                        = ()
  KeysValuesAllF c (N color left k v right) = (c k v, KeysValuesAll c left, KeysValuesAll c right)

{- | Require a constraint for every key-value pair in a tree. This is a generalization of 'Data.SOP.All' from "Data.SOP".
-}
type KeysValuesAll :: (symbol -> q -> Constraint) -> Map symbol q -> Constraint
class KeysValuesAllF c t => KeysValuesAll (c :: symbol -> q -> Constraint) (t :: Map symbol q) where

  --  'cpara_Map' constructs a 'Record' by means of a constraint for producing
  --  the nodes of the tree. The constraint is passed as a 'Data.Proxy.Proxy'.
  cpara_Map ::
       proxy c
    -> r E
    -> (forall left k v right color . (c k v, KeysValuesAll c left, KeysValuesAll c right) 
                                   => r left -> r right -> r (N color left k v right))
    -> r t

{- | This typeclass provides generalizations of 'Applicative'-like functions
     which work over 'Record's and 'Variant's.
-}
type Maplike :: Map Symbol Type -> Constraint
class Maplike (t :: Map Symbol Type) where
    {- | 
         See 'cpure_Record' and 'cpure'_Record' for more useful versions of
         this function.

         The naming scheme follows that of 'Data.SOP.NP.pure_NP'.
    -}
    pure_Record :: (forall v. f v) -> Record f t
    {- | 
         Pulls out an 'Applicative' that wraps each field, resulting in an 'Applicative' containing a pure 'Record'.

         The naming scheme follows that of 'Data.SOP.NP.sequence_NP'.
    -}
    sequence_Record :: Applicative f => Record f t -> f (Record I t)
    {- | 
         Like 'sequence_Record', but only pulls out the outer 'Applicative'
         from an 'Applicative' composition that wraps each field. See
         'Data.SOP.:.:'.

         This can be useful for staged computations, where each stage is
         represented by an 'Applicative' layer.

         The naming scheme follows that of 'Data.SOP.NP.sequence'_NP'.
    -}
    sequence'_Record :: Applicative f => Record (f :.: g) t -> f (Record g t)
    {- | Apply a transformation to the type constructor which wraps the fields of a 'Record'.
     
         The naming scheme follows that of 'Data.SOP.NP.liftA_NP'.
    -}
    liftA_Record :: (forall a. f a -> g a) -> Record f t -> Record g t
    {- | 
         The naming scheme follows that of 'Data.SOP.NP.liftA2_NP'.
    -}
    liftA2_Record :: (forall a. f a -> g a -> h a) -> Record f t -> Record g t -> Record h t
    {- | Apply a transformation to the active branch of a 'Variant'.
     
         The naming scheme follows that of 'Data.SOP.NS.liftA_NS'.
    -}
    liftA_Variant :: (forall a. f a -> g a) -> Variant f t -> Variant g t
    {- | Given a 'Record' of transformation, apply the one which matches the active branch of 'Variant'.
     
         The naming scheme follows that of 'Data.SOP.NS.liftA2_NS'.
    -}
    liftA2_Variant :: (forall a. f a -> g a -> h a) -> Record f t -> Variant g t -> Variant h t
    {- | 
         Constructs a 'Record' made of functions which take a value of the
         field's type and inject it in the 'Variant' branch which corresponds
         to the field.

         Compare to 'Data.SOP.NS.injections' from @generics-sop@.
    -}
    injections'_Variant :: Record (Case f (Variant f t)) t
    {- | 
         Constructs a 'Record' made of functions which take a value of the
         field's type and return a record updater function that sets the field.
    -}
    injections_Record :: Record (Case f (Endo (Record f t))) t
    {- | Collapse a 'Record' composed of 'K' monoidal annotations.
        
    >>> collapse'_Record (unit :: Record (K [Bool]) Empty)
    []

    >>> collapse'_Record (insert @"bar" (K [False]) unit)
    [False]

    The naming scheme follows that of 'Data.SOP.NP.collapse_NP'.

    -}
    collapse'_Record :: Monoid a => Record (K a) t -> a
    collapse_Variant :: Variant (K a) t -> a

instance Maplike E where
    pure_Record _ = Empty
    sequence_Record Empty = pure Empty
    sequence'_Record Empty = pure Empty
    liftA_Record _ Empty = Empty
    liftA2_Record _ Empty Empty = Empty
    liftA_Variant _ neverHappens = impossible neverHappens
    liftA2_Variant _ Empty neverHappens = impossible neverHappens
    injections'_Variant = Empty
    injections_Record = Empty
    collapse'_Record Empty = mempty
    collapse_Variant = impossible

instance (Maplike left, Maplike right) => Maplike (N color left k v right) where
    pure_Record f = Node (pure_Record f) f (pure_Record f)
    sequence_Record (Node left v right) = (\l x r -> Node l (I x) r) <$> sequence_Record left <*> v <*> sequence_Record right
    sequence'_Record (Node left (Comp v) right) = (\l x r -> Node l x r) <$> sequence'_Record left <*> v <*> sequence'_Record right
    liftA_Record trans (Node left1 v1 right1) = Node (liftA_Record trans left1) (trans v1) (liftA_Record trans right1)
    liftA2_Record trans (Node left1 v1 right1) (Node left2 v2 right2) = Node (liftA2_Record trans left1 left2) (trans v1 v2) (liftA2_Record trans right1 right2)
    liftA_Variant trans vv = case vv of
        Here  fv -> Here (trans fv)
        LookLeft leftV -> LookLeft (liftA_Variant trans leftV)
        LookRight rightV -> LookRight (liftA_Variant trans rightV)
    liftA2_Variant trans (Node left rv right) vv = case vv of
        Here  fv -> Here (trans rv fv)
        LookLeft leftV -> LookLeft (liftA2_Variant trans left leftV)
        LookRight rightV -> LookRight (liftA2_Variant trans right rightV)
    injections'_Variant = 
        let injections_Left = liftA_Record (\(Case j) -> Case $ LookLeft . j) (injections'_Variant @left)
            injections_Right = liftA_Record (\(Case j) -> Case $ LookRight . j) (injections'_Variant @right)
         in Node injections_Left (Case $ Here) injections_Right
    injections_Record = 
         Node 
             (liftA_Record (\(Case cleft) -> 
                                (Case $ \x -> 
                                    Endo $ (\(Node left' x' right') -> Node (appEndo (cleft x)  left') x' right')))

                           (injections_Record @left))
             (Case $ \x -> Endo $ \(Node left v right) -> Node left x right) 
             (liftA_Record (\(Case cright) -> 
                                (Case $ \x -> 
                                    Endo $ (\(Node left' x' right') -> Node left' x' (appEndo (cright x) right'))))

                           (injections_Record @right))  
    collapse'_Record (Node left (K v) right) = collapse'_Record left <> (v <> collapse'_Record right) 
    collapse_Variant vv = case vv of
        Here (K a) -> a
        LookLeft leftV -> collapse_Variant leftV
        LookRight rightV -> collapse_Variant rightV

{-# DEPRECATED injections_Variant "Use injections'_Variant instead" #-}
injections_Variant :: Maplike t => Record (VariantInjection f t) t
injections_Variant = liftA_Record (\(Case f) -> VariantInjection f) injections'_Variant 

{-# DEPRECATED VariantInjection "Use Case instead" #-}
newtype VariantInjection (f :: q -> Type) (t :: Map Symbol q) (v :: q) = VariantInjection { runVariantInjection :: f v -> Variant f t }

instance KeysValuesAll c E where
  cpara_Map _p nil _step = nil

instance (c k v, KeysValuesAll c left, KeysValuesAll c right) => KeysValuesAll c (N color left k v right) where
  cpara_Map p nil cons =
    cons (cpara_Map p nil cons) (cpara_Map p nil cons)

{- |
    Create a 'Record', knowing that both keys and values satisfy a 2-place constraint. The constraint is passed as a 'Data.Proxy.Proxy'.

    The naming scheme follows that of 'Data.SOP.NP.cpure_NP'.
 -}
cpure_Record :: forall c t f. KeysValuesAll c t => Proxy c -> (forall k v. c k v => f v) -> Record f t
cpure_Record _ fpure = cpara_Map (Proxy @c) unit go
    where
    go :: forall left k' v' right color. (c k' v', KeysValuesAll c left, KeysValuesAll c right) 
       => Record f left
       -> Record f right
       -> Record f (N color left k' v' right)
    go left right = Node left (fpure @k' @v') right 

{- |
    Create a 'Record', knowing that the keys can be demoted to strings and that
    the values satisfy some constraint. The constraint is passed as a
    'Data.Proxy.Proxy'.

    The function that constructs each field receives the name of the field as an
    argument.

    The naming scheme follows that of 'Data.SOP.NP.cpure_NP'.
 -}
cpure'_Record :: forall c t f. KeysValuesAll (KeyValueConstraints KnownSymbol c) t => Proxy c -> (forall v. c v => String -> f v) -> Record f t
cpure'_Record _ fpure = cpara_Map (Proxy @(KeyValueConstraints KnownSymbol c)) unit go
   where
    go :: forall left k' v' right color. (KeyValueConstraints KnownSymbol c k' v', KeysValuesAll (KeyValueConstraints KnownSymbol c) left, KeysValuesAll (KeyValueConstraints KnownSymbol c) right) 
       => Record f left
       -> Record f right
       -> Record f (N color left k' v' right)
    go left right = Node left (fpure @v' (symbolVal (Proxy @k'))) right 

type F1 :: (q -> Type) -> (q -> Type) -> Map Symbol q -> Type
newtype F1 f g t = F1 { unF1 :: Record f t -> Record g t }

{- | Apply a transformation to the type constructor which wraps the fields of a 'Record', with some constraints in scope.
 
     The naming scheme follows that of 'Data.SOP.NP.cliftA_NP'.
-}
cliftA_Record :: forall c t f g. KeysValuesAll c t => Proxy c -> (forall k v. c k v => f v -> g v) -> Record f t -> Record g t
cliftA_Record _ func = unF1 $ cpara_Map (Proxy @c) (F1 $ \_ -> unit) go
    where
    go :: forall left k' v' right color. (c k' v', KeysValuesAll c left, KeysValuesAll c right) 
       => F1 f g left
       -> F1 f g right
       -> F1 f g (N color left k' v' right)
    go (F1 leftf) (F1 rightf) = F1 (\(Node left v right) -> Node (leftf left) (func @k' @v' v) (rightf right))

type F2 :: (q -> Type) -> (q -> Type) -> (q -> Type) -> Map Symbol q -> Type
newtype F2 f g h t = F2 { unF2 :: Record f t -> Record g t -> Record h t }

{- | 
     The naming scheme follows that of 'Data.SOP.NP.cliftA2_NP'.
-}
cliftA2_Record :: forall c t f g h. KeysValuesAll c t => Proxy c -> (forall k v. c k v => f v -> g v -> h v) -> Record f t -> Record g t -> Record h t
cliftA2_Record _ func = unF2 $ cpara_Map (Proxy @c) (F2 $ \_ _ -> unit) go
    where
    go :: forall left k' v' right color. (c k' v', KeysValuesAll c left, KeysValuesAll c right) 
       => F2 f g h left
       -> F2 f g h right
       -> F2 f g h (N color left k' v' right)
    go (F2 leftf) (F2 rightf) = F2 (\(Node left1 v1 right1) (Node left2 v2 right2) -> Node (leftf left1 left2) (func @k' @v' v1 v2) (rightf right1 right2))

{- | Create a 'Record' containing the names of each field. 
    
     The names are represented by a constant functor 'K' carrying an annotation
     of type 'String'. This means that there aren't actually any values of the
     type that corresponds to each field, only the 'String' annotations.

>>> putStrLn $ prettyShow_Record show $ demoteKeys @(FromList [ '("foo",Char), '("bar",Bool) ])
{bar = K "bar", foo = K "foo"}

     For computations involving field names, sometimes 'cpure'_Record' is a better option.

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
type KnownKey :: Symbol -> q -> Constraint
class KnownSymbol k => KnownKey (k :: Symbol) (v :: q)
instance KnownSymbol k => KnownKey k v 


{- | 
  Create a record containing the names of each field along with a term-level
  representation of each type.

>>> putStrLn $ prettyShow_Record show $ demoteEntries @(FromList [ '("foo",Char), '("bar",Bool) ])
{bar = K ("bar",Bool), foo = K ("foo",Char)}

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
type KnownKeyTypeableValue :: Symbol -> q -> Constraint
class (KnownSymbol k, Typeable v) => KnownKeyTypeableValue (k :: Symbol) (v :: q)
instance (KnownSymbol k, Typeable v) => KnownKeyTypeableValue k v 

{- |
  Lifts two one-place constraints (one for keys, one for values) to a two-place constraint. Useful with function like 'cpure_Record'.

  Defined using the "class synonym" <https://www.reddit.com/r/haskell/comments/ab8ypl/monthly_hask_anything_january_2019/edk1ot3/ trick>.
-}
type KeyValueConstraints :: (Symbol -> Constraint) -> (q -> Constraint) -> Symbol -> q -> Constraint
class (kc k, vc v) => KeyValueConstraints (kc :: Symbol -> Constraint) (vc :: q -> Constraint) (k :: Symbol) (v :: q)
instance (kc k, vc v) => KeyValueConstraints kc vc k v

{- |
  Lifts a one-place constraint for values to a two-place constraint. Useful with function like 'cpure_Record'.

  Defined using the "class synonym" <https://www.reddit.com/r/haskell/comments/ab8ypl/monthly_hask_anything_january_2019/edk1ot3/ trick>.
-}
type ValueConstraint :: (q -> Constraint) -> Symbol -> q -> Constraint
class (vc v) => ValueConstraint (vc :: q -> Constraint) (k :: Symbol) (v :: q)
instance (vc v) => ValueConstraint vc k v

--
--

{- | An extensible product-like type with named fields.
 
     The values in the 'Record' come wrapped in a type constructor @f@, which
     for pure records will be the identity functor 'I'.

     See also 'insert', 'delete' and 'project'.
-}
type Record :: (q -> Type) -> Map Symbol q -> Type
data Record (f :: q -> Type) (t :: Map Symbol q) where
    Empty :: Record f E 
    Node  :: Record f left -> f v -> Record f right -> Record f (N color left k v right)

instance (Productlike '[] t result, Show (NP f result)) => Show (Record f t) where
    show x = "fromNP (" ++ show (toNP x) ++ ")"

instance ToRecord (Record I (t :: Map Symbol Type)) where
    type RecordCode (Record I t)  = t
    toRecord = id

instance FromRecord (Record I (t :: Map Symbol Type)) where
    fromRecord = id

{-# DEPRECATED collapse_Record "Use collapse'_Record" #-}
collapse_Record :: forall t result a. (Productlike '[] t result) => Record (K a) t -> [a]
collapse_Record = collapse_NP . toNP


{- | Show a 'Record' in a friendlier way than the default 'Show' instance. The
     function argument will usually be 'show', but it can be used to unwrap the
     value of each field before showing it.
-}
prettyShow_Record :: forall t f. (Maplike t, KeysValuesAll (KeyValueConstraints KnownSymbol Show) t) 
                  => (forall x. Show x => f x -> String) 
                  -> Record f t 
                  -> String
prettyShow_Record showf r = 
    let showfs = cpure'_Record (Proxy @Show) $ \fieldName -> Comp (fieldName, Case  showf)
        entries = liftA2_Record (\(Comp (fieldName,Case f)) fv -> K [ fieldName ++ " = " ++ f fv ]) showfs r
     in "{" ++ mconcat (intersperse ", " (collapse'_Record entries)) ++ "}"


{- | Like 'prettyShow_Record' but specialized to pure records.
-}
prettyShow_RecordI :: forall t. (Maplike t, KeysValuesAll (KeyValueConstraints KnownSymbol Show) t) => Record I t -> String
prettyShow_RecordI r = prettyShow_Record (show . unI) r 


{-# DEPRECATED prettyShowRecord "Use prettyShow_Record" #-}
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


{-# DEPRECATED prettyShowRecordI "Use prettyShow_RecordI" #-}
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
type Variant :: (q -> Type) -> Map Symbol q -> Type
data Variant (f :: q -> Type) (t :: Map Symbol q)  where
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
prettyShow_Variant :: forall t flat f. (Maplike t, KeysValuesAll (KeyValueConstraints KnownSymbol Show) t)
                   => (forall x. Show x => f x -> String) 
                   -> Variant f t 
                   -> String
prettyShow_Variant showf v = 
    let showfs = cpure'_Record (Proxy @Show) $ \fieldName -> Comp (fieldName, Case showf)
        entries = liftA2_Variant (\(Comp (fieldName,Case f)) fv -> K (fieldName ++ " (" ++ f fv ++ ")")) showfs v
     in collapse_Variant entries

{- | Like 'prettyShow_Variant' but specialized to pure variants.
-}
prettyShow_VariantI :: forall t flat. (Maplike t, KeysValuesAll (KeyValueConstraints KnownSymbol Show) t)
                    => Variant I t -> String
prettyShow_VariantI v = prettyShow_Variant (show . unI) v 


{-# DEPRECATED prettyShowVariant "Use prettyShow_Variant" #-}
prettyShowVariant :: forall t flat f. (KeysValuesAll KnownKey t,Productlike '[] t flat, Sumlike '[] t flat, All Show flat, SListI flat)
                  => (forall x. Show x => f x -> String) 
                  -> Variant f t 
                  -> String
prettyShowVariant showf v = 
    let keysflat = toNP @t (demoteKeys @t)
        eliminators = cliftA_NP (Proxy @Show) (\(K k) -> Fn (\fv -> (K (k ++ " (" ++ showf fv ++ ")")))) keysflat
        valuesflat = toNS @t v
     in collapse_NS (ap_NS eliminators valuesflat)

{-# DEPRECATED prettyShowVariantI "Use prettyShow_VariantI" #-}
prettyShowVariantI :: forall t flat. (KeysValuesAll KnownKey t,Productlike '[] t flat, Sumlike '[] t flat, All Show flat, SListI flat) 
                   => Variant I t -> String
prettyShowVariantI v = prettyShowVariant (show . unI) v 

--
--
-- Insertion

{- | Insert a list of type level key / value pairs into a type-level map. 
-}
type InsertAll :: [(Symbol,q)] -> Map Symbol q -> Map Symbol q
type family InsertAll (es :: [(Symbol,q)]) (t :: Map Symbol q) :: Map Symbol q where
    InsertAll '[] t = t
    InsertAll ( '(name,fieldType) ': es ) t = Insert name fieldType (InsertAll es t)

{- | Build a type-level map out of a list of type level key / value pairs. 
-}
type FromList (es :: [(Symbol,q)]) = InsertAll es Empty


{- |
     Adds a new field to a 'Record'.

>>> project @"foo" (insert @"foo" (I 'a') unit)
I 'a'

>>> project @"foo" (insert @"foo" @Char Nothing unit)
Nothing

 -}
insert :: forall k v t f. Insertable k v t => f v -> Record f t -> Record f (Insert k v t)
insert = _insert @_ @k @v @t @f

{- |
     Lets you use a 'Variant' in a bigger context
     than the one in which is was defined. 
 -}
widen :: forall k v t f. Insertable k v t => Variant f t -> Variant f (Insert k v t)
widen = _widen @_ @k @v @t @f

{- | Alias for 'insert'. 
-}
addField :: forall k v t f. Insertable k v t => f v -> Record f t -> Record f (Insert k v t)
addField = insert @k @v @t @f

{- | Like 'insert' but specialized to pure 'Record's.
 
>>> projectI @"foo" (insertI @"foo" 'a' unit)
'a'

-}
insertI :: forall k v t . Insertable k v t => v -> Record I t -> Record I (Insert k v t)
insertI = insert @k @v @t . I

{- | Like 'addField' but specialized to pure 'Record's.
-}
addFieldI :: forall k v t . Insertable k v t => v -> Record I t -> Record I (Insert k v t)
addFieldI = insertI @k @v @t

{- | Class that determines if the pair of a 'Symbol' key and a type can
     be inserted into a type-level map.
 
     The associated type family 'Insert' produces the resulting map.

     At the term level, this manifests in 'insert', which adds a new field to a
     record, and in 'widen', which lets you use a 'Variant' in a bigger context
     than the one in which is was defined. 'insert' tends to be more useful in
     practice.

     If the map already has the key but with a /different/ type, the
     insertion fails to compile.
 -}
type Insertable :: Symbol -> q -> Map Symbol q -> Constraint
class Insertable (k :: Symbol) (v :: q) (t :: Map Symbol q) where
    type Insert k v t :: Map Symbol q
    _insert :: f v -> Record f t -> Record f (Insert k v t)
    _widen :: Variant f t -> Variant f (Insert k v t)

-- insert x s =
--  T B a z b
--  where
--  T _ a z b = ins s
instance (InsertableHelper1 k v t, Insert1 k v t ~ inserted, CanMakeBlack inserted) => Insertable k v t where
    type Insert k v t = MakeBlack (Insert1 k v t)
    _insert fv r = makeBlackR @_ (insert1 @_ @k @v fv r) 
    _widen v = makeBlackV @_ (widen1 @_ @k @v v)

class CanMakeBlack (t :: Map Symbol q) where
    type MakeBlack t :: Map Symbol q
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

-- for some reason, removing the "inline" kind signatures causes a compilation error
type InsertableHelper1 :: Symbol -> q -> Map Symbol q -> Constraint
class InsertableHelper1 (k :: Symbol) 
                        (v :: q) 
                        (t :: Map Symbol q) where
    type Insert1 k v t :: Map Symbol q 
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
    insert1 = insert2 @_ @ordering @k @v @color @left @k' @v' @right
    widen1  = widen2 @_ @ordering @k @v @color @left @k' @v' @right

class InsertableHelper2 (ordering :: Ordering) 
                        (k :: Symbol) 
                        (v :: q) 
                        (color :: Color) 
                        (left :: Map Symbol q) 
                        (k' :: Symbol) 
                        (v' :: q) 
                        (right :: Map Symbol q) where
    type Insert2 ordering k v color left k' v' right :: Map Symbol q 
    insert2 :: f v -> Record f (N color left k' v' right) -> Record f (Insert2 ordering k v color left k' v' right)
    widen2 :: Variant f (N color left k' v' right) -> Variant f (Insert2 ordering k v color left k' v' right)

--  ins s@(T B a y b)
--      | x<y = balance (ins a) y b
instance (InsertableHelper1 k v left, Insert1 k v left ~ inserted,
          Balanceable inserted k' v' right 
         )
         => InsertableHelper2 LT k v B left k' v' right where
    type Insert2              LT k v B left k' v' right = Balance (Insert1 k v left) k' v' right
    insert2 fv (Node left fv' right) = balanceR @_ @_ @k' @v' @right (Node (insert1 @_ @k @v fv left) fv' right) 
    widen2 v = balanceV @_ @(Insert1 k v left) @k' @v' @right $ case v of
        Here x -> Here x
        LookLeft x -> LookLeft (widen1 @_ @k @v x)
        LookRight x -> LookRight x

--  ins s@(T B a y b)
--      | x<y = balance (ins a) y b
instance (InsertableHelper1 k v left, Insert1 k v left ~ inserted,
          Balanceable inserted k' v' right
         )
         => InsertableHelper2 LT k v R left k' v' right where
    type Insert2              LT k v R left k' v' right = N R (Insert1 k v left) k' v' right
    insert2 fv (Node left fv' right) = Node (insert1 @_ @k @v fv left) fv' right 
    widen2 v = case v of
        Here x -> Here x
        LookLeft x -> LookLeft (widen1 @_ @k @v x)
        LookRight x -> LookRight x


-- This instance implies that we can't change the type associated to an
-- existing key. If we did that, we wouldn't be able to widen Variants that
-- happen to match that key!
instance InsertableHelper2 EQ k v color left k v right where
    type Insert2           EQ k v color left k v right = N color left k v right
    insert2 fv (Node left _ right) = Node left fv right
    widen2 = id

--  ins s@(T B a y b)
--      | ...
--      | x>y = balance a y (ins b)
instance (InsertableHelper1 k v right, Insert1 k v right ~ inserted,
          Balanceable left  k' v' inserted
         )
         => InsertableHelper2 GT k v B left k' v' right where
    type Insert2              GT k v B left k' v' right = Balance left  k' v' (Insert1 k v right)
    insert2 fv (Node left fv' right) = balanceR @_ @left @k' @v' @_ (Node left  fv' (insert1 @_ @k @v fv right)) 
    widen2 v = balanceV @_ @left @k' @v' @(Insert1 k v right) $ case v of
        Here x -> Here x
        LookLeft x -> LookLeft x
        LookRight x -> LookRight (widen1 @_ @k @v x)

--  ins s@(T R a y b)
--      | ...
--      | x>y = T R a y (ins b)
instance (InsertableHelper1 k v right, Insert1 k v right ~ inserted,
          Balanceable left  k' v' inserted
         )
         => InsertableHelper2 GT k v R left k' v' right where
    type Insert2              GT k v R left k' v' right = N R left k' v' (Insert1 k v right)
    insert2 fv (Node left fv' right) = Node left fv' (insert1 @_ @k @v fv right) 
    widen2 v = case v of
        Here x -> Here x
        LookLeft x -> LookLeft x
        LookRight x -> LookRight (widen1 @_ @k @v x)

data BalanceAction = BalanceSpecial
                   | BalanceLL
                   | BalanceLR
                   | BalanceRL
                   | BalanceRR
                   | DoNotBalance
                   deriving Show

type ShouldBalance :: Map k' v' -> Map k' v' -> BalanceAction
type family ShouldBalance (left :: Map k' v') (right :: Map k' v') :: BalanceAction where
    ShouldBalance (N R _ _ _ _) (N R _ _ _ _) = BalanceSpecial
    ShouldBalance (N R (N R _ _ _ _) _ _ _) _ = BalanceLL
    ShouldBalance (N R _ _ _ (N R _ _ _ _)) _ = BalanceLR
    ShouldBalance _ (N R (N R _ _ _ _) _ _ _) = BalanceRL
    ShouldBalance _ (N R _ _ _ (N R _ _ _ _)) = BalanceRR
    ShouldBalance _ _                         = DoNotBalance

class Balanceable (left :: Map Symbol q) (k :: Symbol) (v :: q) (right :: Map Symbol q) where
    type Balance left k v right :: Map Symbol q
    balanceR :: Record f (N color left k v right) -> Record f (Balance left k v right)
    balanceV :: Variant f (N color left k v right) -> Variant f (Balance left k v right)

instance (ShouldBalance left right ~ action, 
          BalanceableHelper action left k v right
         ) 
         => Balanceable left k v right where
    -- FIXME possible duplicate work with ShouldBalance: both in constraint and in associated type family. 
    -- Is that bad? How to avoid it?
    type Balance left k v right = Balance' (ShouldBalance left right) left k v right
    balanceR = balanceR' @_ @action @left @k @v @right
    balanceV = balanceV' @_ @action @left @k @v @right
    
class BalanceableHelper (action :: BalanceAction) 
                        (left :: Map Symbol q) 
                        (k :: Symbol) 
                        (v :: q) 
                        (right :: Map Symbol q) where
    type Balance' action left k v right :: Map Symbol q
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
    type Balance'          DoNotBalance a k v b = N B a k v b 
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

type family Field (f :: q -> Type) (t :: Map Symbol q) (v :: q) where
    Field f t v = Record f t -> (f v -> Record f t, f v)

{- | Auxiliary type family to avoid repetition and help improve compilation times.
 -}
type family Branch (f :: q -> Type) (t :: Map Symbol q) (v :: q) where
    Branch f t v = (Variant f t -> Maybe (f v), f v -> Variant f t)

--
{- | 
     Class that determines if a given 'Symbol' key is present in a type-level
     map.

     The 'Value' type family gives the 'Type' corresponding to the key.
-} 
class Key (k :: Symbol) (t :: Map Symbol q) where
    type Value k t :: q
    _field  :: Field  f t (Value k t)
    _branch :: Branch f t (Value k t)

{- |
     Takes a field name (given through @TypeApplications@) and a
     'Record', and returns a pair of a setter for the field and the original
     value of the field.
-}
field  :: forall k t f. Key k t => Field f t (Value k t)
field = _field @_ @k @t

{- |
     Takes a branch name (given through @TypeApplications@) and
     returns a pair of a match function and a constructor.
-}
branch :: forall k t f. Key k t => Branch f t (Value k t)
branch = _branch @_ @k @t

-- member :: Ord a => a -> RB a -> Bool
class KeyHelper (ordering :: Ordering) (k :: Symbol) (left :: Map Symbol q) (v :: q) (right :: Map Symbol q) where 
    type Value' ordering k left v right :: q
    field'  :: Field  f (N colorx left kx v right) (Value' ordering k left v right)
    branch' :: Branch f (N colorx left kx v right) (Value' ordering k left v right)

instance (CmpSymbol k' k ~ ordering, KeyHelper ordering k left v' right) => Key k (N color left k' v' right) where
    type Value k (N color left k' v' right) = Value' (CmpSymbol k' k) k left v' right
    _field = field' @_ @ordering @k @left @v' @right
    _branch = branch' @_ @ordering @k @left @v' @right

--  | x<y = member x a
instance (CmpSymbol k2 k ~ ordering, KeyHelper ordering k left2 v2 right2) 
      => KeyHelper LT k left v (N color2 left2 k2 v2 right2) where
    type Value'    LT k left v (N color2 left2 k2 v2 right2) = Value' (CmpSymbol k2 k) k left2 v2 right2
    field' (Node left fv right) = 
        let (setter,x) = field' @_ @ordering @k @left2 @v2 @right2 right
         in (\z -> Node left fv (setter z),x)
    branch' = 
        let (match,inj) = branch' @_ @ordering @k @left2 @v2 @right2 
         in (\case LookRight x -> match x
                   _ -> Nothing,
             \fv -> LookRight (inj fv))

--  | x>y = member x b
instance (CmpSymbol k2 k ~ ordering, KeyHelper ordering k left2 v2 right2) 
      => KeyHelper GT k (N color2 left2 k2 v2 right2) v' right where
    type    Value' GT k (N color2 left2 k2 v2 right2) v' right = Value' (CmpSymbol k2 k) k left2 v2 right2
    field' (Node left fv right) = 
        let (setter,x) = field' @_ @ordering @k @left2 @v2 @right2 left
         in (\z -> Node (setter z) fv right,x)
    branch' =
        let (match,inj) = branch' @_ @ordering @k @left2 @v2 @right2 
         in (\case LookLeft x -> match x
                   _ -> Nothing,
             \fv -> LookLeft (inj fv))

--  | otherwise = True
instance KeyHelper EQ k left v right where
    type Value'    EQ k left v right = v
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

>>> match @"foo" (inject @"foo" (I 'a') :: Variant I (Insert "foo" Char Empty))
Just (I 'a')

-}
inject :: forall k t f. Key k t => f (Value k t) -> Variant f t
inject = snd (branch @k @t)

{- | Check if a 'Variant' value is the given branch.
-}
match :: forall k t f. Key k t => Variant f t -> Maybe (f (Value k t))
match = fst (branch @k @t)

{- | Like 'project' but specialized to pure 'Record's.

>>> projectI @"foo" (insertI @"foo" 'a' (insertI @"bar" False unit))
'a'

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
 
>>> matchI @"foo" (injectI @"foo" 'a' :: Variant I (Insert "foo" Char Empty))
Just 'a'

-}
injectI :: forall k t. Key k t => Value k t -> Variant I t
injectI = snd (branch @k @t) . I

{- | Like 'match' but specialized to pure 'Variants's.
-}
matchI :: forall k t . Key k t => Variant I t ->  Maybe (Value k t)
matchI v = unI <$> fst (branch @k @t) v

{-# DEPRECATED eliminate "Use eliminate_Variant instead." #-}
eliminate :: (Productlike '[] t result, Sumlike '[] t result, SListI result) => Record (Case f r) t -> Variant f t -> r
eliminate cases variant = 
    let adapt (Case e) = Fn (\fv -> K (e fv))
     in collapse_NS (ap_NS (liftA_NP adapt (toNP cases)) (toNS variant)) 

{- | Process a 'Variant' using a eliminator 'Record' that carries
     handlers for each possible branch of the 'Variant'.

>>> eliminate_Variant (addCaseI @"foo" @Int succ (addCaseI @"bar" pred unit)) (injectI @"bar" 33)
32

-}
eliminate_Variant :: Maplike t => Record (Case f r) t -> Variant f t -> r
eliminate_Variant cases variant = 
    let adapt (Case f) x = K (f x) 
     in collapse_Variant $ liftA2_Variant adapt cases variant

{- | Represents a handler for a branch of a 'Variant'.  
-}
type Case :: (q -> Type) -> Type -> q -> Type
newtype Case f a b = Case { runCase :: f b -> a }

instance Functor f => Contravariant (Case f a) where
    contramap g (Case c) = Case (c . fmap g)

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
type SetField :: (q -> Type) -> Type -> q -> Type
newtype SetField f a b = SetField { getSetField :: f b -> a -> a }
 
{- | For a given 'Map', produces a two-place constraint confirming the presence
     of a entry.
     
     Defined using the "class synonym" <https://www.reddit.com/r/haskell/comments/ab8ypl/monthly_hask_anything_january_2019/edk1ot3/ trick>.
-}
type PresentIn :: Map Symbol q -> Symbol -> q -> Constraint
class (Key k t, Value k t ~ v) => PresentIn (t :: Map Symbol q) (k :: Symbol) (v :: q) 
instance (Key k t, Value k t ~ v) => PresentIn (t :: Map Symbol q) (k :: Symbol) (v :: q)

{-# DEPRECATED ProductlikeSubset "This constraint is obsolete" #-}
type ProductlikeSubset (subset :: Map Symbol q) (whole :: Map Symbol q) (flat :: [q]) = 
                       (KeysValuesAll (PresentIn whole) subset,
                       Productlike '[] subset flat,
                       SListI flat)

{-# DEPRECATED fieldSubset "Use Data.RBR.Subset.fieldSubset" #-}
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

{-# DEPRECATED projectSubset "Use Data.RBR.Subset.projectSubset" #-}
projectSubset :: forall subset whole flat f. (ProductlikeSubset subset whole flat) 
              => Record f whole 
              -> Record f subset
projectSubset =  snd . fieldSubset

{-# DEPRECATED getFieldSubset "Use Data.RBR.Subset.getFieldSubset" #-}
getFieldSubset :: forall subset whole flat f. (ProductlikeSubset subset whole flat)  
               => Record f whole 
               -> Record f subset
getFieldSubset = projectSubset

{-# DEPRECATED setFieldSubset "Use Data.RBR.Subset.setFieldSubset" #-}
setFieldSubset :: forall subset whole flat f.  (ProductlikeSubset subset whole flat) 
               => Record f subset
               -> Record f whole 
               -> Record f whole
setFieldSubset subset whole = fst (fieldSubset whole) subset 

{-# DEPRECATED modifyFieldSubset "Use Data.RBR.Subset.modifyFieldSubset" #-}
modifyFieldSubset :: forall subset whole flat f.  (ProductlikeSubset subset whole flat) 
                  => (Record f subset -> Record f subset)
                  -> Record f whole 
                  -> Record f whole
modifyFieldSubset f r = uncurry ($) (fmap f (fieldSubset @subset @whole r))


{-# DEPRECATED SumlikeSubset "This constraint is obsolete" #-}
type SumlikeSubset (subset :: Map Symbol q) (whole :: Map Symbol q) (subflat :: [q]) (wholeflat :: [q]) = 
                   (KeysValuesAll (PresentIn whole) subset,
                    Productlike '[] whole  wholeflat,
                    Sumlike '[] whole  wholeflat,
                    SListI wholeflat,
                    Productlike '[] subset subflat,
                    Sumlike '[] subset subflat,
                    SListI subflat)

{-# DEPRECATED branchSubset "Use Data.RBR.Subset.branchSubset" #-}
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


{-# DEPRECATED injectSubset  "Use Data.RBR.Subset.injectSubset" #-}
injectSubset :: forall subset whole subflat wholeflat f. (SumlikeSubset subset whole subflat wholeflat)
             => Variant f subset -> Variant f whole
injectSubset = snd (branchSubset @subset @whole @subflat @wholeflat)

{-# DEPRECATED matchSubset  "Use Data.RBR.Subset.matchSubset" #-}
matchSubset :: forall subset whole subflat wholeflat f. (SumlikeSubset subset whole subflat wholeflat)
            => Variant f whole -> Maybe (Variant f subset)
matchSubset = fst (branchSubset @subset @whole @subflat @wholeflat)

{-# DEPRECATED eliminateSubset  "Use Data.RBR.Subset.eliminateSubset" #-}
eliminateSubset :: forall subset whole subflat wholeflat f r. (SumlikeSubset subset whole subflat wholeflat)
                => Record (Case f r) whole -> Variant f subset -> r
eliminateSubset cases = 
    let reducedCases = getFieldSubset @subset @whole cases
     in eliminate reducedCases 

--
-- Interaction with Data.SOP

{- | Class from converting 'Record's to and from the n-ary product type 'NP' from "Data.SOP".
    
     'prefixNP' flattens a 'Record' and adds it to the initial part of the product.

     'breakNP' reconstructs a 'Record' from the initial part of the product and returns the unconsumed part.

     The functions 'toNP' and 'fromNP' are usually easier to use. 
-}
type Productlike :: [k] -> Map Symbol k -> [k] -> Constraint
class Productlike (start :: [k])
                  (t :: Map Symbol k) 
                  (result :: [k]) | start t -> result, result t -> start where
    _prefixNP:: Record f t -> NP f start -> NP f result
    _breakNP :: NP f result -> (Record f t, NP f start)

instance Productlike start E start where
    _prefixNP _ start = start  
    _breakNP start = (Empty, start) 

instance (Productlike start right middle, 
          Productlike (v ': middle) left result)
          => Productlike start (N color left k v right) result where
    _prefixNP (Node left fv right) start = 
        _prefixNP @_ @_ @left @result left (fv :* prefixNP @start @right @middle right start)
    _breakNP result =
        let (left, fv :* middle) = _breakNP @_ @_ @left @result result
            (right, start) = _breakNP @_ @start @right middle
         in (Node left fv right, start)

{- | 
     Flattens a 'Record' and adds it to the initial part of the product.
-}
prefixNP:: forall start t result f. Productlike start t result => Record f t -> NP f start -> NP f result
prefixNP = _prefixNP @_ @start @t @result

{- | 
     Reconstructs a 'Record' from the initial part of the product and returns the unconsumed part.
-}
breakNP :: forall start t result f. Productlike start t result => NP f result -> (Record f t, NP f start)
breakNP = _breakNP @_ @start @t @result

{- | Convert a 'Record' into a n-ary product. The order of the elements in the
     product is not the order of insertion in the record.

>>> toNP (insertI @"foo" 'a' (insertI @"bar" True unit))
I True :* I 'a' :* Nil 

-}
toNP :: forall t result f. Productlike '[] t result => Record f t -> NP f result
toNP r = prefixNP r Nil

{- | Convert a n-ary product into a compatible 'Record'. Usually follows an invocation of 'toNP'. 


>>> :{ 
    prettyShow_RecordI $ 
    fromNP @(Insert "foo" _ (Insert "bar" _ Empty)) $
    toNP $ 
    insertI @"foo" 'a' $
    insertI @"bar" True $
    unit
:}
"{bar = True, foo = 'a'}"

-}
fromNP :: forall t result f. Productlike '[] t result => NP f result -> Record f t
fromNP np = let (r,Nil) = breakNP np in r

{- | Class from converting 'Variant's to and from the n-ary sum type 'NS' from "Data.SOP".
    
     'prefixNS' flattens a 'Variant' and adds it to the initial part of the sum.

     'breakNS' reconstructs a 'Variant' from the initial part of the sum and returns the unconsumed part.

     The functions 'toNS' and 'fromNS' are usually easier to use. 
-}
type Sumlike :: [k] -> Map Symbol k -> [k] -> Constraint
class Sumlike (start :: [k]) 
              (t :: Map Symbol k) 
              (result :: [k]) | start t -> result, result t -> start where
    _prefixNS :: Either (NS f start) (Variant f t) -> NS f result
    _breakNS :: NS f result -> Either (NS f start) (Variant f t)

instance Sumlike start 
                  (N color E k v E)
                  (v ': start) where
    _prefixNS = \case
        Left  l -> S l
        Right x -> case x of Here fv -> Z @_ @v @start fv
    _breakNS = \case 
        Z x -> Right (Here x)
        S x -> Left x

instance (Sumlike start (N colorR leftR kR vR rightR) middle,
          Sumlike (v ': middle) (N colorL leftL kL vL rightL) result)
         => Sumlike start 
                    (N color (N colorL leftL kL vL rightL) k v (N colorR leftR kR vR rightR)) 
                    result where
    _prefixNS = \case
        Left x -> 
            _prefixNS @_ @_ @(N colorL leftL kL vL rightL) (Left (S (_prefixNS @_ @_ @(N colorR leftR kR vR rightR) (Left x))))
        Right x -> 
            case x of LookLeft x  -> _prefixNS @_ @(v ': middle) @(N colorL leftL kL vL rightL) @result (Right x) 
                      Here x      -> _prefixNS @_ @_ @(N colorL leftL kL vL rightL) (Left (Z x))
                      LookRight x -> _prefixNS @_ @_ @(N colorL leftL kL vL rightL) (Left (S (_prefixNS @_ (Right x))))
    _breakNS ns = case _breakNS @_ @(v ': middle) @(N colorL leftL kL vL rightL) ns of
        Left x -> case x of
            Z x -> Right (Here x)
            S x -> case _breakNS @_ @start @(N colorR leftR kR vR rightR) x of
                Left ns  -> Left ns
                Right v  -> Right (LookRight v)
        Right v -> Right (LookLeft v)

instance Sumlike (v ': start) (N colorL leftL kL vL rightL) result
         => Sumlike start (N color (N colorL leftL kL vL rightL) k v E) result where
    _prefixNS = \case
        Left x  -> 
            _prefixNS @_ @_ @(N colorL leftL kL vL rightL) (Left (S x))
        Right x -> 
            case x of LookLeft x  -> _prefixNS @_ @(v ': start) @(N colorL leftL kL vL rightL) @result (Right x)
                      Here x      -> _prefixNS @_ @_ @(N colorL leftL kL vL rightL) (Left (Z x))
    _breakNS ns = case _breakNS @_ @(v ': start) @(N colorL leftL kL vL rightL) ns of
        Left x -> case x of
            Z x -> Right (Here x)
            S x -> Left x 
        Right v -> Right (LookLeft v)

instance Sumlike start (N colorR leftR kR vR rightR) middle
         => Sumlike start (N color E k v (N colorR leftR kR vR rightR)) (v ': middle) where
    _prefixNS = \case
        Left x  -> S (_prefixNS @_ @_ @(N colorR leftR kR vR rightR) (Left x))
        Right x -> 
            case x of Here x      -> Z x
                      LookRight x -> S (_prefixNS @_ @_ @(N colorR leftR kR vR rightR) (Right x))
    _breakNS = \case 
        Z x -> Right (Here x)
        S x -> case _breakNS @_ @_ @(N colorR leftR kR vR rightR) x of
            Left  ns     -> Left ns
            Right v      -> Right (LookRight v)

{- | 
    
     Flattens a 'Variant' and adds it to the initial part of the sum.
-}
prefixNS :: forall start t result f. Sumlike start t result => Either (NS f start) (Variant f t) -> NS f result 
prefixNS = _prefixNS @_ @start @t @result

{- | 
     Reconstructs a 'Variant' from the initial part of the sum and returns the unconsumed part.
-}
breakNS :: forall start t result f. Sumlike start t result => NS f result -> Either (NS f start) (Variant f t)
breakNS = _breakNS @_ @start @t @result

{- | Convert a 'Variant' into a n-ary sum. 
 
>>> toNS (injectI @"foo" 'a' :: Variant I (Insert "foo" Char (Insert "bar" Bool Empty)))
S (Z (I 'a')) 

-}
toNS :: forall t result f. Sumlike '[] t result => Variant f t -> NS f result
toNS = prefixNS . Right

{- | Convert a n-ary sum into a compatible 'Variant'. 
 
>>> :{ 
    prettyShow_VariantI $ 
    fromNS @(FromList [ '("foo",_), '("bar",_) ]) $ 
    toNS $ 
    (injectI @"foo" 'a' :: Variant I (FromList [ '("foo",Char), '("bar",Bool) ]))
:}
"foo ('a')"

-}
fromNS :: forall t result f. Sumlike '[] t result => NS f result -> Variant f t
fromNS ns = case breakNS ns of 
    Left _ -> error "this never happens"
    Right x -> x

--
--
-- Interfacing with normal records
type ToRecord :: Type -> Constraint
class ToRecord (r :: Type) where
    type RecordCode r :: Map Symbol Type
    -- https://stackoverflow.com/questions/22087549/defaultsignatures-and-associated-type-families/22088808
    type RecordCode r = RecordCode' E (G.Rep r)
    toRecord :: r -> Record I (RecordCode r)
    default toRecord :: (G.Generic r,ToRecordHelper E (G.Rep r),RecordCode r ~ RecordCode' E (G.Rep r)) => r -> Record I (RecordCode r)
    toRecord r = toRecord' unit (G.from r)

instance (
    G.Generic r,
    ToRecordHelper E (G.Rep r)
    ) =>
    ToRecord (Generically (r :: Type)) where
    type RecordCode (Generically (r :: Type)) = RecordCode' E (G.Rep r)
    toRecord (Generically r) = toRecord' unit (G.from r)

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
type FromRecord :: Type -> Constraint
class ToRecord r => FromRecord (r :: Type) where
    fromRecord :: Record I (RecordCode r) -> r
    default fromRecord :: (G.Generic r, FromRecordHelper (RecordCode r) (G.Rep r)) => Record I (RecordCode r) -> r
    fromRecord r = G.to (fromRecord' @(RecordCode r) @(G.Rep r) r)

{- |
     The naming scheme follows that of 'Generics.SOP.IsProductType'.
 -}
type IsRecordType :: Type -> Map Symbol Type -> Constraint
type IsRecordType (r :: Type) (t :: Map Symbol Type) = (G.Generic r, ToRecord r, RecordCode r ~ t, FromRecord r)

-- {- |
--     A version of 'fromRecord' which accepts 'Record' values with more fields than the target nominal record, and possibly in an incompatible order.
--  -}
-- fromRecordSuperset :: forall r subset whole flat. (FromRecord r, RecordCode r ~ subset, ProductlikeSubset subset whole flat) => Record I whole -> r
-- fromRecordSuperset = fromRecord @r . projectSubset @subset @whole @flat

type FromRecordHelper :: Map Symbol Type -> (Type -> Type) -> Constraint
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
type VariantCode :: Type -> Map Symbol Type
type family VariantCode (s :: Type) :: Map Symbol Type where
    VariantCode s = VariantCode' E (G.Rep s)

type VariantCode' :: Map Symbol Type -> (Type -> Type) -> Map Symbol Type
type family VariantCode' (acc :: Map Symbol Type) (g :: Type -> Type) :: Map Symbol Type where
    VariantCode' acc (D1 meta fields) = VariantCode' acc fields
    VariantCode' acc (t1 G.:+: t2) = VariantCode' (VariantCode' acc t2) t1
    VariantCode' acc (C1 (G.MetaCons k _ _) (S1 ('G.MetaSel Nothing unpackedness strictness laziness) (Rec0 v))) = Insert k v acc
    VariantCode' acc (C1 (G.MetaCons k _ _) G.U1) = Insert k () acc
     
type FromVariant :: Type -> Constraint     
class FromVariant (s :: Type) where
    fromVariant :: Variant I (VariantCode s) -> s
    default fromVariant :: (G.Generic s, FromVariantHelper (VariantCode s) (G.Rep s)) => Variant I (VariantCode s) -> s
    fromVariant v = case fromVariant' @(VariantCode s) v of
        Just x -> G.to x
        Nothing -> error "fromVariant match fail. Should not happen."

{- |
     The naming scheme follows that of 'Generics.SOP.IsProductType'.
 -}
type IsVariantType :: Type -> Map Symbol Type -> Constraint
type IsVariantType (v :: Type) (t :: Map Symbol Type) = (G.Generic v, ToVariant v, VariantCode v ~ t, FromVariant v)

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

instance (Key k t, Value k t ~ ()) 
         => FromVariantHelper t (C1 (G.MetaCons k x y) G.U1)
  where
    fromVariant' v = case matchI @k @t v of
        Just x -> Just (M1 G.U1)
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
type ToVariant :: Type -> Constraint
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

instance (Key k t, Value k t ~ ()) =>
    ToVariantHelper t (C1 (G.MetaCons k x y) G.U1) where
    toVariant' (M1 G.U1) = injectI @k ()

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
type DiscriminateBalL :: Map k v -> Map k v -> Bool 
type family DiscriminateBalL (l :: Map k v) (r :: Map k v) :: Bool where
    DiscriminateBalL (N R _ _ _ _) _ = False
    DiscriminateBalL _             _ = True

type BalanceableL :: Map Symbol q -> Symbol -> q -> Map Symbol q -> Constraint
class BalanceableL (l :: Map Symbol q) (k :: Symbol) (v :: q) (r :: Map Symbol q) where
    type BalL l k v r :: Map Symbol q
    balLR :: Record f (N color l k v r) -> Record f (BalL l k v r)
    balLV :: Variant f (N color l k v r) -> Variant f (BalL l k v r)

type BalanceableHelperL :: Bool -> Map Symbol q -> Symbol -> q -> Map Symbol q -> Constraint
class BalanceableHelperL (b :: Bool) (l :: Map Symbol q) (k :: Symbol) (v :: q) (r :: Map Symbol q) where
    type BalL' b l k v r :: Map Symbol q
    balLR' :: Record f (N color l k v r) -> Record f (BalL' b l k v r)
    balLV' :: Variant f (N color l k v r) -> Variant f (BalL' b l k v r)

instance (DiscriminateBalL l r ~ b, BalanceableHelperL b l k v r) => BalanceableL l k v r where
    type BalL l k v r = BalL' (DiscriminateBalL l r) l k v r
    balLR = balLR' @_ @b @l @k @v @r
    balLV = balLV' @_ @b @l @k @v @r

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
instance (N R t2 z zv t3 ~ g, BalanceableHelper (ShouldBalance t1 g) t1 y yv g) => 
    BalanceableHelperL True t1 y yv (N B t2 z zv t3) where
    type BalL'         True t1 y yv (N B t2 z zv t3)     
                 =  Balance t1 y yv (N R t2 z zv t3)
    balLR' (Node left1 v1 (Node left2 v2 right2)) = 
        balanceR @_ @t1 @y @yv @(N R t2 z zv t3) (Node left1 v1 (Node left2 v2 right2))
    balLV' v = balanceV @_ @t1 @y @yv @(N R t2 z zv t3) (case v of
        LookLeft l -> LookLeft l
        Here x -> Here x
        LookRight r -> LookRight (case r of
                            LookLeft l' -> LookLeft l'
                            Here x' -> Here x'
                            LookRight r' -> LookRight r'))

-- balleft bl x (T R (T B a y b) z c) = T R (T B bl x a) y (balance b z (sub1 c))
instance (N R l k kv r ~ g, BalanceableHelper    (ShouldBalance t3 g) t3 z zv g) => 
    BalanceableHelperL True t1 y yv (N R (N B t2 u uv t3) z zv (N B l k kv r)) where
    type BalL'         True t1 y yv (N R (N B t2 u uv t3) z zv (N B l k kv r)) =
                             N R (N B t1 y yv t2) u uv (Balance t3 z zv (N R l k kv r))          
    balLR' (Node left1 v1 (Node (Node left2 v2 right2) vx (Node left3 v3 right3))) = 
            Node (Node left1 v1 left2) v2 (balanceR @_ @t3 @z @zv @(N R l k kv r) (Node right2 vx (Node left3 v3 right3)))
    balLV' v = case v of LookLeft left1                          -> LookLeft (LookLeft left1)
                         Here v1                                 -> LookLeft (Here v1)
                         LookRight (LookLeft (LookLeft left2))   -> LookLeft (LookRight left2)
                         LookRight (LookLeft (Here v2))          -> Here v2
                         LookRight (LookLeft (LookRight right2)) -> LookRight (balanceV @_ @t3 @z @zv @(N R l k kv r) (LookLeft right2))
                         LookRight (Here vx)                     -> LookRight (balanceV @_ @t3 @z @zv @(N R l k kv r) (Here vx))
                         LookRight (LookRight rr)                -> LookRight (balanceV @_ @t3 @z @zv @(N R l k kv r) (LookRight (case rr of
                                                                        LookLeft left3 -> LookLeft left3
                                                                        Here v3 -> Here v3
                                                                        LookRight right3 -> LookRight right3)))


-- balright :: RB a -> a -> RB a -> RB a
-- balright a x (T R b y c) = T R a x (T B b y c)
-- balright (T B a x b) y bl = balance (T R a x b) y bl
-- balright (T R a x (T B b y c)) z bl = T R (balance (sub1 a) x b) y (T B c z bl)
type DiscriminateBalR :: Map k v -> Map k v -> Bool
type family DiscriminateBalR (l :: Map k v) (r :: Map k v) :: Bool where
    DiscriminateBalR _ (N R _ _ _ _) = False
    DiscriminateBalR _ _             = True


type BalanceableR :: Map Symbol q -> Symbol -> q -> Map Symbol q -> Constraint
class BalanceableR (l :: Map Symbol q) (k :: Symbol) (v :: q) (r :: Map Symbol q) where
    type BalR l k v r :: Map Symbol q
    balRR :: Record f (N color l k v r) -> Record f (BalR l k v r)
    balRV :: Variant f (N color l k v r) -> Variant f (BalR l k v r)

type BalanceableHelperR :: Bool -> Map Symbol q -> Symbol -> q -> Map Symbol q -> Constraint
class BalanceableHelperR (b :: Bool) (l :: Map Symbol q) (k :: Symbol) (v :: q) (r :: Map Symbol q) where
    type BalR' b l k v r :: Map Symbol q
    balRR' :: Record f (N color l k v r) -> Record f (BalR' b l k v r)
    balRV' :: Variant f (N color l k v r) -> Variant f (BalR' b l k v r)

instance (DiscriminateBalR l r ~ b, BalanceableHelperR b l k v r) => BalanceableR l k v r where
    type BalR l k v r = BalR' (DiscriminateBalR l r) l k v r
    balRR = balRR' @_ @b @l @k @v @r
    balRV = balRV' @_ @b @l @k @v @r

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
instance (N R t2 z zv t3 ~ g, ShouldBalance g t1 ~ shouldbalance, BalanceableHelper shouldbalance g y yv t1) => 
    BalanceableHelperR True (N B t2 z zv t3) y yv t1 where
    type BalR'         True (N B t2 z zv t3) y yv t1     
             =  Balance (N R t2 z zv t3) y yv t1
    balRR' (Node (Node left1 v1 right1) v2 right2) = balanceR @_ @(N R t2 z zv t3) @y @yv @t1 
           (Node (Node left1 v1 right1) v2 right2)
    balRV' v = balanceV @_ @(N R t2 z zv t3) @y @yv @t1 (case v of
        LookLeft l -> LookLeft (case l of 
            LookLeft l' -> LookLeft l'
            Here x' -> Here x'
            LookRight r' -> LookRight r')
        Here x -> Here x
        LookRight r -> LookRight r)

-- balright (T R a x (T B b y c)) z bl = T R (balance (sub1 a) x b) y (T B c z bl)
instance (N R t2 u uv t3 ~ g, ShouldBalance g l ~ shouldbalance, BalanceableHelper shouldbalance g z zv l) => 
    BalanceableHelperR True (N R (N B t2 u uv t3) z zv (N B l k kv r)) y yv t1 where
    type BalR'         True (N R (N B t2 u uv t3) z zv (N B l k kv r)) y yv t1 =
                             N R (Balance (N R t2 u uv t3) z zv l) k kv (N B r y yv t1) 
    balRR' (Node (Node (Node left2 v2 right2) vx (Node left3 v3 right3)) v1 left1) = 
            Node (balanceR @_ @(N R t2 u uv t3) @z @zv @l (Node (Node left2 v2 right2) vx left3)) v3 (Node right3 v1 left1)
    balRV' v = case v of
        LookLeft  (LookLeft rr)                 -> LookLeft (balanceV @_ @(N R t2 u uv t3) @z @zv @l (LookLeft (case rr of
                                                        LookLeft t2 -> LookLeft t2
                                                        Here uv -> Here uv
                                                        LookRight t3 -> LookRight t3)))
        LookLeft  (Here zv)                     -> LookLeft (balanceV @_ @(N R t2 u uv t3) @z @zv @l (Here zv))
        LookLeft  (LookRight (LookLeft l))      -> LookLeft (balanceV @_ @(N R t2 u uv t3) @z @zv @l (LookRight l))
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


type Fuseable :: Map Symbol q -> Map Symbol q -> Constraint
class Fuseable (l :: Map Symbol q) (r :: Map Symbol q) where
    type Fuse l r :: Map Symbol q
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
instance Fuseable (N B left1 k1 v1 right1) left2 
    => Fuseable (N B left1 k1 v1 right1) (N R left2 k2 v2 right2) where
    type Fuse   (N B left1 k1 v1 right1) (N R left2 k2 v2 right2) = N R (Fuse (N B left1 k1 v1 right1) left2) k2 v2 right2
    fuseRecord (Node left1 v1 right1) (Node left2 v2 right2) = Node (fuseRecord @_ @(N B left1 k1 v1 right1) (Node left1 v1 right1) left2) v2 right2 
    fuseVariant e = case e of 
        Left l  -> case l of
            LookLeft left1   -> LookLeft  (fuseVariant @_ @(N B left1 k1 v1 right1) @left2 (Left (LookLeft left1)))
            Here v1          -> LookLeft  (fuseVariant @_ @(N B left1 k1 v1 right1) @left2 (Left (Here v1)))
            LookRight right1 -> LookLeft  (fuseVariant @_ @(N B left1 k1 v1 right1) @left2 (Left (LookRight right1)))
        Right r -> case r of
            LookLeft left2   -> LookLeft  (fuseVariant @_ @(N B left1 k1 v1 right1) @left2 (Right left2))
            Here v2          -> Here      v2
            LookRight right2 -> LookRight right2


-- app (T R a x b) c = T R a x (app b c)
instance Fuseable right1 (N B left2 k2 v2 right2) 
    => Fuseable (N R left1 k1 v1 right1) (N B left2 k2 v2 right2) where
    type Fuse   (N R left1 k1 v1 right1) (N B left2 k2 v2 right2) = N R left1 k1 v1 (Fuse right1 (N B left2 k2 v2 right2))
    fuseRecord (Node left1 v1 right1) (Node left2 v2 right2) = Node left1 v1 (fuseRecord @_ @_ @(N B left2 k2 v2 right2) right1 (Node left2 v2 right2))
    fuseVariant e = case e of
        Left l  -> case l of
            LookLeft left1   -> LookLeft left1
            Here v1          -> Here v1
            LookRight right1 -> LookRight (fuseVariant @_ @right1 @(N B left2 k2 v2 right2) (Left right1))
        Right r -> case r of
            LookLeft left2   -> LookRight (fuseVariant @_ @right1 @(N B left2 k2 v2 right2) (Right (LookLeft left2)))
            Here v2          -> LookRight (fuseVariant @_ @right1 @(N B left2 k2 v2 right2) (Right (Here v2)))
            LookRight right2 -> LookRight (fuseVariant @_ @right1 @(N B left2 k2 v2 right2) (Right (LookRight right2)))


-- app (T R a x b) (T R c y d) =
instance (Fuseable right1 left2, Fuse right1 left2 ~ fused, FuseableHelper1 fused (N R left1 k1 v1 right1) (N R left2 k2 v2 right2)) 
    => Fuseable (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) where
    type Fuse   (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) = Fuse1 (Fuse right1 left2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) 
    fuseRecord = fuseRecord1 @_ @(Fuse right1 left2) 
    fuseVariant = fuseVariant1 @_ @(Fuse right1 left2)

type FuseableHelper1 :: Map Symbol q -> Map Symbol q -> Map Symbol q -> Constraint
class FuseableHelper1 (fused :: Map Symbol q) (l :: Map Symbol q) (r :: Map Symbol q) where
    type Fuse1 fused l r :: Map Symbol q
    fuseRecord1 :: Record f l -> Record f r -> Record f (Fuse l r)
    fuseVariant1 :: Either (Variant f l) (Variant f r) -> Variant f (Fuse l r)

-- app (T R a x b) (T R c y d) =
--  case app b c of
--      T R b' z c' -> T R (T R a x b') z (T R c' y d)
-- FIXME: The Fuseable constraint is repeated from avobe :(
instance (Fuseable right1 left2, Fuse right1 left2 ~ N R s1 z zv s2) 
    => FuseableHelper1 (N R s1 z zv s2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) where
    type Fuse1         (N R s1 z zv s2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) = N R (N R left1 k1 v1 s1) z zv (N R s2 k2 v2 right2)
    fuseRecord1 (Node left1 v1 right1) (Node left2 v2 right2) = 
        case fuseRecord right1 left2 of
            Node s1 zv s2 -> Node (Node left1 v1 s1) zv (Node s2 v2 right2)
    fuseVariant1 e = 
        case e of
            Left l  -> case l of
                            LookLeft  left1  -> LookLeft (LookLeft left1)
                            Here      v1     -> LookLeft (Here v1)
                            LookRight right1 -> case fuseVariant @_ @right1 @left2 (Left right1) of
                                                    LookLeft s1  -> LookLeft (LookRight s1)
                                                    Here zv      -> Here zv
                                                    LookRight s2 -> LookRight (LookLeft s2)
            Right r -> case r of 
                            LookLeft  left2  -> case fuseVariant @_ @right1 @left2 (Right left2) of
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
instance (Fuseable right1 left2, Fuse right1 left2 ~ N B s1 z zv s2) 
    => FuseableHelper1 (N B s1 z zv s2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) where
    type Fuse1         (N B s1 z zv s2) (N R left1 k1 v1 right1) (N R left2 k2 v2 right2) = N R left1 k1 v1 (N R (N B s1 z zv s2) k2 v2 right2)
    fuseRecord1 (Node left1 v1 right1) (Node left2 v2 right2) = 
        case fuseRecord right1 left2 of
            Node s1 zv s2 -> Node left1 v1 (Node (Node s1 zv s2) v2 right2)
    fuseVariant1 e = 
        case e of
            Left l  -> case l of
                            LookLeft  left1  -> LookLeft left1
                            Here      v1     -> Here v1
                            LookRight right1 -> case fuseVariant @_ @right1 @left2 (Left right1) of
                                                    LookLeft s1  -> LookRight (LookLeft (LookLeft s1))
                                                    Here zv      -> LookRight (LookLeft (Here zv))
                                                    LookRight s2 -> LookRight (LookLeft (LookRight s2))
            Right r -> case r of 
                            LookLeft  left2  -> case fuseVariant @_ @right1 @left2 (Right left2) of
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
    type Fuse1           E (N R left1 k1 v1 E) (N R E k2 v2 right2) = N R left1 k1 v1 (N R E k2 v2 right2)
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
instance (Fuseable right1 left2, Fuse right1 left2 ~ fused, FuseableHelper2 fused (N B left1 k1 v1 right1) (N B left2 k2 v2 right2)) 
    => Fuseable (N B left1 k1 v1 right1) (N B left2 k2 v2 right2) where
    type Fuse   (N B left1 k1 v1 right1) (N B left2 k2 v2 right2) = Fuse2 (Fuse right1 left2) (N B left1 k1 v1 right1) (N B left2 k2 v2 right2) 
    fuseRecord = fuseRecord2 @_ @(Fuse right1 left2) 
    fuseVariant = fuseVariant2 @_ @(Fuse right1 left2)

-- could FuseableHelper1 and FuseableHelper2 be, well... fused?
class FuseableHelper2 (fused :: Map Symbol q) (l :: Map Symbol q) (r :: Map Symbol q) where
    type Fuse2 fused l r :: Map Symbol q
    fuseRecord2 :: Record f l -> Record f r -> Record f (Fuse l r)
    fuseVariant2 :: Either (Variant f l) (Variant f r) -> Variant f (Fuse l r)

-- app (T B a x b) (T B c y d) = 
--  case app b c of
--      T R b' z c' -> T R (T B a x b') z (T B c' y d)
instance (Fuseable right1 left2, Fuse right1 left2 ~ N R s1 z zv s2) 
    => FuseableHelper2 (N R s1 z zv s2) (N B left1 k1 v1 right1) (N B left2 k2 v2 right2) where
    type Fuse2         (N R s1 z zv s2) (N B left1 k1 v1 right1) (N B left2 k2 v2 right2) = N R (N B left1 k1 v1 s1) z zv (N B s2 k2 v2 right2)
    fuseRecord2 (Node left1 v1 right1) (Node left2 v2 right2) = 
        case fuseRecord right1 left2 of
            Node s1 zv s2 -> Node (Node left1 v1 s1) zv (Node s2 v2 right2) 
    fuseVariant2 e =
        case e of
            Left l  -> case l of
                            LookLeft  left1  -> LookLeft (LookLeft left1)
                            Here      v1     -> LookLeft (Here v1)
                            LookRight right1 -> case fuseVariant @_ @right1 @left2 (Left right1) of
                                                    LookLeft s1  -> LookLeft (LookRight s1)
                                                    Here zv      -> Here zv
                                                    LookRight s2 -> LookRight (LookLeft s2)
            Right r -> case r of 
                            LookLeft  left2  -> case fuseVariant @_ @right1 @left2 (Right left2) of
                                                    LookLeft s1  -> LookLeft (LookRight s1)
                                                    Here zv      -> Here zv
                                                    LookRight s2 -> LookRight (LookLeft s2)
                            Here      v2     -> LookRight (Here v2)
                            LookRight right2 -> LookRight (LookRight right2)

-- app (T B a x b) (T B c y d) = 
--  case app b c of
--      ...
--      bc -> balleft a x (T B bc y d)
instance (Fuseable right1 left2, Fuse right1 left2 ~ N B s1 z zv s2, BalanceableL left1 k1 v1 (N B (N B s1 z zv s2) k2 v2 right2)) 
    => FuseableHelper2 (N B s1 z zv s2) (N B left1 k1 v1 right1) (N B left2 k2 v2 right2) where
    type Fuse2         (N B s1 z zv s2) (N B left1 k1 v1 right1) (N B left2 k2 v2 right2) = BalL left1 k1 v1 (N B (N B s1 z zv s2) k2 v2 right2)
    fuseRecord2 (Node left1 v1 right1) (Node left2 v2 right2) = 
        case fuseRecord @_ @right1 @left2 right1 left2 of
            Node s1 zv s2 -> balLR @_ @left1 @k1 @v1 @(N B (N B s1 z zv s2) k2 v2 right2) (Node left1 v1 (Node (Node s1 zv s2) v2 right2))
    fuseVariant2 e = balLV @_ @left1 @k1 @v1 @(N B (N B s1 z zv s2) k2 v2 right2) (case e of
            Left l  -> case l of
                            LookLeft  left1  -> LookLeft left1
                            Here      v1     -> Here v1
                            LookRight right1 -> case fuseVariant @_ @right1 @left2 (Left right1) of
                                                    LookLeft s1  -> LookRight (LookLeft (LookLeft s1))
                                                    Here zv      -> LookRight (LookLeft (Here zv))
                                                    LookRight s2 -> LookRight (LookLeft (LookRight s2))
            Right r -> case r of 
                            LookLeft  left2  -> case fuseVariant @_ @right1 @left2 (Right left2) of
                                                    LookLeft s1  -> LookRight (LookLeft (LookLeft s1))
                                                    Here zv      -> LookRight (LookLeft (Here zv))
                                                    LookRight s2 -> LookRight (LookLeft (LookRight s2))
                            Here      v2     -> LookRight (Here v2)
                            LookRight right2 -> LookRight (LookRight right2))

-- app (T B a x b) (T B c y d) = 
--  case app b c of
--      ...
--      bc -> balleft a x (T B bc y d)
instance (BalanceableL left1 k1 v1 (N B E k2 v2 right2)) 
    => FuseableHelper2 E (N B left1 k1 v1 E) (N B E k2 v2 right2) where
    type Fuse2         E (N B left1 k1 v1 E) (N B E k2 v2 right2) = BalL left1 k1 v1 (N B E k2 v2 right2)
    fuseRecord2 (Node left1 v1 right1) (Node left2 v2 right2) = 
            balLR @_ @left1 @k1 @v1 @(N B E k2 v2 right2) (Node left1 v1 (Node Empty v2 right2))
    fuseVariant2 e = balLV @_ @left1 @k1 @v1 @(N B E k2 v2 right2) (case e of
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
-- removing the inline kind signatures here breaks stuff...
type Delable :: Symbol -> q -> Map Symbol q -> Constraint
class Delable (k :: Symbol) (v :: q) (t :: Map Symbol q) where
    type Del k v t :: Map Symbol q
    del :: Record f t -> Record f (Del k v t)
    win :: Variant f t -> Either (Variant f (Del k v t)) (f v) 

--  delformLeft a@(T B _ _ _) y b = balleft (del a) y b
--  delformLeft a y b = T R (del a) y b
--  In the term-level code, the k to delete is already on the environment.
class DelableL (k :: Symbol) (v :: q) (l :: Map Symbol q) (kx :: Symbol) (vx :: q) (r :: Map Symbol q) where
    type DelL k v l kx vx r :: Map Symbol q
    delL :: Record f (N color l kx vx r) -> Record f (DelL k v l kx vx r)
    winL :: Variant f (N color l kx vx r) -> Either (Variant f (DelL k v l kx vx r)) (f v) 

--  delformLeft a@(T B _ _ _) y b = balleft (del a) y b
instance (N B leftz kz vz rightz ~ g, Delable k v g, Del k v g ~ deleted, BalanceableL deleted kx vx right) 
    => DelableL k v (N B leftz kz vz rightz) kx vx right where
    type DelL   k v (N B leftz kz vz rightz) kx vx right = BalL (Del k v (N B leftz kz vz rightz)) kx vx right
    delL (Node left vx right) = balLR @_ @(Del k v (N B leftz kz vz rightz)) @kx @vx @right (Node (del @_ @k @v left) vx right)
    winL v = first (balLV @_ @(Del k v (N B leftz kz vz rightz)) @kx @vx @right) (case v of
        LookLeft l -> first LookLeft (win @_ @k @v l)
        Here vx -> Left $ Here vx
        LookRight r -> Left $ LookRight r)

--  delformLeft a y b = T R (del a) y b
instance (Delable k v (N R leftz kz vz rightz)) 
    => DelableL k v (N R leftz kz vz rightz) kx vx right where
    type DelL   k v (N R leftz kz vz rightz) kx vx right = N R (Del k v (N R leftz kz vz rightz)) kx vx right
    delL (Node left vx right) = Node (del @_ @k @v left) vx right
    winL v = case v of
        LookLeft l -> first LookLeft (win @_ @k @v l)
        Here vx -> Left (Here vx)
        LookRight r -> Left (LookRight r)

--  delformLeft a y b = T R (del a) y b
instance DelableL k v E kx vx right where
    type DelL     k v E kx vx right = N R E kx vx right
    delL (Node left vx right) = Node Empty vx right
    winL v = case v of
        Here vx -> Left (Here vx)
        LookRight r -> Left (LookRight r)

--  delformRight a y b@(T B _ _ _) = balright a y (del b)
--  delformRight a y b = T R a y (del b)
class DelableR (k :: Symbol) (v :: q) (l :: Map Symbol q) (kx :: Symbol) (vx :: q) (r :: Map Symbol q) where
    type DelR k v l kx vx r :: Map Symbol q
    delR :: Record f (N color l kx vx r) -> Record f (DelR k v l kx vx r)
    winR :: Variant f (N color l kx vx r) -> Either (Variant f (DelR k v l kx vx r)) (f v) 

--  delformRight a y b@(T B _ _ _) = balright a y (del b)
instance (N B leftz kz vz rightz ~ g, Delable k v g, Del k v g ~ deleted, BalanceableR left kx vx deleted) 
    => DelableR k v left kx vx (N B leftz kz vz rightz) where
    type DelR   k v left kx vx (N B leftz kz vz rightz) = BalR left kx vx (Del k v (N B leftz kz vz rightz))
    delR (Node left vx right) = balRR @_ @left @kx @vx @(Del k v (N B leftz kz vz rightz)) (Node left vx (del @_ @k @v right))
    winR v = first (balRV @_ @left @kx @vx @(Del k v (N B leftz kz vz rightz))) (case v of
        LookLeft l -> Left $ LookLeft l
        Here vx -> Left $ Here vx
        LookRight r -> first LookRight (win @_ @k @v r))

--  delformRight a y b = T R a y (del b)
instance (Delable k v (N R leftz kz vz rightz)) 
    => DelableR k v left kx vx (N R leftz kz vz rightz) where
    type   DelR k v left kx vx (N R leftz kz vz rightz) = N R left kx vx (Del k v (N R leftz kz vz rightz))
    delR (Node left vx right) = Node left vx (del @_ @k @v right)
    winR v = case v of
        LookLeft l -> Left (LookLeft l)
        Here vx -> Left (Here vx)
        LookRight r -> first LookRight (win @_ @k @v r)

--  delformRight a y b = T R a y (del b)
instance DelableR k v left kx vx E where
    type DelR     k v left kx vx E = N R left kx vx E
    delR (Node left vx right) = Node left vx Empty
    winR v = case v of
        LookLeft l -> Left (LookLeft l)
        Here vx -> Left (Here vx)

--  del E = E
instance Delable k v E where
    type Del     k v E = E
    del _ = unit
    win = impossible

-- the color is discarded
--  del (T _ a y b)
--      | x<y = delformLeft a y b
--      | x>y = delformRight a y b
--      | otherwise = app a b
instance (CmpSymbol kx k ~ ordering, DelableHelper ordering k v left kx vx right) => Delable k v (N color left kx vx right) where
    type Del k v (N color left kx vx right) = Del' (CmpSymbol kx k) k v left kx vx right
    del = del' @_ @(CmpSymbol kx k) @k @v @left @kx @vx @right
    win = win' @_ @(CmpSymbol kx k) @k @v @left @kx @vx @right

class DelableHelper (ordering :: Ordering) (k :: Symbol) (v :: q) (l :: Map Symbol q) (kx :: Symbol) (vx :: q) (r :: Map Symbol q) where
    type Del' ordering k v l kx vx r :: Map Symbol q
    del' :: Record f (N color l kx vx r) -> Record f (Del' ordering k v l kx vx r)
    win' :: Variant f (N color l kx vx r) -> Either (Variant f (Del' ordering k v l kx vx r)) (f v) 

--      | x<y = delformLeft a y b
instance DelableL k v left kx vx right => DelableHelper GT k v left kx vx right where
    type Del'                                           GT k v left kx vx right = DelL k v left kx vx right
    del' = delL @_ @k @v @left @kx @vx @right  
    win' = winL @_ @k @v @left @kx @vx @right  

--      | otherwise = app a b
instance Fuseable left right => DelableHelper EQ k v left k v right where
    type Del'                                 EQ k v left k v right = Fuse left right
    del' (Node left _ right) = fuseRecord @_ @left @right left right 
    win' v = case v of
        LookLeft l  ->  Left $ fuseVariant @_ @left @right (Left l)
        Here v      -> Right v 
        LookRight r -> Left $ fuseVariant @_ @left @right (Right r)

--      | x>y = delformRight a y b
instance DelableR k v left kx vx right => DelableHelper LT k v left kx vx right where
    type Del'                                           LT k v left kx vx right = DelR k v left kx vx right
    del' = delR @_ @k @v @left @kx @vx @right  
    win' = winR @_ @k @v @left @kx @vx @right  

{- | Class that determines if the pair of a 'Symbol' key and a type can
     be deleted from a type-level map.
 
     The associated type family 'Delete' produces the resulting map.

     At the term level, this manifests in 'delete', which removes a field from
     a record, and in 'winnow', which checks if a 'Variant' is of a given
     branch and returns the value in the branch if there's a match, or a
     reduced 'Variant' if there isn't. 'winnow' tends to be more useful in
     practice.

     If the map already has the key but with a /different/ type, the deletion
     fails to compile.
 -}
class Deletable (k :: Symbol) (v :: q) (t :: Map Symbol q) where
    type Delete k v t :: Map Symbol q
    _delete :: Record f t -> Record f (Delete k v t)
    _winnow :: Variant f t -> Either (Variant f (Delete k v t)) (f v) 

instance (Delable k v t, Del k v t ~ deleted, CanMakeBlack deleted) => Deletable k v t where
    type Delete k v t = MakeBlack (Del k v t)
    _delete r = makeBlackR (del @_ @k @v r) 
    _winnow v = first makeBlackV (win @_ @k @v v)

{- | 
     Removes a field from a 'Record'.
 -}
delete :: forall k v t f . Deletable k v t => Record f t -> Record f (Delete k v t)
delete = _delete @_ @k @v @t

{- | 
     Checks if a 'Variant' is of a given branch and returns the value in the
     branch if there's a match, or a reduced 'Variant' if there isn't. 
 -}
winnow :: forall k v t f . Deletable k v t => Variant f t -> Either (Variant f (Delete k v t)) (f v)
winnow = _winnow @_ @k @v @t 

{- | Like 'winnow' but specialized to pure 'Variant's.
 
>>> winnow @"bar" @Bool (injectI @"bar" False :: Variant I (FromList [ '("foo",Char), '("bar",Bool) ]))
Right (I False)

>>> prettyShow_VariantI `first` winnow @"foo" @Char (injectI @"bar" False :: Variant I (FromList [ '("foo",Char), '("bar",Bool) ]))
Left "bar (False)" 

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

