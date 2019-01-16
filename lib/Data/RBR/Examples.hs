module Data.RBR.Examples (
    -- * Constructing a record and viewing its fields.
    -- $record1
    
    -- * Getting a subset of fields out of a record
    -- $record2
    
    -- * Creating a Record out of a conventional Haskell record
    -- $record3
    
    -- * Injecting into a Variant and eliminating it
    -- $variant1
    
    -- * Creating a Variant out of a sum type and matching on it
    -- $variant2
      
    -- * Changing the way a specific record field is parsed from JSON
    -- $json1
    ) where

import Data.RBR
import Data.SOP

{- $setup
 
>>> :set -XDataKinds -XTypeApplications -XPartialTypeSignatures -XFlexibleContexts -XTypeFamilies -XDeriveGeneric -XAllowAmbiguousTypes -XScopedTypeVariables
>>> :set -Wno-partial-type-signatures  
>>> import Data.RBR
>>> import Data.SOP
>>> import Data.SOP.NP (cpure_NP,sequence_NP,cliftA2_NP)
>>> import qualified Data.ByteString.Lazy as BL
>>> import qualified Data.Text
>>> import Data.String
>>> import GHC.Generics
>>> import Data.Functor.Compose
>>> import Data.Aeson
>>> import Data.Aeson.Types (explicitParseField,Parser)
>>> import Data.Proxy

-}

{- $record1
 
We use 'addFieldI' instead of 'addField' because we are dealing with pure
records.

>>> :{ 
    let r = addFieldI @"name" "Foo"
          . addFieldI @"age"  5
          $ unit
     in print (getFieldI @"name" r)
:}
"Foo"
 
-} 

{- $record2
 
Notice that the subset is specified as a type-level tree using 'FromList', a
type family that takes a list of type-level tuples.

Because here the types of each field can be inferred, we can use a wildcard
(enabled by the @PartialTypeSignatures@ extension).

>>> :{ 
    let r = addFieldI @"name"      "Foo"
          . addFieldI @"age"       5
          . addFieldI @"whatever"  'x'
          $ unit
        s = getFieldSubset @(FromList [ '("age",_), '("whatever",_) ]) r
     in putStrLn (prettyShowRecordI s)
:}
{age = 5, whatever = 'x'} 

-} 

{- $record3
 
>>> data Person = Person { name :: String, age :: Int } deriving (Generic, Show)
>>> instance ToRecord Person 
>>> :{ 
    let r = addFieldI @"whatever" 'x' (toRecord (Person "Foo" 50))
     in putStrLn (prettyShowRecordI r)
:}
{age = 50, name = "Foo", whatever = 'x'} 

-} 

{- $variant1
 
   Here the full type of the 'Variant' is inferred from the type of its
   'Record' of eliminators.

>>> :{
    let b = injectI @"left" 'c'
        e = addCaseI @"left" putChar
          . addCaseI @"right" @Bool print
          $ unit
     in eliminate e b
:}
c

-} 


{- $variant2
 
>>> data Summy = Lefty Int | Righty Bool deriving (Generic,Show)
>>> instance ToVariant Summy 
>>> :{
    let v = toVariant (Lefty 5)
     in matchI @"Lefty" v
:}
Just 5

-} 

{- $json1
 
>>> :{
    let parseDifferently 
              :: forall k r c flat. (Generic r, 
                                     FromRecord r, 
                                     RecordCode r ~ c, 
                                     KeysValuesAll KnownKey c, 
                                     Key k c,
                                     Productlike '[] c flat, All FromJSON flat) 
              => (Data.Aeson.Value -> Parser (Data.RBR.Value k c))
              -> Data.Aeson.Value 
              -> Parser r
        parseDifferently p = withObject "someobj" $ \o ->
            let pr = setField @k (Compose p) 
                   $ fromNP @c (cpure_NP (Proxy @FromJSON) (Compose parseJSON))
                mapKCC (K name) (Compose pf) = Compose (\o -> explicitParseField pf o (Data.Text.pack name))
                Compose parser = sequence_NP (cliftA2_NP (Proxy @FromJSON) mapKCC (toNP @c demoteKeys) (toNP pr))  
             in fromRecord . fromNP <$> parser o
    :}

>>> data Person = Person { name :: String, age :: Int } deriving (Generic, Show)
>>> instance ToRecord Person 
>>> instance FromRecord Person 
>>> :{ 
    instance FromJSON Person where 
        parseJSON = parseDifferently @"name" (\_ -> pure "foo")
    :}

>>> Data.Aeson.eitherDecode @Person (fromString "{ \"name\" : null, \"age\" : 50 }")
Right (Person {name = "foo", age = 50})

-}
