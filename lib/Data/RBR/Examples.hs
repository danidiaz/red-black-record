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
    
    -- * Parsing a record from JSON using aliased fields
    -- $json2
   
    -- * Parsing a subset of a record's fields from JSON and inserting them in an existing record value
    -- $json3
    ) where

import Data.RBR
import Data.SOP

{- $setup
 
>>> :set -XDataKinds -XTypeApplications 
>>> :set -XFlexibleContexts -XTypeFamilies -XAllowAmbiguousTypes -XScopedTypeVariables
>>> :set -XDeriveGeneric 
>>> :set -XPartialTypeSignatures 
>>> :set -Wno-partial-type-signatures  
>>> import Data.RBR
>>> import Data.SOP
>>> import Data.SOP.NP (cpure_NP,sequence_NP,liftA2_NP)
>>> import Data.String
>>> import Data.Proxy
>>> import Data.Profunctor (Star(..))
>>> import GHC.Generics
>>> import qualified Data.Text
>>> import Data.Aeson
>>> import Data.Aeson.Types (explicitParseField,Parser,parseMaybe)

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
 
    We start in the @sop-core@ world, creating a product of parsing functions
    (one for each field) using 'cpure_NP'. 

    Then we convert that product to a 'Record', apply to it a transformation
    that uses field selectors, and convert it back to a product.

    Then we demote the field names and combine them with the product of
    'Data.Aeson.Value' parsers using 'liftA2_NP', getting a product of
    'Data.Aeson.Object' parsers.

    Then we use 'sequence_NP' to convert the product of parsers into a parser
    of 'Record'.

>>> :{
    let parseSpecial
              :: forall r c flat. (Generic r, 
                                   FromRecord r, 
                                   RecordCode r ~ c, 
                                   KeysValuesAll KnownKey c, 
                                   Productlike '[] c flat, All FromJSON flat) 
              => (Record (Star Parser Data.Aeson.Value) c -> Record (Star Parser Data.Aeson.Value) c)
              -> Data.Aeson.Value 
              -> Parser r
        parseSpecial transform = 
            let pr = transform $ fromNP @c (cpure_NP (Proxy @FromJSON) (Star parseJSON))
                mapKSS (K name) (Star pf) = Star (\o -> explicitParseField pf o (Data.Text.pack name))
                Star parser = fromNP <$> sequence_NP (liftA2_NP mapKSS (toNP @c demoteKeys) (toNP pr))
             in withObject "someobj" $ \o -> fromRecord <$> parser o
    :}

>>> data Person = Person { name :: String, age :: Int } deriving (Generic, Show)
>>> instance ToRecord Person 
>>> instance FromRecord Person 
>>> :{ 
    instance FromJSON Person where 
        parseJSON = parseSpecial (setField @"name" (Star (\_ -> pure "foo")))
    :}

>>> Data.Aeson.eitherDecode @Person (fromString "{ \"name\" : null, \"age\" : 50 }")
Right (Person {name = "foo", age = 50})

-}


{- $json2
 
   We have to use 'getFieldSubset' because the aliases are listed in a
   different order than the record fields, and that might result in different
   type-level trees. If the orders were the same, we wouldn't need it. 

>>> :{
    let parseWithAliases
              :: forall r c flat. (Generic r, 
                                   FromRecord r, 
                                   RecordCode r ~ c, 
                                   KeysValuesAll KnownKey c, 
                                   Productlike '[] c flat, All FromJSON flat) 
              => Record (K String) c
              -> Data.Aeson.Value 
              -> Parser r
        parseWithAliases aliases = 
            let pr = fromNP @c (cpure_NP (Proxy @FromJSON) (Star parseJSON))
                mapKSS (K name) (Star pf) = Star (\o -> explicitParseField pf o (Data.Text.pack name))
                Star parser = fromNP <$> sequence_NP (liftA2_NP mapKSS (toNP @c aliases) (toNP pr))
             in withObject "someobj" $ \o -> fromRecord <$> parser o
    :}

>>> data Person = Person { name :: String, age :: Int } deriving (Generic, Show)
>>> instance ToRecord Person 
>>> instance FromRecord Person 
>>> :{ 
    instance FromJSON Person where 
        parseJSON = let aliases = addField @"age"  (K "bar")
                                . addField @"name" (K "foo")
                                $ unit
                     in parseWithAliases (getFieldSubset @(RecordCode Person) aliases)
    :}

>>> Data.Aeson.eitherDecode @Person (fromString "{ \"foo\" : \"John\", \"bar\" : 50 }")
Right (Person {name = "John", age = 50})

-}



{- $json3
 
>>> :{
    let parseFieldSubset
              :: forall subset whole flat wholeflat. (KeysValuesAll KnownKey whole, 
                                                      Productlike '[] whole wholeflat,
                                                      ProductlikeSubset subset whole flat,
                                                      All FromJSON wholeflat) 
              => Data.Aeson.Value 
              -> Parser (Record I subset)
        parseFieldSubset = 
            let pNP = cpure_NP (Proxy @FromJSON) (Star parseJSON)
                mapKSS (K name) (Star pf) = Star (\o -> explicitParseField pf o (Data.Text.pack name))
                objpNP = liftA2_NP mapKSS (toNP @whole demoteKeys) pNP
                subNP = toNP @subset $ getFieldSubset @subset $ fromNP @whole objpNP
                Star subparser = fromNP @subset <$> sequence_NP subNP
             in withObject "someobj" subparser
    :}

>>> data Person = Person { name :: String, age :: Int, whatever :: Bool } deriving (Generic, Show)
>>> instance ToRecord Person 
>>> instance FromRecord Person 
>>> :{ 
    let original = Person "John" 50 True
        Just v = Data.Aeson.decode @Data.Aeson.Value (fromString "{ \"name\" : \"Mark\", \"age\" : 70 }")
        subsetParser = parseFieldSubset @(FromList [ '("name",_), '("age",_) ]) @(RecordCode Person)
        Just s = parseMaybe subsetParser v
     in fromRecord @Person . setFieldSubset s $ toRecord original
    :}
Person {name = "Mark", age = 70, whatever = True}

-}
