module Data.RBR.Examples (
    -- * Setup code
    -- $setup

    -- * Constructing a record and viewing its fields.
    -- $record1
    
    -- * Getting a subset of fields out of a record
    -- $record2
    
    -- * Creating a Record out of a conventional Haskell record
    -- $record3
    
    -- * Injecting into a Variant and eliminating it
    -- $variant1
    
    -- * Working with a bigger error type inside a function
    -- $variant1bError
    
    -- * Creating a Variant out of a sum type and matching on it
    -- $variant2
      
    -- * Changing the way a specific record field is parsed from JSON
    -- $json1
    
    -- * Parsing a record from JSON using aliased fields
    -- $json2
   
    -- * Parsing a subset of a record's fields from JSON and inserting them in an existing record value
    -- $json3
    
    -- * Ensuring all branches of a sum type are parsed from JSON
    -- $json4sum

    -- * External examples
    -- $externalexamples
    ) where

import Data.RBR
import Data.SOP

{- $setup
 
>>> :set -XDataKinds -XTypeApplications 
>>> :set -XFlexibleContexts -XTypeFamilies -XAllowAmbiguousTypes -XScopedTypeVariables
>>> :set -XDeriveGeneric 
>>> :set -XPartialTypeSignatures 
>>> :set -XTypeOperators
>>> :set -Wno-partial-type-signatures  
>>> import Data.RBR
>>> import Data.SOP
>>> import Data.SOP.NP (cpure_NP,sequence_NP,liftA2_NP,collapse_NP)
>>> import Data.String
>>> import Data.Proxy
>>> import Data.Foldable
>>> import Data.Profunctor (Star(..))
>>> import GHC.Generics (Generic)
>>> import GHC.TypeLits
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

{- $variant1bError
 
    A function can use internally an error 'Variant' bigger than the one it
    eventually returns. The internal branches of the 'Variant' can be removed with
    'winnow'. 

    This library makes it more involved than it should be, because inserting an
    entry and then deleting it can result in structurally dissimilar type-level
    maps. So we need extra type annotations in 'winnow', and also a call to
    'injectSubset' to perform the conversion.
 
>>> type Smaller = FromList '[ '("foo",Char), '("bar",Int) ]
>>> :{
    let func :: Int -> Variant I Smaller 
        func i = 
            let v = if (i == 0) then injectI @"baz" "internal"
                                else injectI @"foo" 'c'
                r = case winnowI @"baz" @String @(Insert "baz" String Smaller) v of
                        Right   e       -> error "this is the baz internal error"
                        Left    smaller -> smaller
             in injectSubset r
     in putStrLn $ prettyShowVariantI (func 1)
:}
foo ('c')

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
              :: forall r c flat. (IsRecordType r c, 
                                   Maplike c,
                                   KeysValuesAll (KeyValueConstraints KnownSymbol FromJSON) c) 
              => (Record ((,) String :.: Star Parser Data.Aeson.Value) c -> Record ((,) String :.: Star Parser Data.Aeson.Value) c)
              -> Data.Aeson.Value 
              -> Parser r
        parseSpecial transform = 
            let fieldParsers = transform $ 
                    cpure'_Record (Proxy @FromJSON) $ \fieldName -> Comp (fieldName,Star parseJSON)
                applyName (Comp (fieldName,Star f)) = Star (\o -> explicitParseField f o (Data.Text.pack fieldName))
                Star objectParser = sequence_Record $ liftA_Record applyName fieldParsers
             in withObject "someobj" $ \o -> fromRecord <$> objectParser o
    :}

>>> data Person = Person { name :: String, age :: Int } deriving (Generic, Show)
>>> instance ToRecord Person 
>>> instance FromRecord Person 
>>> :{ 
    instance FromJSON Person where 
        parseJSON = parseSpecial (setField @"name" (Comp ("anothername",Star (\_ -> pure "foo"))))
    :}

>>> Data.Aeson.eitherDecode @Person (fromString "{ \"anothername\" : null, \"age\" : 50 }")
Right (Person {name = "foo", age = 50})

-}


{- $json2
 
    The aliases are passed as a 'Record' with values wrapped in the 'K'
    functor. This means that there aren't really any values of the type that
    corresponds to each field, only the `String` annotations.

>>> :{
    let parseWithAliases
              :: forall r c flat. (IsRecordType r c, 
                                   Maplike c,
                                   KeysValuesAll (ValueConstraint FromJSON) c) 
              => Record (K String) c
              -> Data.Aeson.Value 
              -> Parser r
        parseWithAliases aliases = 
            let fieldParsers = cpure_Record (Proxy @(ValueConstraint FromJSON)) (Star parseJSON)
                mapKSS (K name) (Star pf) = Star (\o -> explicitParseField pf o (Data.Text.pack name))
                Star objectParser = sequence_Record $ liftA2_Record mapKSS aliases fieldParsers
             in withObject "someobj" $ \o -> fromRecord <$> objectParser o
    :}

   We have to use 'getFieldSubset' because the aliases are listed in a
   different order than the record fields, and that might result in different
   type-level trees. If the orders were the same, we wouldn't need it. 

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
              :: forall subset subflat c r. (IsRecordType r c, 
                                             Maplike subset,
                                             KeysValuesAll (KeyValueConstraints KnownSymbol FromJSON) subset, 
                                             ProductlikeSubset subset c subflat) 
              => r 
              -> Data.Aeson.Value
              -> Parser r 
        parseFieldSubset r = 
            let subparser = 
                    sequence_Record $
                        cpure'_Record (Proxy @FromJSON) $ \fieldName ->
                            Star (\o -> explicitParseField parseJSON o (Data.Text.pack fieldName))
                intoOriginal subrecord = fromRecord (setFieldSubset @subset subrecord (toRecord r))
                Star parser = intoOriginal <$> subparser
             in withObject "someobj" parser
    :}

>>> data Person = Person { name :: String, age :: Int, whatever :: Bool } deriving (Generic, Show)
>>> instance ToRecord Person 
>>> instance FromRecord Person 
>>> :{ 
    let original = Person "John" 50 True
        Just v = Data.Aeson.decode @Data.Aeson.Value (fromString "{ \"name\" : \"Mark\", \"age\" : 70 }")
        subsetParser = parseFieldSubset @(FromList [ '("name",_), '("age",_) ]) original
        Just s = parseMaybe subsetParser v
     in s
    :}
Person {name = "Mark", age = 70, whatever = True}

-}


{- $json4sum
 
    To ensure that we don't forget any branch when parsing a sum type from JSON, 
    we can create a n-ary product of parsers, one for each branch.

    Then we create a n-ary product of injections. Each component of the
    product creates a n-ary sum out of the value of the corresponding branch.

    We combine the n-ary product of parsers with the n-ary product of
    injections, and collapse all the resulting parsers with
    'Control.Applicative.asum'.

    Then we convert the n-ary sum value that "wins" into a 'Variant' and
    finally back into the original type.

>>> :{
    let parseAll
              :: forall r c flat. (IsVariantType r c, 
                                   Maplike c,
                                   KeysValuesAll (KeyValueConstraints KnownSymbol FromJSON) c, 
                                   Productlike '[] c flat) 
              => Data.Aeson.Value 
              -> Parser r
        parseAll = 
            let fieldParsers = cpure'_Record (Proxy @FromJSON) $ \fieldName -> 
                    Star (\o -> explicitParseField parseJSON o (Data.Text.pack fieldName))
                injected = liftA2_Record (\f star -> K (runVariantInjection f . I <$> star)) injections_Variant fieldParsers 
                Star parser = asum $ collapse_Record injected
             in withObject "someobj" (\o -> fromVariant <$> parser o)
    :}

>>> data ThisOrThat = This String | That Int deriving (Generic, Show)
>>> instance FromVariant ThisOrThat
>>> instance ToVariant ThisOrThat
>>> :{ 
    let Just v = Data.Aeson.decode @Data.Aeson.Value (fromString "{ \"That\" : 70 }")
        Just s = parseMaybe (parseAll @ThisOrThat) v
     in s
    :}
That 70

-}

{- $externalexamples
 
    * [Is there a canonical way of comparing/changing one/two records in haskell? (SO)](https://stackoverflow.com/a/57574731/1364288)
    * [Given a record of functions, and a record of data of the types acted on by the functions, how to generically apply the function record? (SO)](https://stackoverflow.com/a/58890226/1364288) 
    * [Help with Generics. (Reddit)](https://www.reddit.com/r/haskell/comments/cteemj/help_with_generics/expyjfk)
    * [Adventures assembling records of capabilities. (Discourse)](https://discourse.haskell.org/t/adventures-assembling-records-of-capabilities/623)
    * [Creating a result piecewise from stateful computation. (SO)](https://stackoverflow.com/a/60067270/1364288)
    * [Extracting sections of function pipelines. (GitHub)](https://gist.github.com/danidiaz/2157e68f5d4967e468a9d062d4476adf#file-pipelines3-hs)
    * [Resources on sop-core and generics-sop. (GitHub)](https://github.com/well-typed/generics-sop/issues/47)

-}

