module Data.RBR.Examples (
    -- * Constructing a record and viewing its fields.
    -- $record1
    
    -- * Getting a subset of fields out of a record.
    -- $record2
    
    -- * Creating a Record out of a conventional Haskell record
    -- $record3
    
    -- * Injecting into a Variant and eliminating it.
    -- $variant1
    ) where

import Data.RBR
import Data.SOP

{- $setup
 
>>> :set -XDataKinds -XTypeApplications -XPartialTypeSignatures -XFlexibleContexts -XTypeFamilies -XDeriveGeneric 
>>> :set -Wno-partial-type-signatures  
>>> import Data.RBR
>>> import Data.SOP
>>> import GHC.Generics

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
 
>>> :{
    let b = injectI @"left" 'c'
        e = addCaseI @"left" putChar
          . addCaseI @"right" @Bool print
          $ unit
     in eliminate e b
:}
c

-} 
