module Data.RBR (
        -- * Type-level map
        -- $typelevel
       Map,
       Empty,
       KeysValuesAll(),
       KnownKey(),
       demoteKeys,
       KnownKeyTypeableValue(),
       demoteEntries,
       -- * Records and Variants
       Record,
       unit,
       cpure_Record,
       collapse_Record,
       prettyShowRecord,
       prettyShowRecordI,
       Variant,
       impossible,
       prettyShowVariant,
       prettyShowVariantI,
       -- ** Inserting and widening
       Insertable (Insert),
       InsertAll,
       FromList,
       insert,
       addField,
       insertI,
       addFieldI,
       widen,
       -- ** Deleting and winnowing
       Deletable (Delete),
       delete,
       winnow,
       winnowI,
       -- ** Projecting and injecting
       Key (Value),
       Field,
       field,
       Branch,
       branch,
       project,
       projectI,
       getField,
       getFieldI,
       setField,
       setFieldI,
       modifyField,
       modifyFieldI,
       inject,
       injectI,
       match,
       matchI,
       -- ** Eliminating variants
       eliminate,
       Case (..),
       addCase,
       addCaseI,
       -- ** Subsets of fields and branches
       PresentIn,
       ProductlikeSubset,
       fieldSubset,
       projectSubset,
       getFieldSubset,
       setFieldSubset,
       modifyFieldSubset,
       SumlikeSubset,
       branchSubset,
       injectSubset,
       matchSubset,
       eliminateSubset,
       -- * Interfacing with normal records
       -- $nominal
       ToRecord (..),
       FromRecord (..),
       VariantCode,
       ToVariant (..),
       FromVariant(..),
       -- * Interfacing with Data.SOP
       Productlike (..),
       prefixNP,
       breakNP,
       fromNP,
       toNP,
       Sumlike (..),
       prefixNS,
       breakNS,
       fromNS,
       toNS,
       -- * Data.SOP re-exports
       I(..),
       K(..),
       NP(..),
       NS(..),
    ) where

import Data.RBR.Internal
import Data.SOP (I(..),K(..),NP(..),NS(..))

{- $setup
 
>>> :set -XDataKinds -XTypeApplications -XPartialTypeSignatures -XFlexibleContexts -XTypeFamilies -XDeriveGeneric 
>>> :set -Wno-partial-type-signatures  
>>> import Data.RBR
>>> import Data.SOP
>>> import GHC.Generics

-}

{- $typelevel
 
   A type-level map that keeps track of which keys are present, and to which
   types they correspond.

   Implemented as a red-black tree, and used as a kind by means of @DataKinds@. 
-} 

{- $nominal
  
  Typeclasses for converting to and from normal Haskell records and sum types.

  They have default implementations based in "GHC.Generics":

>>> data Person = Person { name :: String, age :: Int } deriving (Generic, Show)
>>> instance ToRecord Person 
>>> instance FromRecord Person 

>>> data Summy = Lefty Int | Righty Bool deriving (Generic,Show)
>>> instance ToVariant Summy 
>>> instance FromVariant Summy 

    Only single-constructor records with named fields can have 'ToRecord' and
    'FromRecord' instances.

    Only sum types with exactly one anonymous argument on each branch can have
    'ToVariant' and 'FromVariant' instances.

-}
