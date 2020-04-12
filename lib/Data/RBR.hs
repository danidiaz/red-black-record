{-| 
    This module provides extensible 'Record' and 'Variant' types, which are
    indexed by a type-level 'Map'.

    Many functions in this module require the use of @TypeApplications@ to
    avoid ambiguity. The order of the applications is the order of the type
    variables in the function signature's @forall@. The first type variable is
    usually the field/branch name and it's always required. The other type
    variables can often be inferred.

    Meaning of commonly used type and kind variables:

        - @t@: A type-level 'Map', usually of kind @Map Symbol q@.
        - @k@: A key of kind 'Symbol' in a type-level 'Map'. 
        - @v@: A type value of kind @q@ in a type-level 'Map'.
        - @q@: The kind of the type value @v@.
        - @f@: A type constructor of kind @q -> Type@ that wraps the type @v@. 
        - @flat@: A type-level list of kind @[q]@ whose elements correspond to values in a type-level 'Map'.
        
-}
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
       KeyValueConstraints,
       ValueConstraint,
       -- * Records and Variants
       Record,
       unit,
       cpure_Record,
       cpure'_Record,
       prettyShow_Record,
       prettyShow_RecordI,
       Variant,
       impossible,
       prettyShow_Variant,
       prettyShow_VariantI,
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
       -- ** Transformations
       Maplike(..),
       VariantInjection(..),
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
       IsRecordType,
       VariantCode,
       ToVariant (..),
       FromVariant(..),
       IsVariantType,
       -- * Interfacing with Data.SOP
       Productlike (..),
       prefixNP,
       breakNP,
       toNP,
       fromNP,
       Sumlike (..),
       prefixNS,
       breakNS,
       toNS,
       fromNS,
       -- * Data.SOP re-exports
       I(..),
       K(..),
       NP(..),
       NS(..),
       (:.:)(..),
       -- * Deprecated
       collapse_Record,
       prettyShowRecord,
       prettyShowRecordI,
       prettyShowVariant,
       prettyShowVariantI
    ) where

import Data.RBR.Internal
import Data.SOP (I(..),K(..),NP(..),NS(..),(:.:)(..),Top)

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
