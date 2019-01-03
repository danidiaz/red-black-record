module Data.RBR (
        -- * Type-level Red-Black tree
        Color (..),
        RBT (..),
        -- * Records and Variants
        Record,
        unit,
        Variant,
        ludicrous,
        -- ** Inserting and widening
        Insertable (..),
        InsertAll,
        FromList,
        -- ** Projecting and injecting
        Member (..)
        -- * Internal
    ) where

import Data.RBR.Internal
