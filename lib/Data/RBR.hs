module Data.RBR (
        -- * Type-level Red-Black tree
        Color (..),
        RBT (..),
        -- * Records and Variants
        Record,
        unit,
        Variant,
        impossible,
        -- ** Inserting and widening
        Insertable (..),
        insertI,
        InsertAll,
        FromList,
        -- ** Projecting and injecting
        KeyIn,
        Key (..),
        project,
        inject,
        projectI,
        injectI,
        -- * Interation with Data.SOP
        Productlike (..),
        Sumlike (..),
        -- * Data.SOP re-exports
        I(..)
        -- * Internal
    ) where

import Data.RBR.Internal
import Data.SOP (I(..))
