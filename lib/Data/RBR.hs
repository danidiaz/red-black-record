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
        insertI,
        InsertAll,
        FromList,
        -- ** Projecting and injecting
        Member (..),
        project,
        projectI,
        inject,
        injectI,
        -- * Data.SOP re-exports
        I(..)
        -- * Internal
    ) where

import Data.RBR.Internal
import Data.SOP (I(..))
