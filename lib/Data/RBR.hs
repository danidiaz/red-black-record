module Data.RBR (
        -- * Type-level Red-Black tree
        Color (..),
        RBT (..),
        KeysValuesAll,
        demoteKeys,
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
        match,
        projectI,
        injectI,
        matchI,
        -- * Interfacing with Data.SOP
        Productlike (..),
        fromNP',
        toNP',
        Sumlike (..),
        fromNS',
        toNS',
        -- * Interfacing with normal records
        NominalRecord (..),
        NominalSum (..),
        -- * Data.SOP re-exports
        I(..),
        K(..),
        NP(..),
        NS(..),
        -- * Internal
    ) where

import Data.RBR.Internal
import Data.SOP (I(..),K(..),NP(..),NS(..))
