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
        addField,
        insertI,
        addFieldI,
        InsertAll,
        FromList,
        -- ** Projecting and injecting
        Key (..),
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
        -- ** Subsetting
        fieldSubset,
        projectSubset,
        getFieldSubset,
        setFieldSubset,
        modifyFieldSubset,
        InjectableSubset,
        branchSubset,
        injectSubset,
        matchSubset,
        eliminateSubset,
        -- * Interfacing with normal records
        FromRecord (..),
        ToRecord (..),
        -- NominalSum (..),
        -- * Interfacing with Data.SOP
        PrefixNP (..),
        fromNP,
        toNP,
        PrefixNS (..),
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
