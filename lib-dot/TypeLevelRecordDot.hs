{-# LANGUAGE DataKinds,
             TypeOperators,
             TypeFamilies,
             TypeApplications,
             DeriveGeneric,
             StandaloneDeriving,
             DerivingStrategies,
             UndecidableInstances,
             KindSignatures,
             PartialTypeSignatures,
             FlexibleContexts,
             ScopedTypeVariables,
             StandaloneKindSignatures
#-}
-- | This module is for exploring record types in the REPL.
module TypeLevelRecordDot (Dot) where

import GHC.Generics (Generically(..))
import Data.RBR
import Data.Kind
import GHC.TypeLits

-- | Inspect the type of a field in a record
--
-- The idea is to use this type family in the REPL, using @kind!@ Mostly useful
-- with complex parameterized records whose fields vary a lot according to the
-- parameters.
--
-- If the record is at the "tip" of a function, the type family goes to the tip.
--
-- The records must have Generic instances.
-- https://hachyderm.io/@DiazCarrete/112342828307643526 
type Dot :: Type -> Symbol -> Type
type family Dot r n where
    Dot (a -> b) n = a -> Dot b n
    Dot r n = Value n (RecordCode (Generically r))
