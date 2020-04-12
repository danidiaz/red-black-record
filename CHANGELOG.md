# Revision history for red-black-record

## 2.1.1.0
- Added NP-like functions for working on Records, like sequence_Record.
  They are memebers of the Maplike typeclass.
- Deprecated the -Subset functions from Data.RBR and created a new module
  Data.RBR.Subset with new versions. To avoid collisions, Data.RBR.Subset
  should be imported qualified.
- Deprecated a number of other functions that had Productlike / Sumlike
  constraints, added new functions with Maplike constraints.
- Added IsRecordType, IsVariantType.
- Added KeyValueConstraints, ValueConstraint.

## 2.1.0.0

- Made the type-level map poly-kinded in the values, as there wasn't a real
  reason to force them to the  Type kind. 
- Removed deprecated EmptyMap (use Empty instead).

## 2.0.4.0

- Compatibility with sop-core 0.5.0.0.
- Contravariant intance for Case newtype.

## 2.0.3.0

- Issue #7: FromVariant & ToVariant instances for sum types with branches with
  no arguments.

## 2.0.2.2

- Improved compilation times for type-level deletion.

## 2.0.0.0

- BREAKING CHANGES
    - The constructors for the type-level map are now hidden.
    - The name of the type-level map has changed from RBT to Map, to
      de-emphasize implementation details. 

- Added the "Deletable" typeclass with de "delete" and "winnow" methods.

- Solved bugs with coloring/balancing, added new tests.

- Data.RBR.Internal is still exported, but it doesn't appear in the Haddocks.
  It appears that Haddock doesn't play well with reexported-modules sections in
  Cabal.

## 1.1.0.0

- Field and Branch type families to help speed up type-level computations. 

  Apparently, having identical invocations of a "costly to compute" type family
  in a signature slowed things down.

## 1.0.0.2

- Improved compilation times for getters by refactoring `KeyHelper`.

## 1.0.0.0

- First version. Released on an unsuspecting world.
