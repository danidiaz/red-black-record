# Revision history for red-black-record

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
