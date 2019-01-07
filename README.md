# red-black-record

## What's this?

A library that provides extensible records and variants, where both are indexed
by a type-level rose tree that maps field names to value types.

## FAQ

### My type signatures are getting big and scary thanks to those type-level trees. What to do?

The
[`-XPartialTypeSignatures`](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html?#extension-PartialTypeSignatures)
extension can help with that, in combination with the
[-Wno-partial-type-signatures](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/using-warnings.html#ghc-flag--Wpartial-type-signatures)
GHC flag that disables the warning message emitted when the underscore is
encountered.

The flag can be set globally in the
[ghc-options](https://www.haskell.org/cabal/users-guide/developing-packages.html?#pkg-field-ghc-options)
section of the .cabal file, and also for a particular module with the
[OPTIONS_GHC](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html?highlight=options_ghc#options-ghc-pragma)
file-header pragma.

### The show instance for record doesn't show any field names.

The field names exists only at the type level. Aslo, the `Show` instance uses
n-ary products and sums from
[sop-core](http://hackage.haskell.org/package/sop-core), which do not have
field labels.

### Working with two records, I'm getting errors about incompatible types even as both records have the exact same fields.

The order of insertion in the type-level tree matters, alas :( Different
insertion orders can produce structurally different trees, even as they encode
the same symbol-to-type map.

Perhaps some kind of conversion function will be implemented in the future. It
would be opt-int, as it will likely incur in some compile-time overhead.

### I can't insert into a record when a field with the same name but different type already exists. Why not simply overwrite it?

That limitation was intentional, because allowing it would make impossible to
implement of `widen` for `Variant`. When/if type-level field deletion gets
implemented, one solution would be to explicitly delete the field and then
insert it again.

### The library doesn't use Proxy and relies on type application instead. But what’s the order of the type parameters?

For typeclass methods, it's the order in which the type variables appear in the
typeclass declaration.

For standalone functions, it’s the order in which the type variables appear in
the `forall`.

### What's the deal with all those -I suffixed versions of functions?

This library aims to provide
[HKD](http://reasonablypolymorphic.com/blog/higher-kinded-data/)-like
functionality by wrapping all the fields of a record in a type constructor.

But sometimes we are working with "pure" records without effects, and we just
want to get and set a field's value. In that case, the type constructor that
wraps each field will be an identity functor `I` (from
[sop-core](http://hackage.haskell.org/package/sop-core)). The -I suffixed
functions wrap and unwrap the field's value on behalf of the user.

## Alternatives

- [records-sop](http://hackage.haskell.org/package/records-sop). Another
  library based on [sop-core](http://hackage.haskell.org/package/sop-core), by
  the autor of that library. Uses a type-level list of fields. Provides record
  subtyping and accessors. The field's values are wrapped in a type
  constructor.

- [superrecord](http://hackage.haskell.org/package/superrecord). This library
  provides very efficient access at runtime because the fields are backed
  internally by an array. Uses a *sorted* type-level list of fields, to avoid
  the problems of multiple field orderings.

- [vinyl](http://hackage.haskell.org/package/vinyl). One of the oldest and more
  fully-featured extensible records libraries. Uses a type level list of
  fields. The field's values are wrapped in a type constructor.

