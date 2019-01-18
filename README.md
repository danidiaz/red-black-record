red-black-record
================

What's this?
------------

A library that provides extensible records and variants, both indexed by a
type-level [red-black](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree)
tree that maps `Symbol` keys to `Type`s. The keys correspond to fields names in
records, and to branch names in variants. Many record functions have their
variant mirror-images and viceversa.

Each value type in a field or branch comes wrapped in a type constructor of
kind `Type -> Type`. Typically, it will be an [identity
functor](http://hackage.haskell.org/package/sop-core-0.4.0.0/docs/Data-SOP.html#t:I),
but it can also be `Maybe` or some other `Applicative` for parsing, validation
and so on.

If we forget about the keys and only keep the values, records are isomorphic to
[n-ary unlabeled
products](http://hackage.haskell.org/package/sop-core-0.4.0.0/docs/Data-SOP.html#t:NP),
and variants are isomorphic to [n-ary unlabeled
sums](http://hackage.haskell.org/package/sop-core-0.4.0.0/docs/Data-SOP.html#t:NS).
The [sop-core](http://hackage.haskell.org/package/sop-core) library provides
such unlabeled types, along with a rich API for manipulating them. Instead of
reinventing the wheel, red-black-record defines conversion functions to
facilitate working in the "unlabeled" world and then coming back to records and
variants.

There is another world towards which bridges must be built: the everyday
Haskell world of conventional records and sums. In fact, one of the motivations
of extensible records and variants is to serve as "generalized" versions of
vanilla data types. Advanced use cases can rely on these generalized versions,
thereby avoiding intrusive changes to the original types. red-black-record
provides conversion typeclasses with default implementations by way of
[`GHC.Generic`](http://hackage.haskell.org/package/base-4.12.0.0/docs/GHC-Generics.html).

For examples on how to use the library, check the haddocks for the
`Data.RBR.Examples` module.

FAQ
---

### What extensions do I need to use this library?

- `DataKinds`.

- `TypeApplications` to be able to specify field and branch names.

- `TypeFamilies`.

- `FlexibleContexts`.

- `DeriveGeneric` for interfacing with normal records.

- `PartialTypeSignatures` for hiding complex tree types.

### My type signatures are getting big and scary because of those type-level trees. What to do?

The
[`-XPartialTypeSignatures`](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html?#extension-PartialTypeSignatures)
extension can help with that, in combination with the
[-Wno-partial-type-signatures](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/using-warnings.html#ghc-flag--Wpartial-type-signatures)
GHC flag that disables the warning message emitted when the underscore is
encountered in a signature.

The flag can be set globally in the
[ghc-options](https://www.haskell.org/cabal/users-guide/developing-packages.html?#pkg-field-ghc-options)
section of the .cabal file, and also for particular modules with the
[OPTIONS_GHC](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html?highlight=options_ghc#options-ghc-pragma)
file-header pragma.

### The `Show` instance for record doesn't show any field names.

The field names exist only at the type level. Also, the `Show` instance uses
n-ary products and sums from
[sop-core](http://hackage.haskell.org/package/sop-core), which do not have
field labels.

For fancier output, use the "pretty-show" functions instead.

### Working with two records, I'm getting errors about incompatible types even as both records have the exact same fields.

Alas, the order of insertion in the type-level tree matters :( Different
insertion orders can produce structurally different trees, even as they encode
the same symbol-to-type map.

As a workaround, one can use the `-Subset` functions to convert between
equivalent structures.

### I can't insert into a record when a field with the same name but different type already exists. Why not simply overwrite it?

That limitation was intentional, because allowing it would make impossible to
implement of `widen` for `Variant`. When/if key deletion gets implemented
type-level tree, one solution would be to explicitly delete the field and then
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

### What's the deal with all those -Subset suffixed versions of functions?

These functions target multiple fields or branches at the same time. They can
be used to build lawful lenses and prisms over fragmenst of a structure.

They can also be used to convert between type-level trees that have the same
entries but different structure.

### I want a version of "match" that when it fails returns a variant with the unmatched cases.

That isn't implemented (yet). It would require key deletion on the type-level
tree.

Inspirations
------------

- The code for the red-black tree has been lifted from ["Persistent Red Black
  Trees in Haskell"](https://abhiroop.github.io/Haskell-Red-Black-Tree/).

- Besides depending on sop-core, I have copied and adapted code from it. In
  particular the `KeysValuessAll` typeclass is a version of the `All` typeclass
  from sop-core. 

- [Surgery for data
  types](https://blog.poisson.chat/posts/2018-11-26-type-surgery.html).
  [reddit](https://www.reddit.com/r/haskell/comments/a0gi4z/surgery_for_data_types/).

Alternatives
------------

- [generics-sop](http://hackage.haskell.org/package/generics-sop) and
  [records-sop](http://hackage.haskell.org/package/records-sop). Like
  red-black-record, both of these libraries build upon sop-core. They are in
  fact written by the same author of sop-core. generics-sop can provide
  sum-of-products representations of any datatype with a Generic instance
  (red-black-record is more limited, it only converts types that fit the named
  record or variant mold—so no types with anonymous fields for example). 
  
  If you don't need to explicitly target *individual* fields in the generic
  representation, you'll be better off using generics-sop instead of
  red-black-record. 
  
  On top of generics-sop, records-sop provides named field accessors and record
  subtyping based on a type-level list of fields (unlike the type-level tree
  used by red-black-record). It doesn't seem to provide variants.

- [superrecord](http://hackage.haskell.org/package/superrecord). This library
  provides very efficient field access at runtime because the fields are backed
  internally by an array. Uses a *sorted* type-level list of fields, to avoid
  the problems of multiple orderings of the same fields.

- [vinyl](http://hackage.haskell.org/package/vinyl). One of the oldest and more
  fully-featured extensible records libraries. Uses a type level list of
  fields. The fields' values are wrapped in a type constructor, like in
  sop-core. The records seem to use an auxiliary sum type that serves as a
  "code" for the fields.

- [HTree](https://github.com/i-am-tom/learn-me-a-haskell#htree). Another
  implementation of extensible records using type-level red-black trees.

- [megarecord](https://github.com/jvanbruegge/Megarecord). Seems to be a
  proof-of-concept for a future [row polymorphism
  extension](https://github.com/ghc-proposals/ghc-proposals/pull/180) for
  Haskell.

- [generic-data-surgery](https://hackage.haskell.org/package/generic-data-surgery).
  Lots of useful machinery for manipulating generic representations of
  dataytpes.

- [Coxswain](https://ghc.haskell.org/trac/ghc/wiki/Plugins/TypeChecker/RowTypes/Coxswain).

