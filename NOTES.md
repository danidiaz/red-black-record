# NOTES

## RELEVANT / RELATED LINKS

[Persistent Red Black Trees in
Haskell](https://abhiroop.github.io/Haskell-Red-Black-Tree/).
[reddit](https://www.reddit.com/r/haskell/comments/79kbog/persistent_red_black_trees_in_haskell/).

[red-black-tree: Red Black Trees implemented in Haskell](http://hackage.haskell.org/package/red-black-tree).

[Persistent Data Structures](https://www.seas.upenn.edu/~cis552/11fa/lectures/RedBlack.html)

[Deletion: The curse of the red-black tree](http://matt.might.net/papers/germane2014deletion.pdf)

[Constructing Red-Black Trees](https://pdfs.semanticscholar.org/b7eb/ce70900c26125240537ba722aeec2cf44a2e.pdf)

[Verifying Red-Black Trees](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.125.1730&rep=rep1&type=pdf)

[supperrecord](https://www.athiemann.net/2017/07/02/superrecord.html). [video](https://www.youtube.com/watch?v=Nh0XD2hPV8w).

[sop-core](http://hackage.haskell.org/package/sop-core).

[Are open sum types dual to stores with allocation?](https://twitter.com/maxsnew/status/1081603990352220168).

[Functor-generic programming](http://r6.ca/blog/20171010T001746Z.html).
[sop-core](http://hackage.haskell.org/package/sop-core) and
[streaming](http://hackage.haskell.org/package/streaming) are good examples of
functor-generic programming.

[Why doesn't TypeSynonymInstances allow partially applied type synonyms to be
used in instance
heads?](https://stackoverflow.com/questions/4922560/why-doesnt-typesynonyminstances-allow-partially-applied-type-synonyms-to-be-use)

[A Touch of Topological Quantum Computation in Haskell Pt.
II](https://www.reddit.com/r/haskell/comments/afrn47/a_touch_of_topological_quantum_computation_in/).
Type-level tree tricks.

[Declarative record migration](https://twitter.com/am_i_tom/status/1084942686975610881).

[Laziness at type
level](https://www.reddit.com/r/haskell/comments/ahbvge/laziness_at_type_level/).
"The type level evaluation order is unspecified, so it’s best avoid defining
your own control structure functions"

Improving compilation times for type family-heavy code
======================================================

Empirical observations (which might be incorrect):

- If a typeclass has an associated type family that is expensive to compute,
  and the type family is "invoked" more than once in the signature of a method
  of the typeclass, the type family seems to be executed *more than once* for
  each occurrence of that method in the code. 

    - Auxiliary type families *can* help to recover sharing in these
      computations.

    - Type synonyms *can't*. 

    - What about the "constraint trick"? I haven't checked.

I still have questions. What about functions whose implementations use these
"exensive to compile" typeclass methods, and have themselves type family
invocations in their signatures? Is the work doubled?

SO question about this: https://stackoverflow.com/questions/54298813/when-does-type-level-computation-happen-with-type-families
