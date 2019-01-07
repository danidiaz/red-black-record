- Clarify the need for "KeysAllF"

- Turn KeysAll into something like KeysValuesAll that takes a two-place constraint.
    - Reimplement KeysAll in terms of KeysValuesAll (possible?)
    - It might be useful for expressing things like "All the key-value pairs in
      this record are present in this other record".

- Interaction with normal records
    - NominalRecord, NominalSum?

- Implement deletion in the type-level tree?

    - It will be harder than insertion.
    - It would allow things like changing the type of a field
    by deleting and re-inserting it. Insertion doesn't 
    support that.
    - Perhaps it would allow to progressively "expand"
    a Variant-consuming function with new cases, but I'm not sure.

- Implement "project a subset of the fields".
  Will require the constraint that all the keys in one tree
  are keys in the original tree.

- Implement "handleAll"


