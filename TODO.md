- Clarify the need for "KeysAllF"

- Turn KeysAll into something like KeysValuesAll that takes a two-place constraint.
    - Reimplement KeysAll in terms of KeysValuesAll (possible?)
    - It might be useful for expressing things like "All the key-value pairs in
      this record are present in this other record".

- Interaction with normal records
    - NominalRecord, NominalSum?

- Add "match" and "matchI" functions.

data Foo = Foo { name :: String, age :: Int } deriving Show

instance NominalRecord Foo where
    type RecordCode Foo = Insert "name" String (Insert "age" Int E)
    toRecord r = insertI @"name" (name r) 
               . insertI @"age" (age r)
               $ unit
    fromRecord r = Foo (projectI @"name" r) (projectI @"age" r)

data Bar = Bar1 Bool
         | Bar2 Char deriving Show

instance NominalSum Bar where
    type SumCode Bar = Insert "Bar1" Bool (Insert "Bar2" Char E)
    toVariant x = 
        case x of Bar1 b -> injectI @"Bar1" b
                  Bar2 c -> injectI @"Bar2" c
    fromVariant v = 
        case matchI @"Bar1" v of
           Just (I b) -> Bar1 b
           Nothing -> case matchI @"Bar2" v of
                Just (I c) -> Bar2 c
                Nothing -> error "can't happen"
            
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

