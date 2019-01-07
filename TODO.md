- Clarify the need for "KeysAllF"

- Turn KeysAll into something like KeysValuesAll that takes a two-place constraint.
    - Reimplement KeysAll in terms of KeysValuesAll (possible?)
    - It might be useful for expressing things like "All the key-value pairs in
      this record are present in this other record".

- Interaction with normal records
    - NominalRecord, NominalSum?


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
    toVariant x = case x of Bar1 b -> injectI @"Bar1" b
                            Bar2 c -> injectI @"Bar2" c
    fromVariant v = 
        let (_,matchBar1) = injection @"Bar1"
            (_,matchBar2) = injection @"Bar2"
         in case matchBar1 v of
               Just (I b) -> Bar1 b
               Nothing -> case matchBar2 v of
                    Just (I c) -> Bar2 c
                    Nothing -> error "can't happen"
            
