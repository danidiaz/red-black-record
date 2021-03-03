{-# LANGUAGE DataKinds,
             TypeOperators,
             TypeFamilies,
             TypeApplications,
             DeriveGeneric,
             StandaloneDeriving,
             UndecidableInstances,
             KindSignatures,
             PartialTypeSignatures,
             FlexibleContexts,
             ScopedTypeVariables
#-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Main where

import Data.RBR
import qualified Data.RBR.Subset as S
import Data.RBR.Demoted (emptyMap,DemotableMap(demoteMap),t_insert,t_delete) 
import Data.SOP
import Data.SOP.NP (cpure_NP,collapse_NP)
import Data.Typeable
import Data.Proxy
import GHC.TypeLits
import Data.Kind
import GHC.Generics (Generic)

import Test.Tasty
import Test.Tasty.HUnit (testCase,Assertion,assertEqual,assertBool)


main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [ testCase "recordGetSet01" testRecordGetSet01,
                            testCase "variantInjectMatch01" testVariantInjectMatch01,
                            testCase "projectSubset01" testProjectSubset01,
                            testGroup "nominalConversion" [
                                testCase "toRecord01" testToRecord01,
                                testCase "fromRecord01" testFromRecord01,
                                testCase "toVariant01" testToVariant01,
                                testCase "toVariant02Units" testToVariant02Units,
                                testCase "fromVariant01" testFromVariant01,
                                testCase "fromVariant02Units" testFromVariant02Units
                            ],
                            testGroup "deletion" [
                                testGroup "records" [
                                    testCase "recordDeletionSingleElem" testRecordDeletionSingleElem,
                                    testCase "recordDeletionLeftElem"   testRecordDeletionLeftElem,
                                    testCase "recordDeletionRightElem"  testRecordDeletionRightElem
                                ],
                                testGroup "variants" [
                                    testCase "variantDeletionSingleElem" testVariantDeletionSingleElem,
                                    testCase "variantDeletionLeftElem" testVariantDeletionLeftElem,
                                    testCase "variantDeletionRightElem" testVariantDeletionRightElem,
                                    testCase "variantDeletion3Elem" testVariantDeletion3Elem,
                                    testCase "variantDeletionMany" testVariantDeletionMany, 
                                    testCase "variantDeletionManyB" testVariantDeletionManyB 
                                ]
                            ],
                            testGroup "typeLevelTermLvel" [
                                    testCase "tandem01" testInTandem01,
                                    testCase "tandem02" testInTandem02,
                                    testCase "tandem03" testInTandem03,
                                    testCase "tandem04" testInTandem04
                            ],
                            testGroup "polyKindedMap" [
                                    testCase "polyKinded01" polyKinded01,
                                    testCase "polyKinded02" polyKinded02
                            ],
                            testGroup "transformations" [
                                    testCase "testLiftA_Record" cliftA2_01,
                                    testCase "testLiftA2_Record" cliftA2_02
                            ]
                          ]


testRecordGetSet01 :: Assertion
testRecordGetSet01 = do
    let r = insertI @"bfoo" 'c'
          . insertI @"bbar" True
          . insertI @"bbaz" (1::Int)
          . insertI @"afoo" 'd'
          . insertI @"abar" False
          . insertI @"abaz" (2::Int)
          . insertI @"zfoo" 'x'
          . insertI @"zbar" False
          . insertI @"zbaz" (4::Int)
          . insertI @"dfoo" 'z'
          . insertI @"dbar" True
          . insertI @"dbaz" (5::Int)
          . insertI @"fbaz" (6::Int)
          $ unit
        s = setFieldI @"fbaz" 9 (setFieldI @"zfoo" 'k' r)
    assertEqual "bfoo" (getFieldI  @"bfoo" s) 'c'
    assertEqual "bbar" (getFieldI  @"bbar" s) True
    assertEqual "bbaz" (getFieldI  @"bbaz" s) (1::Int)
    assertEqual "afoo" (getFieldI  @"afoo" s) 'd'
    assertEqual "abar" (getFieldI  @"abar" s) False
    assertEqual "abaz" (getFieldI  @"abaz" s) (2::Int)
    assertEqual "zfoo" (getFieldI  @"zfoo" s) 'k'
    assertEqual "zbar" (getFieldI  @"zbar" s) False
    assertEqual "zbaz" (getFieldI  @"zbaz" s) (4::Int)
    assertEqual "dfoo" (getFieldI  @"dfoo" s) 'z'
    assertEqual "dbar" (getFieldI  @"dbar" s) True
    assertEqual "dbaz" (getFieldI  @"dbaz" s) (5::Int)
    assertEqual "fbaz" (getFieldI  @"fbaz" s) (9::Int)
    return ()

type Tree01 = FromList [ '("bfoo",Char),
                         '("bbar",Bool),
                         '("bbaz",Int),
                         '("afoo",Char),
                         '("abar",Bool),
                         '("abaz",Int),
                         '("zfoo",Char),
                         '("zbar",Bool),
                         '("zbaz",Int),
                         '("dfoo",Char),
                         '("dbar",Bool),
                         '("dbaz",Int),
                         '("fbaz",Int),
                         '("kgoz",Int) ]

testVariantInjectMatch01 :: Assertion
testVariantInjectMatch01 = do
    let r0  =  injectI @"bfoo" @Tree01 'c'
        r1  =  injectI @"bbar" @Tree01 True
        r2  =  injectI @"bbaz" @Tree01 (1::Int)
        r3  =  injectI @"afoo" @Tree01 'd'
        r4  =  injectI @"abar" @Tree01 False
        r5  =  injectI @"abaz" @Tree01 (2::Int)
        r6  =  injectI @"zfoo" @Tree01 'x'
        r7  =  injectI @"zbar" @Tree01 False
        r8  =  injectI @"zbaz" @Tree01 (4::Int)
        r9  =  injectI @"dfoo" @Tree01 'z'
        r10 =  injectI @"dbar" @Tree01 True
        r11 =  injectI @"dbaz" @Tree01 (5::Int)
        r12 =  injectI @"fbaz" @Tree01 (6::Int)
        r13 =  injectI @"kgoz" @Tree01 (9::Int)
    assertEqual "bfoo" (matchI  @"bfoo" r0 ) $ Just 'c'
    assertEqual "bbar" (matchI  @"bbar" r1 ) $ Just True
    assertEqual "bbaz" (matchI  @"bbaz" r2 ) $ Just (1::Int)
    assertEqual "afoo" (matchI  @"afoo" r3 ) $ Just 'd'
    assertEqual "abar" (matchI  @"abar" r4 ) $ Just False
    assertEqual "abaz" (matchI  @"abaz" r5 ) $ Just (2::Int)
    assertEqual "zfoo" (matchI  @"zfoo" r6 ) $ Just 'x'
    assertEqual "zbar" (matchI  @"zbar" r7 ) $ Just False
    assertEqual "zbaz" (matchI  @"zbaz" r8 ) $ Just (4::Int)
    assertEqual "dfoo" (matchI  @"dfoo" r9 ) $ Just 'z'
    assertEqual "dbar" (matchI  @"dbar" r10) $ Just True
    assertEqual "dbaz" (matchI  @"dbaz" r11) $ Just (5::Int)
    assertEqual "fbaz" (matchI  @"fbaz" r12) $ Just (6::Int)
    assertEqual "kgoz" (matchI  @"kgoz" r13) $ Just (9::Int)
    return ()


testProjectSubset01 :: Assertion
testProjectSubset01 = do
    let r = insertI @"foo" 'c'
          . insertI @"bar" True
          . insertI @"baz" (1::Int)
          $ unit
        s = S.projectSubset @(FromList '[ '("bar",_),
                                          '("baz",_) ]) r
        bar = getFieldI @"bar" s
        baz = getFieldI @"baz" s
    assertEqual "bar" bar True
    assertEqual "baz" baz 1

data Person = Person { name :: String, age :: Int, whatever :: Char } deriving (Generic,Eq,Show)

instance ToRecord Person
instance FromRecord Person

testToRecord01 :: Assertion
testToRecord01 = do
    let r = toRecord (Person "Foo" 50 'z')
    assertEqual "name" "Foo" (getFieldI @"name" r)
    assertEqual "age" 50 (getFieldI @"age" r)
    assertEqual "whatever" 'z' (getFieldI @"whatever" r)

testFromRecord01 :: Assertion
testFromRecord01 = do
    let r = insertI @"name" "Foo"
          . insertI @"age" 50
          . insertI @"whatever" 'z'
          $ unit
    assertEqual "person" (Person "Foo" 50 'z') (fromRecord r)

data Variant01 = Variant01A Int
               | Variant01B Char
               | Variant01C Bool
               | Variant01D Bool
               deriving (Generic,Eq,Show)

instance ToVariant Variant01
instance FromVariant Variant01

testToVariant01 :: Assertion
testToVariant01 = do
    let val1 = Variant01A 0
        val2 = Variant01B 'c'
        val3 = Variant01C True
        cases = addCaseI @"Variant01A" (const 'F')
              . addCaseI @"Variant01B" id
              . addCaseI @"Variant01C" (const 'F')
              . addCaseI @"Variant01D" (const 'F')
              $ unit
        variant = toVariant (Variant01B 'T')
    -- Eliminate would also work because the order of the eliminators is the
    -- same as the order of the cases.
    assertEqual "T" 'T' (S.eliminateSubset cases variant)

data Variant02Unit = 
      Variant02A 
    | Variant02B Char 
    | Variant02C deriving (Generic,Eq,Show)

instance ToVariant Variant02Unit
instance FromVariant Variant02Unit

testToVariant02Units :: Assertion
testToVariant02Units = do
    let cases = addCaseI @"Variant02A" (const 'a')
              . addCaseI @"Variant02B" id
              . addCaseI @"Variant02C" (const 'c')
              $ unit
        variantA = toVariant Variant02A
        variantB = toVariant (Variant02B 'b')
        variantC = toVariant Variant02C
    -- Eliminate would also work because the order of the eliminators is the
    -- same as the order of the cases.
    assertEqual "a" 'a' (S.eliminateSubset cases variantA)
    assertEqual "b" 'b' (S.eliminateSubset cases variantB)
    assertEqual "c" 'c' (S.eliminateSubset cases variantC)

testFromVariant01 :: IO ()
testFromVariant01 = do
    let val1 = fromVariant (injectI @"Variant01A" 1)
        val2 = fromVariant (injectI @"Variant01B" 'z')
        val3 = fromVariant (injectI @"Variant01C" True)
        val4 = fromVariant (injectI @"Variant01D" False)
    assertEqual "Variant01A" val1 (Variant01A 1)
    assertEqual "Variant01B" val2 (Variant01B 'z')
    assertEqual "Variant01C" val3 (Variant01C True)
    assertEqual "Variant01D" val4 (Variant01D False)
 
testFromVariant02Units :: IO ()
testFromVariant02Units = do
    let val1 = fromVariant (injectI @"Variant02A" ())
        val2 = fromVariant (injectI @"Variant02B" 'b')
        val3 = fromVariant (injectI @"Variant02C" ())
    assertEqual "Variant02A" val1 Variant02A
    assertEqual "Variant02B" val2 (Variant02B 'b')
    assertEqual "Variant02C" val3 Variant02C

testRecordDeletionSingleElem :: IO ()
testRecordDeletionSingleElem = do
    let r = insertI @"bar" False
          . insertI @"foo" 'c'
          . delete @"foo" @Bool 
          . insertI @"foo" True
          $ unit
    assertEqual "foo" (getFieldI  @"foo" r) 'c'
    assertEqual "bar" (getFieldI  @"bar" r) False

testVariantDeletionSingleElem :: IO ()
testVariantDeletionSingleElem = do
    let v = injectI @"foo" @(FromList '[ '("foo",Bool) ]) False
        Right r = winnowI @"foo" @Bool v
    assertEqual "foo" False r

testRecordDeletionRightElem :: IO ()
testRecordDeletionRightElem = do
    let r = delete @"foo" @Char
          . insertI @"foo" 'f'
          . insertI @"bar" 'b'
          $ unit
    assertEqual "bar" (getFieldI  @"bar" r) 'b'

testVariantDeletionRightElem :: IO ()
testVariantDeletionRightElem = do
    let v = injectI @"foo" @(FromList '[ '("foo",Bool), '("bar",Char) ]) False
        Left v' = winnowI @"bar" @Char v
        Right r = winnowI @"foo" @Bool v'
    assertEqual "foo" False r

testRecordDeletionLeftElem :: IO ()
testRecordDeletionLeftElem = do
    let r = delete @"bar" @Char
          . insertI @"foo" 'f'
          . insertI @"bar" 'b'
          $ unit
    assertEqual "foo" (getFieldI  @"foo" r) 'f'

testVariantDeletionLeftElem :: IO ()
testVariantDeletionLeftElem = do
    let v = injectI @"bar" @(FromList '[ '("foo",Bool), '("bar",Char) ]) 'b'
        Left v' = winnowI @"foo" @Bool v
        Right r = winnowI @"bar" @Char v'
    assertEqual "bar" 'b' r

type TreeX3 = FromList [ '("bfoo",Char),
                         '("bbar",Bool),
                         '("bbaz",Int)  ]

testVariantDeletion3Elem :: IO ()
testVariantDeletion3Elem = do
    let v = injectI @"bbaz" @TreeX3 1
        Right r = winnowI @"bbaz" @Int v
    assertEqual "bbaz" 1 r


type Tree02 = FromList [ 
                         '("bfoo",Char),
                         '("bbar",Bool),
                         '("bbaz",Int),
                         '("afoo",Char),
                         '("abar",Bool),
                         '("abaz",Int),
                         '("zfoo",Char),
                         '("zbar",Bool),
                         '("zbaz",Int),
                         '("dfoo",Char),
                         '("dbar",Bool),
                         '("dbaz",Int),
                         '("fbaz",Int),
                         '("kgoz",Int) 
                         ]

testVariantDeletionMany :: IO ()
testVariantDeletionMany = do
    let a00 = injectI @"bfoo" @Tree02 'z'
        Left a02 = winnowI @"bbar" @Bool a00
        Left a03 = winnowI @"bbaz" @Int a02
        Left a04 = winnowI @"afoo" @Char a03
        Left a05 = winnowI @"abar" @Bool a04
        Left a06 = winnowI @"abaz" @Int a05
        Left a07 = winnowI @"zfoo" @Char a06
        Left a08 = winnowI @"zbar" @Bool a07
        Left a09 = winnowI @"zbaz" @Int a08
        Left a10 = winnowI @"dfoo" @Char a09
        Left a11 = winnowI @"dbar" @Bool a10
        Left a12 = winnowI @"dbaz" @Int a11
        Left a13 = winnowI @"fbaz" @Int a12
        Left a14 = winnowI @"kgoz" @Int a13
        Right a  = winnowI @"bfoo" @Char a14
    assertEqual "bfoo" a 'z'
    return ()

type Tree02b = FromList [ 
                         '("bfoo",Char),
                         '("bbar",Bool),
                         '("bbaz",Int),
                         '("afoo",Char),
                         '("abar",Bool),
                         '("abaz",Int),
                         '("zfoo",Char),
                         '("zbar",Bool),
                         '("zbaz",Int),
                         '("dfoo",Char),
                         '("dbar",Bool),
                         '("dbaz",Int),
                         '("fbaz",Int),
                         '("kgoz",Int) 
                         ]

testVariantDeletionManyB :: IO ()
testVariantDeletionManyB = do
    let a00 = injectI @"bfoo" @Tree02b 'z'
        a00' = widen @"ggg" @Char a00
        Left a02 = winnowI @"bbar" @Bool a00
        Left a03 = winnowI @"bbaz" @Int a02
        Left a04 = winnowI @"afoo" @Char a03
        Left a05 = winnowI @"abar" @Bool a04
        Left a06 = winnowI @"abaz" @Int a05
        a06b = widen @"bbb" @Int a06
        Left a07 = winnowI @"zfoo" @Char a06b
        Left a08 = winnowI @"zbar" @Bool a07
        Left a09 = winnowI @"zbaz" @Int a08
        Left a10 = winnowI @"dfoo" @Char a09
        Left a10b = winnowI @"zzz" @Float a10 -- non-existent entry
        Right m = winnowI @"bfoo" @Char a10b
        Left a11 = winnowI @"dbar" @Bool a10b
        Left a12 = winnowI @"dbaz" @Int a11
        Left a13 = winnowI @"fbaz" @Int a12
        Left a14 = winnowI @"kgoz" @Int a13
        Left a15 = winnowI @"ggg"  @Char a14
        Right a  = winnowI @"bfoo" @Char a15
    assertEqual "bfoo" m 'z'
    assertEqual "bfoo" a 'z'
    return ()

type Actions01 = [Act In "f1" Bool,
                  Act In "f2" Char,
                  Act In "f3" Float,
                  Act In "f4" (Int -> Int),
                  Act In "f5" Bool,
                  Act In "f6" Char,
                  Act In "f7" String,
                  Act In "f8" (Char -> Char),
                  Act In "f9" Bool,
                  Act In "f10" Char,
                  Act In "f11" Float
                 ]

testInTandem01 :: IO ()
testInTandem01 = assertEqual "" (demoteMap (Proxy @(Perform Actions01))) (perform (demoteActions (Proxy @Actions01)))
    
type Actions02 = [Act In "f11" Bool,
                  Act In "f10" Int,
                  Act In "f9" Char,
                  Act In "f8" (Char -> Char),
                  Act In "f7" Int,
                  Act In "f6" Char,
                  Act In "f5" Float,
                  Act In "f4" Int,
                  Act In "f3" (Char -> Int),
                  Act In "f2" Bool,
                  Act In "f1" Char
                 ]

testInTandem02 :: IO ()
testInTandem02 = assertEqual "" (demoteMap (Proxy @(Perform Actions02))) (perform (demoteActions (Proxy @Actions02)))
    
type Actions03 = [Act In "ff1" Bool,
                  Act In "af2" Char,
                  Act In "wf3" Int,
                  Act In "uf4" Bool,
                  Act In "uf5" Char,
                  Act In "af6" Int,
                  Act In "pf7" Bool,
                  Act De "qf5" Char,
                  Act De "bf2" Char,
                  Act In "hf8" (Int -> Int),
                  Act De "mf4" Bool,
                  Act In "af9" Bool,
                  Act In "yf10" Char,
                  Act In "mf11" String,
                  Act De "zf3" Int
                 ]

testInTandem03 :: IO ()
testInTandem03 = assertEqual "" (demoteMap (Proxy @(Perform Actions03))) (perform (demoteActions (Proxy @Actions03)))


type Actions04 = [Act In "ef1" Bool,
                  Act In "ef2" Char,
                  Act De "ef3" Int, -- we can delete entries that don't exist
                  Act In "af3" Int,
                  Act De "af3" Int, 
                  Act In "kf4" Bool,
                  Act De "kf4" Bool,
                  Act In "pf5" Char,
                  Act De "pf5" Char,
                  Act In "zf6" Int,
                  Act De "zf6" Int,
                  Act In "ff7" Bool,
                  Act De "ff7" Bool,
                  Act In "rf5" Char,
                  Act De "rf5" Char,
                  Act De "ef2" Char,
                  Act In "lf8" (Int -> Int),
                  Act In "lll" Bool,
                  Act De "lll" Bool,
                  Act De "lf8" (Int -> Int),
                  Act In "ef1" Bool, -- we can re-add the exact same entry
                  Act De "ef1" Bool
                 ]

testInTandem04 :: IO ()
testInTandem04 = assertEqual "" (demoteMap (Proxy @(Perform Actions04))) (perform (demoteActions (Proxy @Actions04)))


-- sequences of actions for tests
--
--
data InsertOrDelete = In
                    | De 
                    deriving (Show, Eq)

class DemotableInsertOrDelete (iod :: InsertOrDelete) where
    demoteIoD :: Proxy iod -> InsertOrDelete

instance DemotableInsertOrDelete 'In where
    demoteIoD _ = In

instance DemotableInsertOrDelete 'De where
    demoteIoD _ = De

data Action s t = Act InsertOrDelete s t deriving (Show, Eq)

class DemotableAction (a :: Action Symbol Type) where 
    demoteAction :: Proxy a -> Action String TypeRep

instance (DemotableInsertOrDelete iod, KnownSymbol s, Typeable t) => DemotableAction (Act iod s t) where
    demoteAction _ = Act (demoteIoD (Proxy @iod)) 
                         (symbolVal (Proxy @s)) 
                         (typeRep (Proxy @t))

demoteActions :: forall as. All DemotableAction as => Proxy (as :: [Action Symbol Type]) -> [Action String TypeRep] 
demoteActions _ = collapse_NP $ cpure_NP @_ @as (Proxy @DemotableAction) conjure
    where 
    conjure :: forall a. DemotableAction a => K (Action String TypeRep) a
    conjure = K (demoteAction (Proxy @a))

type family Perform (as :: [Action Symbol Type]) :: Map Symbol Type where
    Perform (Act In s v ': as) = Insert s v (Perform as)
    Perform (Act De s v ': as) = Delete s v (Perform as)
    Perform '[]                = Empty

perform :: [Action String TypeRep] -> Map String TypeRep
perform = foldr (\(Act iod s v) t -> case iod of In -> t_insert s v t
                                                 De -> t_delete s t) 
                emptyMap

--
--
--

type PolyKinded01 = FromList '[ '("aaa","v1"),
                                '("bbb","v2"), 
                                '("ccc","v3"), 
                                '("ddd","v4"), 
                                '("eee","v5")  ]

polyKindedRecord01 :: Record Proxy PolyKinded01
polyKindedRecord01 = 
               insert @"aaa" (Proxy @"v1")
             . insert @"bbb" (Proxy @"v2")
             . insert @"ccc" (Proxy @"v3")
             . insert @"ddd" (Proxy @"v4")
             . insert @"eee" (Proxy @"v5")
             $ unit

polyKinded01 :: Assertion
polyKinded01 = do
    let r = insert @"aaa" (Proxy @"v1")
          . insert @"bbb" (Proxy @"v2")
          . insert @"ccc" (Proxy @"v3")
          . insert @"ddd" (Proxy @"v4")
          . insert @"eee" (Proxy @"v5")
          . insert @"abb" (Proxy @"v2")
          . insert @"acc" (Proxy @"v3")
          . insert @"add" (Proxy @"v4")
          . insert @"aee" (Proxy @"v5")
          $ unit
        proxy :: Proxy "v2"
        proxy = getField @"abb" r
    return ()

polyKinded02 :: Assertion
polyKinded02 = do
    let r = demoteEntries @PolyKinded01
        K (_,trep) = getField @"eee" r
    assertEqual "" trep (typeRep (Proxy @"v5"))
    return ()


cliftA2_01 :: Assertion
cliftA2_01 = do
    let r = insertI @"foo" 'c'
          . insertI @"bar" True
          . insertI @"baz" (1::Int)
          $ unit
        r' = cliftA_Record (Proxy @(KeyValueConstraints KnownSymbol Show)) (\(I x) -> K (show x)) r
        K foo = getField @"foo" r'
        K bar = getField @"bar" r'
        K baz = getField @"baz" r'
    assertEqual "foo" foo "'c'"
    assertEqual "bar" bar "True"
    assertEqual "baz" baz "1"

cliftA2_02 :: Assertion
cliftA2_02 = do
    let r = insertI @"foo" 'c'
          . insertI @"bar" True
          . insertI @"baz" (1::Int)
          $ unit
        r' = cliftA2_Record (Proxy @(KeyValueConstraints KnownSymbol Show)) (\(I x) (I y) -> K (show x ++ show y)) r r
        K foo = getField @"foo" r'
        K bar = getField @"bar" r'
        K baz = getField @"baz" r'
    assertEqual "foo" foo "'c''c'"
    assertEqual "bar" bar "TrueTrue"
    assertEqual "baz" baz "11"
