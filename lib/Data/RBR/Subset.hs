{-# LANGUAGE DataKinds,
             TypeOperators,
             ConstraintKinds,
             PolyKinds,
             TypeFamilies,
             GADTs,
             MultiParamTypeClasses,
             FunctionalDependencies,
             FlexibleInstances,
             FlexibleContexts,
             UndecidableInstances,
             UndecidableSuperClasses,
             TypeApplications,
             ScopedTypeVariables,
             AllowAmbiguousTypes,
             ExplicitForAll,
             RankNTypes, 
             DefaultSignatures,
             PartialTypeSignatures,
             LambdaCase,
             EmptyCase 
#-}
{-#  OPTIONS_GHC -Wno-partial-type-signatures  #-}
module Data.RBR.Subset (Subset) where

import Data.Proxy
import Data.Kind
import Data.Monoid (Endo(..))
import Data.List (intersperse)
import Data.Foldable (asum)
import GHC.TypeLits
import Data.SOP (I(..),K(..),unI,unK,NP(..),NS(..),All,SListI,type (-.->)(Fn,apFn),mapKIK,(:.:)(..),Top)

import Data.RBR.Internal hiding 
    ( 
       ProductlikeSubset,
       fieldSubset,
       projectSubset,
       getFieldSubset,
       setFieldSubset,
       modifyFieldSubset,
       SumlikeSubset,
       branchSubset,
       injectSubset,
       matchSubset,
       eliminateSubset
   )


type Subset (subset :: Map Symbol q) (whole :: Map Symbol q) = KeysValuesAll (PresentIn whole) subset


{- | Like 'field', but targets multiple fields at the same time 

-}
fieldSubset :: forall subset whole f. (Maplike subset, Subset subset whole) 
            => Record f whole -> (Record f subset -> Record f whole, Record f subset)
fieldSubset r = 
    (,)
    (let goset :: forall left k v right color. (PresentIn whole k v, KeysValuesAll (PresentIn whole) left, 
                                                                     KeysValuesAll (PresentIn whole) right) 
               => Record (SetField f (Record f whole)) left 
               -> Record (SetField f (Record f whole)) right 
               -> Record (SetField f (Record f whole)) (N color left k v right)
         goset left right = Node left (SetField (\v w -> fst (field @k @whole w) v)) right
         setters :: Record (SetField f (Record f whole)) _ = cpara_Map (Proxy @(PresentIn whole)) unit goset
         appz (SetField func) fv = K (Endo (func fv))
      in \toset -> appEndo (collapse'_Record (liftA2_Record appz setters toset)) r)
    (let goget :: forall left k v right color. (PresentIn whole k v, KeysValuesAll (PresentIn whole) left, 
                                                                     KeysValuesAll (PresentIn whole) right) 
               => Record f left 
               -> Record f right 
               -> Record f (N color left k v right)
         goget left right = Node left (project @k @whole r) right
      in cpara_Map (Proxy @(PresentIn whole)) unit goget)


{- | Like 'branch', but targets multiple branches at the same time.
-}
branchSubset :: forall subset whole f. (Maplike subset, Maplike whole, Subset subset whole)
             => (Variant f whole -> Maybe (Variant f subset), Variant f subset -> Variant f whole)
branchSubset = 
    let inj2case = \adapt (VariantInjection vif) -> Case $ \fv -> adapt (vif fv) -- (\fv -> adapt (fromNS @t (unK (apFn fn fv))))
        -- The intuition is that getting the setter and the getter together might be faster at compile-time.
        -- The intuition might be wrong.
        subs :: forall f. Record f whole -> (Record f subset -> Record f whole, Record f subset)
        subs = fieldSubset @subset @whole
     in
     (,)
     (let injs :: Record (Case f (Maybe (Variant f subset))) subset 
          injs = liftA_Record (inj2case Just) (injections_Variant @subset)
          -- fixme: possibly inefficient?
          wholeinjs :: Record (Case f (Maybe (Variant f subset))) whole 
          wholeinjs = pure_Record (Case (\_ -> Nothing))
          mixedinjs = fst (subs wholeinjs) injs
       in eliminate_Variant mixedinjs)
     (let wholeinjs :: Record (Case f (Variant f whole)) whole
          wholeinjs = liftA_Record (inj2case id) (injections_Variant @whole)
          injs = snd (subs wholeinjs)
       in eliminate_Variant injs)

