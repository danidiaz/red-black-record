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

module Data.RBR.Demoted where

import Data.RBR.Internal

import           Data.Proxy
import           Data.Kind
import           Data.Typeable
import           GHC.TypeLits

emptyMap :: Map String TypeRep
emptyMap = E

class DemotableColor (c :: Color) where
    demoteColor :: Proxy c -> Color

instance DemotableColor R where
    demoteColor _ = R

instance DemotableColor B where
    demoteColor _ = B

class DemotableMap (t :: Map Symbol Type) where
    demoteMap :: Proxy t -> Map String TypeRep

instance DemotableMap E where
    demoteMap _ = E

instance (DemotableColor c,
          KnownSymbol s,
          Typeable ty,
          DemotableMap l,
          DemotableMap r) 
          => DemotableMap (N c l s ty r) where
    demoteMap _ = N (demoteColor (Proxy @c)) 
                    (demoteMap (Proxy @l)) 
                    (symbolVal (Proxy @s)) 
                    (typeRep (Proxy @ty)) 
                    (demoteMap (Proxy @r))

t_insert :: Ord a => a -> v -> Map a v -> Map a v
t_insert x val s =
    N B a v z b
    where
    N _ a v z b = ins s
    ins E = N R E x val E
    ins s@(N B a y val' b)
        | x<y = t_balance (ins a) y val' b
        | x>y = t_balance a y val' (ins b)
        | otherwise = s
    ins s@(N R a y val' b)
        | x<y = N R (ins a) y val' b
        | x>y = N R a y val' (ins b)
        | otherwise = s

t_balance :: Map a v -> a -> v -> Map a v -> Map a v
t_balance (N R a x xv b) y yv (N R c z zv d) = N R (N B a x xv b) y yv (N B c z zv d)
t_balance (N R (N R a x xv b) y yv c) z zv d = N R (N B a x xv b) y yv (N B c z zv d)
t_balance (N R a x xv (N R b y yv c)) z zv d = N R (N B a x xv b) y yv (N B c z zv d)
t_balance a x xv (N R b y yv (N R c z zv d)) = N R (N B a x xv b) y yv (N B c z zv d)
t_balance a x xv (N R (N R b y yv c) z zv d) = N R (N B a x xv b) y yv (N B c z zv d)
t_balance a x xv b = N B a x xv b


t_delete :: Ord a => a -> Map a v -> Map a v
t_delete x t =
 case del t of {N _ a y yv b -> N B a y yv b; _ -> E}
 where
 del E = E
 del (N _ a y yv b)
     | x<y = delformLeft a y yv b
     | x>y = delformRight a y yv b
     | otherwise = t_app a b
 delformLeft a@(N B _ _ _ _) y yv b = t_balleft (del a) y yv b
 delformLeft a y yv b = N R (del a) y yv b

 delformRight a y yv b@(N B _ _ _ _) = t_balright a y yv (del b)
 delformRight a y yv b = N R a y yv (del b)

t_balleft :: Map a v -> a -> v -> Map a v -> Map a v
t_balleft (N R a x xv b) y yv c = N R (N B a x xv b) y yv c
t_balleft bl x xv (N B a y yv b) = t_balance bl x xv (N R a y yv b)
t_balleft bl x xv (N R (N B a y yv b) z zv c) = N R (N B bl x xv a) y yv (t_balance b z zv (t_sub1 c))

t_balright :: Map a v -> a -> v -> Map a v -> Map a v
t_balright a x xv (N R b y yv c) = N R a x xv (N B b y yv c)
t_balright (N B a x xv b) y yv bl = t_balance (N R a x xv b) y yv bl
t_balright (N R a x xv (N B b y yv c)) z zv bl = N R (t_balance (t_sub1 a) x xv b) y yv (N B c z zv bl)

t_sub1 :: Map a v -> Map a v
t_sub1 (N B a x xv b) = N R a x xv b
t_sub1 _ = error "invariance violation"

t_app :: Map a v -> Map a v -> Map a v
t_app E x = x
t_app x E = x
t_app (N R a x xv b) (N R c y yv d) =
 case t_app b c of
     N R b' z zv c' -> N R (N R a x xv b') z zv (N R c' y yv d)
     bc -> N R a x xv (N R bc y yv d)
t_app (N B a x xv b) (N B c y yv d) = 
 case t_app b c of
     N R b' z zv c' -> N R (N B a x xv b') z zv (N B c' y yv d)
     bc -> t_balleft a x xv (N B bc y yv d)
t_app a (N R b x xv c) = N R (t_app a b) x xv c
t_app (N R a x xv b) c = N R a x xv (t_app b c)

-- The original term-level code, taken from:
-- https://www.cs.kent.ac.uk/people/staff/smk/redblack/rb.html
--
-- {- Version 1, 'untyped' -}
-- data Color = R | B deriving Show
-- data RB a = E | T Color (RB a) a (RB a) deriving Show
-- 
-- {- Insertion and membership test as by Okasaki -}
-- insert :: Ord a => a -> RB a -> RB a
-- insert x s =
--  T B a z b
--  where
--  T _ a z b = ins s
--  ins E = T R E x E
--  ins s@(T B a y b)
--      | x<y = balance (ins a) y b
--      | x>y = balance a y (ins b)
--      | otherwise = s
--  ins s@(T R a y b)
--      | x<y = T R (ins a) y b
--      | x>y = T R a y (ins b)
--      | otherwise = s
-- 
-- 
-- {- balance: first equation is new,
--    to make it work with a weaker invariant -}
-- balance :: RB a -> a -> RB a -> RB a
-- balance (T R a x b) y (T R c z d) = T R (T B a x b) y (T B c z d)
-- balance (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
-- balance (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
-- balance a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
-- balance a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
-- balance a x b = T B a x b
--
-- member :: Ord a => a -> RB a -> Bool
-- member x E = False
-- member x (T _ a y b)
--  | x<y = member x a
--  | x>y = member x b
--  | otherwise = True
-- 
-- {- deletion a la SMK -}
-- delete :: Ord a => a -> RB a -> RB a
-- delete x t =
--  case del t of {T _ a y b -> T B a y b; _ -> E}
--  where
--  del E = E
--  del (T _ a y b)
--      | x<y = delformLeft a y b
--      | x>y = delformRight a y b
--             | otherwise = app a b
--  delformLeft a@(T B _ _ _) y b = balleft (del a) y b
--  delformLeft a y b = T R (del a) y b
--
--  delformRight a y b@(T B _ _ _) = balright a y (del b)
--  delformRight a y b = T R a y (del b)
-- 
-- balleft :: RB a -> a -> RB a -> RB a
-- balleft (T R a x b) y c = T R (T B a x b) y c
-- balleft bl x (T B a y b) = balance bl x (T R a y b)
-- balleft bl x (T R (T B a y b) z c) = T R (T B bl x a) y (balance b z (sub1 c))
-- 
-- balright :: RB a -> a -> RB a -> RB a
-- balright a x (T R b y c) = T R a x (T B b y c)
-- balright (T B a x b) y bl = balance (T R a x b) y bl
-- balright (T R a x (T B b y c)) z bl = T R (balance (sub1 a) x b) y (T B c z bl)
-- 
-- sub1 :: RB a -> RB a
-- sub1 (T B a x b) = T R a x b
-- sub1 _ = error "invariance violation"
-- 
-- app :: RB a -> RB a -> RB a
-- app E x = x
-- app x E = x
-- app (T R a x b) (T R c y d) =
--  case app b c of
--      T R b' z c' -> T R(T R a x b') z (T R c' y d)
--      bc -> T R a x (T R bc y d)
-- app (T B a x b) (T B c y d) = 
--  case app b c of
--      T R b' z c' -> T R(T B a x b') z (T B c' y d)
--      bc -> balleft a x (T B bc y d)
-- app a (T R b x c) = T R (app a b) x c
-- app (T R a x b) c = T R a x (app b c)

