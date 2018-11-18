module Data.Heap.Binomial where

import Data.Kind
import Numeric.Binary
import Numeric.Peano

data Tree n a = Root a (Node n a)

data Node n a where
    Nil  :: Node Z a
    (:<) :: Tree n a -> Node n a -> Node ('S n) a

mergeTree :: Ord a => Tree n a -> Tree n a -> Tree (S n) a
mergeTree xr@(Root x xs) yr@(Root y ys)
  | x <= y    = Root x (yr :< xs)
  | otherwise = Root y (xr :< ys)

data Binomial (x :: ℕ) (xs :: [ℕ]) (a :: Type) where
    Empty :: Binomial n '[] a
    Cons  :: Nest x y ys a -> Binomial x (y : ys) a

data Nest x y ys a where
    Odd  :: Tree n a -> Binomial ('S n) xs a -> Nest n Z xs a
    Even :: Nest (S x) y ys a -> Nest x (S y) ys a

merge :: Ord a => Binomial x xs a -> Binomial x ys a -> Binomial x (Add xs ys) a
merge Empty ys = ys
merge xs Empty = xs
merge (Cons xs) (Cons ys) = Cons (mergeNest xs ys)

mergeNest
    :: Ord a
    => Nest x y ys a
    -> Nest x z zs a
    -> Nest x (AddFst' y ys z zs) (AddSnd' y ys z zs) a
mergeNest (Even xs)         (Even ys)         = Even (mergeNest xs ys)
mergeNest (Odd x Empty)     (Even ys)         = Odd x (Cons ys)
mergeNest (Odd x (Cons xs)) (Even ys)         = Odd x (Cons (mergeNest xs ys))
mergeNest (Even xs)         (Odd y (Cons ys)) = Odd y (Cons (mergeNest xs ys))
mergeNest (Even xs)         (Odd y Empty)     = Odd y (Cons xs)
mergeNest (Odd x Empty)     (Odd y Empty)     = Even (Odd (mergeTree x y) Empty)
mergeNest (Odd x (Cons xs)) (Odd y (Cons ys)) = Even (mergeCarryNest (mergeTree x y) xs ys)
mergeNest (Odd x (Cons xs)) (Odd y Empty)     = Even (carryOneNest (mergeTree x y) xs)
mergeNest (Odd x Empty)     (Odd y (Cons ys)) = Even (carryOneNest (mergeTree x y) ys)

mergeCarry
    :: Ord a
    => Tree x a
    -> Binomial x xs a
    -> Binomial x ys a
    -> Binomial x (AddCin xs ys) a
mergeCarry t Empty ys = carryOne t ys
mergeCarry t xs Empty = carryOne t xs
mergeCarry t (Cons xs) (Cons ys) = Cons (mergeCarryNest t xs ys)


mergeCarryNest
    :: Ord a
    => Tree n a
    -> Nest n x xs a
    -> Nest n y ys a
    -> Nest n (AddCinFst' x xs y ys) (AddCinSnd' x xs y ys) a
mergeCarryNest t (Even  xs) (Even  ys) = Odd t (Cons (mergeNest xs ys))
mergeCarryNest t (Odd x (Cons xs)) (Even ys) = Even (mergeCarryNest (mergeTree t x) xs ys)
mergeCarryNest t (Odd x Empty) (Even  ys) = Even (carryOneNest (mergeTree t x) ys)
mergeCarryNest t (Even  xs) (Odd y (Cons ys)) = Even (mergeCarryNest (mergeTree t y) xs ys)
mergeCarryNest t (Even  xs) (Odd y Empty) = Even (carryOneNest (mergeTree t y) xs)
mergeCarryNest t (Odd x xs) (Odd y ys) = Odd t (mergeCarry (mergeTree x y) xs ys)

carryOne
    :: Ord a
    => Tree n a -> Binomial n xs a -> Binomial n (Inc xs) a
carryOne x Empty = Cons (Odd x Empty)
carryOne x (Cons xs) = Cons (carryOneNest x xs)

carryOneNest
    :: Ord a
    => Tree n a -> Nest n x xs a -> Nest n (IncFst' x xs) (IncSnd' x xs) a
carryOneNest x (Odd y Empty) = Even (Odd (mergeTree x y) Empty)
carryOneNest x (Odd y (Cons ys)) = Even (carryOneNest (mergeTree x y) ys)
carryOneNest x (Even xs) = Odd x (Cons xs)
