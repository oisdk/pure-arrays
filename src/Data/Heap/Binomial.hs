module Data.Heap.Binomial where

import Data.Kind
import Numeric.Binary
import Numeric.Peano
import Data.Type.Equality

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
mergeCarryNest t (Even xs)         (Even ys)         = Odd t (Cons (mergeNest xs ys))
mergeCarryNest t (Odd x (Cons xs)) (Even ys)         = Even (mergeCarryNest (mergeTree t x) xs ys)
mergeCarryNest t (Odd x Empty)     (Even ys)         = Even (carryOneNest (mergeTree t x) ys)
mergeCarryNest t (Even xs)         (Odd y (Cons ys)) = Even (mergeCarryNest (mergeTree t y) xs ys)
mergeCarryNest t (Even xs)         (Odd y Empty)     = Even (carryOneNest (mergeTree t y) xs)
mergeCarryNest t (Odd x xs)        (Odd y ys)        = Odd t (mergeCarry (mergeTree x y) xs ys)

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

data Zipper a n xs = Zipper a (Node n a) (Binomial n xs a)

slideLeft :: Zipper a (S n) xs -> Zipper a n (Z : xs)
slideLeft (Zipper m (t :< ts) hs) = Zipper m ts (Cons (Odd t hs))

lemma1 :: forall x xs n a. Decr x xs :~: '[] → Nest n x xs a -> (x : xs) :~: Z : '[]
lemma1 Refl (Odd _ Empty) = Refl

lemma2 :: forall x xs y ys n a. Decr x xs :~: (y : ys) -> Nest n x xs a -> Nest n y ys a -> (x : xs) :~: Inc (y : ys)
lemma2 Refl (Even xs) ys = case ys of
  Odd y Empty -> case xs of
    Odd x' xs' -> case xs' of
      Empty -> Refl
  Odd y (Cons ys') -> case lemma2 Refl xs ys' of
    Refl -> Refl
lemma2 Refl (Odd _ xs) (Even _) = case xs of
  Cons _ -> Refl
lemma2 Refl (Odd _ xs) (Odd _ _) = case xs of

minViewZip :: Ord a => Binomial n (x : xs) a -> Zipper a n (Decr x xs)
minViewZip (Cons xs') = go xs'
  where
    go :: forall a n x xs. Ord a => Nest n x xs a -> Zipper a n (Decr x xs)
    go (Even xs) = slideLeft (go xs)
    go (Odd (Root x ts) Empty) = Zipper x ts Empty
    go wit@(Odd c@(Root x ts) (Cons xs)) = case go xs of
      ex@(Zipper m (t' :< ts') (hs :: Binomial (S n) (Decr y ys) a)) | m >= x -> Zipper x ts (Cons (Even xs))
                                   | otherwise -> Zipper m ts (case hs of
                                                                   Empty -> gcastWith (lemma1 @y @ys Refl xs) (Cons (Even (Odd (mergeTree c t') Empty)))
                                                                   Cons hs' -> gcastWith (lemma2 @y @ys Refl  xs hs') (Cons (Even (carryOneNest (mergeTree c t') hs'))))
