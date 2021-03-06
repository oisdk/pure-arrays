module Data.Heap.Binomial where

import Data.Kind
import Numeric.Binary
import Numeric.Peano
import Data.List (unfoldr)

-- $setup
-- >>> import Test.QuickCheck
-- >>> import Data.Foldable (toList)
-- >>> import qualified Data.List as List

data Tree n a = Root a (Node n a) deriving Foldable

data Node n a where
    Nil  :: Node Z a
    (:<) :: Tree n a -> Node n a -> Node ('S n) a

deriving instance Foldable (Node n)

mergeTree :: Ord a => Tree n a -> Tree n a -> Tree (S n) a
mergeTree xr@(Root x xs) yr@(Root y ys)
  | x <= y    = Root x (yr :< xs)
  | otherwise = Root y (xr :< ys)

data Binomial (x :: ℕ) (xs :: [ℕ]) (a :: Type) where
    Empty :: Binomial n '[] a
    Cons  :: Nest x y ys a -> Binomial x (y : ys) a

deriving instance Foldable (Binomial x xs)

data Nest x y ys a where
    Odd  :: Tree n a -> Binomial ('S n) xs a -> Nest n Z xs a
    Even :: Nest (S x) y ys a -> Nest x (S y) ys a

deriving instance Foldable (Nest n x xs)

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

minView :: Ord a => Binomial n (x : xs) a -> (a, Binomial n (Decr x xs) a)
minView xs = minViewProof xs (,)

minViewProof :: Ord a => Binomial n (x : xs) a -> (Inc (Decr x xs) ~ (x : xs) => a -> Binomial n (Decr x xs) a -> b) -> b
minViewProof (Cons xs' ) k' = go xs' \(Zipper x _ xs) -> k' x xs
  where
    go :: Ord a
       => Nest n x xs a
       -> (Inc (Decr x xs) ~ (x : xs) => Zipper a n (Decr x xs) -> b) -> b
    go (Even xs) k = go xs \(Zipper m (t :< ts) hs) -> k (Zipper m ts (Cons (Odd t hs)))
    go (Odd (Root x ts) Empty) k = k (Zipper x ts Empty)
    go (Odd c@(Root x cs) (Cons xs)) k =
        go xs
            \case
                Zipper m _ _ | m >= x -> k (Zipper x cs (Cons (Even xs)))
                Zipper m (t :< ts) Empty -> k (Zipper m ts (Cons (Even (Odd (mergeTree c t) Empty))))
                Zipper m (t :< ts) (Cons hs) -> k (Zipper m ts (Cons (Even (carryOneNest (mergeTree c t) hs))))

data BlindBinom a = forall xs. BlindBinom (Binomial Z xs a)

deriving instance Foldable BlindBinom

insert' :: Ord a => a -> BlindBinom a -> BlindBinom a
insert' x (BlindBinom xs) = BlindBinom (carryOne (Root x Nil) xs)

minView' :: Ord a => BlindBinom a -> Maybe (a, BlindBinom a)
minView' (BlindBinom Empty) = Nothing
minView' (BlindBinom (Cons xs)) = case minView (Cons xs) of
  (y,ys) -> Just (y, BlindBinom ys)

fromList :: Ord a => [a] -> BlindBinom a
fromList = foldr insert' (BlindBinom Empty)

-- |
-- prop> Data.List.sort (xs :: [Int]) === sort xs
sort :: Ord a => [a] -> [a]
sort = unfoldr minView' . fromList
