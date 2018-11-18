module Data.Sequence.RightPerfect where

import Data.Strict.Pair
import Numeric.Peano
import Numeric.Binary
import Data.Bits

data Nest n ns a where
    Odd  :: a -> !(Seq    ns (P a)) -> Nest Z ns a
    Even ::      !(Nest n ns (P a)) -> Nest (S n) ns a

data Seq ns a where
    Nil :: Seq '[] a
    Con :: !(Nest n ns a) -> Seq (n : ns) a

cons :: a -> Seq ns a -> Seq (Inc ns) a
cons x' xs' = Con (go x' xs')
  where
    go :: a -> Seq ns a -> Nest (IncFst ns) (IncSnd ns) a
    go x Nil = Odd x Nil
    go x (Con (Even xs)) = Odd x (Con xs)
    go x (Con (Odd y ys)) = Even (go (x :*: y) ys)

uncons :: Seq (n : ns) a -> (a, Seq (Decr n ns) a)
uncons (Con xs') = go xs' (,)
  where
    go :: Nest n ns a -> (a -> Seq (Decr n ns) a -> b) -> b
    go (Odd x Nil) k = k x Nil
    go (Odd x (Con xs)) k = k x (Con (Even xs))
    go (Even xs) k = go xs (\(y :*: z) ys -> k y (Con (Odd z ys)))

index :: Int -> Seq ns a -> Maybe a
index = go id
  where
    go :: (a -> b) -> Int -> Seq ns a -> Maybe b
    go _ !_ Nil = Nothing
    go k !i (Con xs) = go' k i xs

    go' :: (a -> b) -> Int -> Nest n ns a -> Maybe b
    go' k 0  (Odd x _) = Just (k x)
    go' k !i (Odd _ xs) = case i - 1 of
      !j | testBit j 0 -> go (k . snd') (shiftR j 1) xs
         | otherwise   -> go (k . fst') (shiftR j 1) xs
    go' k !i (Even xs)
      | testBit i 0 = go' (k . snd') (shiftR i 1) xs
      | otherwise   = go' (k . fst') (shiftR i 1) xs

data BlindSeq a = forall ns. BlindSeq (Seq ns a)

cons' :: a -> BlindSeq a -> BlindSeq a
cons' x (BlindSeq xs) = BlindSeq (cons x xs)

fromList :: [a] -> BlindSeq a
fromList = foldr cons' (BlindSeq Nil)

-- |
-- >>> index' 3 (fromList [0..10])
-- Just 3
--
-- >>> let xs = fromList [0..35] in and [ index' i xs == Just i | i <- [0..35] ]
-- True
index' :: Int -> BlindSeq a -> Maybe a
index' i (BlindSeq xs) = index i xs
