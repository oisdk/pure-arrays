{-# LANGUAGE UndecidableInstances #-}

module Numeric.Peano where

import           Control.DeepSeq
import           Data.Typeable
import           GHC.Generics
import           Numeric.Natural
import           Text.Read
import           Data.List
import           Data.Function
import           GHC.TypeLits

-- $setup
-- >>> import Test.QuickCheck
-- >>> import Data.List (genericLength)
-- >>> default (ℕ)
-- >>> :{
-- instance Arbitrary ℕ where
--     arbitrary = fmap (fromInteger . getNonNegative) arbitrary
-- :}

-- | Peano numbers. Care is taken to make operations as lazy as
-- possible:
--
-- >>> 1 > S (S undefined)
-- False
-- >>> Z > undefined
-- False
-- >>> 3 + undefined >= 3
-- True

data ℕ
    = Z
    | S ℕ
    deriving (Eq, Generic, Typeable)

-- | Converts to a church numeral
fold ∷ ℕ → (a → a) → a → a
fold Z _ b     = b
fold (S n) f b = f (fold n f b)

-- | As lazy as possible
instance Ord ℕ where
    compare Z Z         = EQ
    compare (S n) (S m) = compare n m
    compare Z (S _)     = LT
    compare (S _) Z     = GT
    Z <= _ = True
    S n <= S m = n <= m
    S _ <= Z = False
    Z > _ = False
    S n > S m = n > m
    S _ > Z = True
    (>=) = flip (<=)
    (<) = flip (>)

-- | Subtraction stops at zero.
--
-- prop> n >= m ==> m - n == Z
instance Num ℕ where
    (+) n = fold n S
    n * m = fold n (m+) Z
    abs = id
    signum Z = 0
    signum _ = 1
    fromInteger n
        | n < 0 = error "cannot convert negative integers to Peano numbers"
        | otherwise = go n where
            go 0 = Z
            go m = S (go (m-1))
    S n - S m = n - m
    n - _ = n

-- | Shows integer representation.
instance Show ℕ where
    showsPrec n = showsPrec n . toInteger

-- | Reads the integer representation.
instance Read ℕ where
    readPrec = fmap (fromIntegral :: Natural -> ℕ) readPrec

-- | Will obviously diverge for values like `maxBound`.
instance NFData ℕ where
    rnf Z     = ()
    rnf (S n) = rnf n

-- | Reasonably expensive.
instance Real ℕ where
    toRational = toRational . toInteger

-- | The maximum bound here is infinity.
--
-- prop> maxBound > (n :: ℕ)
instance Bounded ℕ where
    minBound = Z
    maxBound = fix S

-- | Uses custom 'enumFrom', 'enumFromThen', 'enumFromThenTo' to avoid
-- expensive conversions to and from 'Int'.
--
-- >>> [1..3]
-- [1,2,3]
-- >>> [1..1]
-- [1]
-- >>> [2..1]
-- []
-- >>> take 3 [1,2..]
-- [1,2,3]
-- >>> take 3 [5,4..]
-- [5,4,3]
-- >>> [1,3..7]
-- [1,3,5,7]
-- >>> [5,4..1]
-- [5,4,3,2,1]
-- >>> [5,3..1]
-- [5,3,1]
instance Enum ℕ where
    succ = S
    pred (S n) = n
    pred Z = error "pred called on zero nat"
    fromEnum = go 0
      where
        go !n Z = n
        go !n (S m) = go (1 + n) m
    toEnum m
      | m < 0 = error "cannot convert negative number to Peano"
      | otherwise = go m
      where
        go 0 = Z
        go n = S (go (n - 1))
    enumFrom = iterate S
    enumFromTo n m = unfoldr f (n, S m - n)
      where
        f (_,Z) = Nothing
        f (e,S l) = Just (e, (S e, l))
    enumFromThen n m = iterate t n
      where
        ts Z mm = (+) mm
        ts (S nn) (S mm) = ts nn mm
        ts nn Z = subtract nn
        t = ts n m
    enumFromThenTo n m t = unfoldr f (n, jm)
      where
        ts (S nn) (S mm) = ts nn mm
        ts Z mm = (S t - n, (+) mm, mm)
        ts nn Z = (S n - t, subtract nn, nn)
        (jm,tf,tt) = ts n m
        td = subtract tt
        f (_,Z) = Nothing
        f (e,l@(S _)) = Just (e, (tf e, td l))

-- | Errors on zero.
--
-- >>> 5 `div` 2
-- 2
instance Integral ℕ where
    toInteger = go 0
      where
        go !p Z     = p
        go !p (S n) = go (p + 1) n
    quotRem _ Z = (maxBound, error "divide by zero")
    quotRem x y = qr Z x y
      where
        qr q n m = go n m
          where
            go nn Z          = qr (S q) nn m
            go (S nn) (S mm) = go nn mm
            go Z (S _)       = (q, n)
    quot n m = go n where
      go = subt m where
        subt Z nn          = S (go nn)
        subt (S mm) (S nn) = subt mm nn
        subt (S _) Z       = Z
    rem _ Z = error "divide by zero"
    rem nn mm = r nn mm where
      r n m = go n m where
        go nnn Z           = r nnn m
        go (S nnn) (S mmm) = go nnn mmm
        go Z (S _)         = n
    div = quot
    mod = rem
    divMod = quotRem

type family ToLit' (i ∷ Nat) (n ∷ ℕ) ∷ Nat where
    ToLit' i Z = i
    ToLit' i ('S n) = ToLit' (i + 1) n

type ToLit (n ∷ ℕ) = ToLit' 0 n

type family FromLit (i ∷ Nat) ∷ ℕ where
    FromLit 0 = Z
    FromLit n = 'S (FromLit (n-1))
