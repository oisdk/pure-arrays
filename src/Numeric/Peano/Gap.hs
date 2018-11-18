module Numeric.Peano.Gap where

import Numeric.Peano

-- | An encoding of the gap between two numbers.
--
-- The type:
--
-- @
--   'Gap' n g m
-- @
--
-- Means that there is a gap of size @g@ between @n@ and @m@.
-- Stated another way, it means:
--
-- @
--   n + g = m
-- @
data Gap (n ∷ ℕ) (g ∷ ℕ) (m ∷ ℕ) where
    Zy ∷ Gap n Z n
    Sy ∷ Gap n g m → Gap n (S g) (S m)

-- | Shift the gap right by one place.
gapr :: Gap n g m -> Gap (S n) g (S m)
gapr Zy       = Zy
gapr (Sy pnm) = Sy (gapr pnm)

-- | Shift the gap left by one place.
gapl ::  Gap (S n) g (S m) -> Gap n g m
gapl Zy = Zy
gapl (Sy snsm) = go snsm
  where
    go :: Gap (S n) g m -> Gap n (S g) m
    go Zy = Sy Zy
    go (Sy snm) = Sy (go snm)
