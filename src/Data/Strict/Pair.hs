module Data.Strict.Pair where

infixr 6 :*:
data P a = !a :*: !a deriving Foldable

fst' ∷ P a → a
fst' (x :*: _) = x

snd' ∷ P a → a
snd' (_ :*: x) = x
