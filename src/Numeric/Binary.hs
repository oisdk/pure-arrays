{-# LANGUAGE UndecidableInstances #-}

module Numeric.Binary where

import Numeric.Peano (ℕ(..))
import qualified Numeric.Peano as Peano
import GHC.TypeLits

type family IncFst (ns :: [ℕ]) :: ℕ where
    IncFst '[] = Z
    IncFst (n : ns) = IncFst' n ns

type family IncFst' (n :: ℕ) (ns :: [ℕ]) :: ℕ where
    IncFst' (S n) ns = Z
    IncFst' Z ns = S (IncFst ns)

type family IncSnd (ns :: [ℕ]) :: [ℕ] where
    IncSnd '[] = '[]
    IncSnd (n : ns) = IncSnd' n ns

type family IncSnd' (n :: ℕ) (ns :: [ℕ]) :: [ℕ] where
    IncSnd' (S n) ns = n : ns
    IncSnd' Z ns = IncSnd ns

type Inc (ns :: [ℕ]) = IncFst ns : IncSnd ns

type family Decr (n :: ℕ) (ns :: [ℕ]) = (r :: [ℕ]) | r -> n ns where
    Decr Z '[] = '[]
    Decr Z (n : ns) = S n : ns
    Decr (S n) ns = Z : Decr n ns

type family FromLit (n ∷ Nat) ∷ [ℕ] where
    FromLit 0 = '[]
    FromLit n = FromLit' Z (Mod n 2) (Div n 2)

type family FromLit' (s ∷ ℕ) (p ∷ Nat) (n ∷ Nat) ∷ [ℕ] where
    FromLit' s 1 n = s : FromLit n
    FromLit' s 0 n = FromLit' ('S s) (Mod n 2) (Div n 2)

type family ToLit (n ∷ [ℕ]) ∷ Nat where
    ToLit '[] = 0
    ToLit (x : xs) = (2 ^ Peano.ToLit x) * (1 + (2 * ToLit xs))
