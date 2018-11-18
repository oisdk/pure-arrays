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

type family Add (xs :: [ℕ]) (ys :: [ℕ]) :: [ℕ] where
    Add '[] ys = ys
    Add xs '[] = xs
    Add (x : xs) (y : ys) = AddFst' x xs y ys : AddSnd' x xs y ys

type family AddFst' (x :: ℕ) (xs :: [ℕ]) (y :: ℕ) (ys :: [ℕ]) :: ℕ where
    AddFst' (S x) xs (S y) ys = S (AddFst' x xs y ys)
    AddFst' Z xs (S y) ys = Z
    AddFst' (S x) xs Z ys = Z
    AddFst' Z '[] Z '[] = S Z
    AddFst' Z '[] Z (y : ys) = S (IncFst' y ys)
    AddFst' Z (x : xs) Z '[] = S (IncFst' x xs)
    AddFst' Z (x : xs) Z (y : ys) = S (AddCinFst' x xs y ys)

type family AddSnd' (x :: ℕ) (xs :: [ℕ]) (y :: ℕ) (ys :: [ℕ]) :: [ℕ] where
    AddSnd' (S x) xs (S y) ys = AddSnd' x xs y ys
    AddSnd' Z '[] Z '[] = '[]
    AddSnd' Z '[] (S y) ys = y : ys
    AddSnd' Z (x : xs) (S y) ys = AddFst' x xs y ys : AddSnd' x xs y ys
    AddSnd' (S x) xs Z '[] = x : xs
    AddSnd' (S x) xs Z (y : ys) = AddFst' x xs y ys : AddSnd' x xs y ys
    AddSnd' Z (x : xs) Z '[] = IncSnd' x xs
    AddSnd' Z '[] Z (y : ys) = IncSnd' y ys
    AddSnd' Z (x : xs) Z (y : ys) = AddCinSnd' x xs y ys

type family AddCin (xs :: [ℕ]) (ys :: [ℕ]) :: [ℕ] where
    AddCin '[] ys = Inc ys
    AddCin xs '[] = Inc xs
    AddCin (x : xs) (y : ys) = AddCinFst' x xs y ys : AddCinSnd' x xs y ys

type family AddCinFst' (x :: ℕ) (xs :: [ℕ]) (y :: ℕ) (ys :: [ℕ]) :: ℕ where
    AddCinFst' (S x) xs (S y) ys = Z
    AddCinFst' Z xs Z ys = Z
    AddCinFst' Z (x : xs) (S y) ys = S (AddCinFst' x xs y ys)
    AddCinFst' Z '[] (S y) ys = S (IncFst' y ys)
    AddCinFst' (S x) xs Z (y : ys) = S (AddCinFst' x xs y ys)
    AddCinFst' (S x) xs Z '[] = S (IncFst' x xs)

type family AddCinSnd' (x :: ℕ) (xs :: [ℕ]) (y :: ℕ) (ys :: [ℕ]) :: [ℕ] where
    AddCinSnd' (S x) xs (S y) ys = AddFst' x xs y ys : AddSnd' x xs y ys
    AddCinSnd' Z xs Z ys = AddCin xs ys
    AddCinSnd' Z (x : xs) (S y) ys = AddCinSnd' x xs y ys
    AddCinSnd' Z '[] (S y) ys = IncSnd' y ys
    AddCinSnd' (S x) xs Z (y : ys) = AddCinSnd' x xs y ys
    AddCinSnd' (S x) xs Z '[] = IncSnd' x xs
