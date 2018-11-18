module Numeric.Binary.Skew where

import Numeric.Peano

type family Inc (ns :: [ℕ]) = (ms :: [ℕ]) | ms -> ns where
    Inc '[]              = Z   : '[]
    Inc (x  : '[])       = Z   : x  : '[]
    Inc (x  : Z    : xs) = S x : xs
    Inc (x₁ : S x₂ : xs) = Z   : x₁ : x₂ : xs

type family Dec (n :: ℕ) (ns :: [ℕ]) = (ms :: [ℕ]) | ms -> n ns where
    Dec (S x)  xs            = x  : Z : xs
    Dec Z     '[]            = '[]
    Dec Z     (x  : '[])     = x  : '[]
    Dec Z     (x₁ : x₂ : xs) = x₁ : S x₂ : xs

