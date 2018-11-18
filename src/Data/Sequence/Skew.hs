module Data.Sequence.Skew where

import Data.Bits
import Numeric.Binary.Skew
import Numeric.Peano
import Data.Kind
import Numeric.Peano.Gap

type family Tree (n :: ℕ) (a :: Type) where
    Tree Z a = a
    Tree (S n) a = Node n a

data Node n a = Node a (Tree n a) (Tree n a)

data ArrayTail (n :: ℕ) (ns :: [ℕ]) (a :: Type) where
    NilT :: ArrayTail n '[] a
    ConT :: Gap n g m
         -> Tree m a
         -> ArrayTail (S m) ms a
         -> ArrayTail n (g : ms) a

data Array (ns :: [ℕ]) (a :: Type) where
    Nil :: Array '[] a
    Con :: Gap Z g n
        -> Tree n a
        -> ArrayTail n ns a
        -> Array (g : ns) a

cons :: a -> Array ns a -> Array (Inc ns) a
cons x Nil = Con Zy x NilT
cons x (Con zn y NilT) = Con Zy x (ConT zn y NilT)
cons x (Con zn y1 (ConT Zy y2 ys)) = Con (Sy zn) (Node x y1 y2) ys
cons x (Con zn y1 (ConT (Sy nm) y2 ys)) =
    Con Zy x (ConT zn y1 (ConT (gapr nm) y2 ys))

uncons :: Array (n : ns) a -> (a, Array (Dec n ns) a)
uncons (Con (Sy zn) (Node x y1 y2) ys) = (x, Con zn y1 (ConT Zy y2 ys))
uncons (Con Zy x NilT) = (x, Nil)
uncons (Con Zy x (ConT nm ys NilT)) = (x, Con nm ys NilT)
uncons (Con Zy x (ConT nm y1 (ConT mp y2 ys))) =
    (x, Con nm y1 (ConT (gapl (Sy mp)) y2 ys))
