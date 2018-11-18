module Main (main) where

import Criterion.Main
import System.Random
import Control.Monad
import Data.List

randInt :: IO Int
randInt = randomR (0,1000)

benchAtSize :: Int -> Benchmark
benchAtSize n =
    env (replicateM randInt n) $
    \xs ->
         bgroup (show n) [bench "sort" $ nf sort xs]


main :: IO ()
main =
    defaultMain
        [ benchAtSize 100
        , benchAtSize 1000 ]
