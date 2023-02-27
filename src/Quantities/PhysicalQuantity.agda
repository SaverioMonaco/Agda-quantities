module Quantities.PhysicalQuantity where

open import Quantities.Units.Composed as 𝕌s
open import Data.Rational
open import Quantities.Units.Composed-examples

record PQ : Set where
  constructor conPQ
  field
    number    : ℚ
    dimension : 𝕌s.𝕌s

_×[_] : (number : ℚ) (dim : 𝕌s) → PQ
_×[_] number dim = conPQ number (𝕌s.𝕌s-simplify dim)


example-of-a-physical-quantity = (+[1+ 2 ] / 4) ×[ newton ]
