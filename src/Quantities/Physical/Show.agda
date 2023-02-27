module Quantities.Physical.Show where

open import Quantities.Physical.Base
open import Data.Nat
open import Data.Rational renaming (show to deprecated-show)
open import Data.Bool
open import Data.Rational.Show using () renaming (show to ℚshow)
open import Data.Integer.Show using () renaming (show to ℤshow)
open import Data.String.Base using (String; _++_)
open import Quantities.Units.Composed.Show using () renaming (show to show𝕌s)

-- show function for the Physical Quantities type.
-- It prints the number either as a ℚ (if the numerator is ≠ 1)
-- or as a ℤ,
-- then it prints the dimension using the show function from
-- Quantities.Units.Composed.Show
show : (pq : PQ) → String
show (conPQ number dimension) with denominator-is-one (number)
  where
    denominator-is-one : (q : ℚ) → Bool
    denominator-is-one q with (ℕisone (ℚ.denominatorℕ q) )
      where
        ℕisone : (n : ℕ) → Bool
        ℕisone zero          = false
        ℕisone (suc zero)    = true
        ℕisone (suc (suc n)) = false
    ...| bool = bool
...| false = ℚshow number ++ "  [" ++ show𝕌s dimension ++ "]"
...| true  = ℤshow (ℚ.numerator number) ++ "  [" ++ show𝕌s dimension ++ "]"
