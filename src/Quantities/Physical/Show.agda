module Quantities.Physical.Show where

open import Quantities.Physical.Base
open import Data.Nat
open import Data.Rational renaming (show to deprecated-show)
open import Data.Bool
open import Data.Rational.Show using () renaming (show to ℚshow)
open import Data.Integer.Show using () renaming (show to ℤshow)
open import Data.String.Base using (String; _++_)
open import Quantities.Units.Composed.Show using () renaming (show to show𝕌s)
open import Data.Vec.Base renaming (_++_ to somethingelse)
open import Relation.Binary.PropositionalEquality

-- show function for the Physical Quantities type.
-- It prints the number either as a ℚ (if the numerator is ≠ 1)
-- or as a ℤ,
-- then it prints the dimension using the show function from
-- Quantities.Units.Composed.Show

show-vec : {n : ℕ} → (vec : Vec ℚ n) → String
show-vec [] = ""
show-vec (v ∷ V) with denominator-is-one v
  where
    denominator-is-one : (q : ℚ) → Bool
    denominator-is-one q with (ℕisone (ℚ.denominatorℕ q) )
      where
        ℕisone : (n : ℕ) → Bool
        ℕisone zero          = false
        ℕisone (suc zero)    = true
        ℕisone (suc (suc n)) = false
    ...| bool = bool
...| false = (ℚshow v) ++ ", " ++(show-vec V)
...| true  = ℤshow (ℚ.numerator v) ++ ", " ++ (show-vec V)

show : (pq : PQ) → String
show pq = "(" ++ (show-vec (PQ.vector pq)) ++ ")  [" ++ (show𝕌s (PQ.units pq)) ++ "]"


str1 = show quantity1
str2 = show quantity2
str3 = show quantity3

str12 = show q12

