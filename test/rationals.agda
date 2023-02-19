open import Data.Rational
open import Data.Integer
open import Data.Nat

-------------------------------
-- TUTORIAL: Rational numbers -
-------------------------------

one = Data.Nat.suc zero
two = Data.Nat.suc one


x : ℚ
x = (+ one) / (one)

a : ℚ
a = (+ one) / zero
