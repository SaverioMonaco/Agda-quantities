open import Data.Rational
open import Data.Integer
open import Data.Nat

-------------------------------
-- TUTORIAL: Rational numbers -
-------------------------------

-- We MUST define a rational number as the ratio
-- of an integer and a natural:
-- ℚ = (ℤ / ℕ)
x : ℚ
x = (+0) / (4) -- [+0 ∈ ℤ]/[4 ∈ ℕ] → 0

-- This would result in an error, here we are trying
-- to define a rational number as the ratio of
-- a natural over an integer (ℕ/ℚ)
--   x' : ℚ
--   x' = 4 / (-[1+ 0 ])

-- This would result in an error aswell, we cannot
-- define a rational as (ℕ/ℕ)
-- x'' : ℚ
-- x'' = 3 / 2

-- Lastly, ℤ/ℤ results in an error aswell
-- x''' : ℚ
-- x''' = + 3 / + 2

-- For this kind of numbers, it is obvious that
-- we have a way to define the same rational numbers
-- in multiple ways

q₁ : ℚ
q₁ = +[1+ 0 ] / 1  -- 1

q₂ : ℚ
q₂ = +[1+ 1 ] / 2  -- 1

q₃ : ℚ
q₃ = +[1+ 2 ] / 3  -- 1

-- However Agda does automatically normalize every declared
-- ℚ variable:
-- >> Ctrl+C + Ctrl+N
-- >> ℚ.denominator q₃
--    + 1             
-- >> ℚ.denominator q₂
--    + 1              
-- >> ℚ.denominator q₁ 
--    + 1
-- >> ℚ.numerator q₃
--    + 1
-- ...

data Bool : Set where
  true  : Bool
  false : Bool

ℕeq : ℕ → ℕ → Bool
ℕeq zero zero = true
ℕeq zero (ℕ.suc b) = false
ℕeq (ℕ.suc a) zero = false
ℕeq (ℕ.suc a) (ℕ.suc b) = ℕeq a b

ℤeq : ℤ → ℤ → Bool
ℤeq (+_ a) (+_ b) = ℕeq a b
ℤeq (+_ a) (-[1+_] b) = false
ℤeq (-[1+_] a) (+_ b) = false
ℤeq (-[1+_] a) (-[1+_] b) = ℕeq a b

ℚeq : ℚ → ℚ → Bool
-- ℕeq was not needed, even though the denominator is defined
-- from a natural ℕ at declaration,
-- ℚ.denominator q does return the denominator as an integer
ℚeq p q with ℤeq (ℚ.numerator p) (ℚ.numerator q) | ℤeq (ℚ.denominator p) (ℚ.denominator q)
...      | true  | true  = true
...      | false | _     = false
...      | _     | false = false

-- Let us define a ℚ number different than +1
p₁ : ℚ
p₁ = + 5 / 7

-- Test of the ℚeq function
-- >> Ctrl+C + Ctrl+N
-- >> ℚeq q₁ q₁
--    true
-- >> ℚeq q₁ q₂
--    true
-- >> ℚeq q₁ p₁
--    false



