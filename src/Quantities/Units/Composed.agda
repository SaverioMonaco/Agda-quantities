module Quantities.Units.Composed where

open import Quantities.Units.SI.Base
open import Data.Integer.Base
open import Data.Bool.Base
open import Data.Nat.Base

open import Data.Rational.Base renaming (NonZero to ℚNonZero; 1/_ to ℚ1/_; _*_ to _ℚ*_; _+_ to _ℚ+_; _-_ to _ℚ-_; _÷_ to _ℚ÷_)
open import Data.String.Base using (String)
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; -[1+_])
import Data.Integer.DivMod as ℤ
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ; mkℚᵘ; _≢0)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

------------------------
-- - - Units type - - --
------------------------

-- Composed Units, are list of Unit types.
-- A composed unit is a unit with multiple SI units:
-- Example : Newton (N) = kg · m · s^(-2)
data 𝕌s : Set where
  I : 𝕌s
  _·_ : 𝕌 → 𝕌s → 𝕌s

------------------------
------------------------

-------------------------
------ OPERATIONS -------
-------------------------

-- Simplify the elements of the Units type
-- First it removes any Unit which exponent is zero
-- Then it removes any adim element
𝕌s-simplify : (U : 𝕌s) → 𝕌s
𝕌s-simplify U = remove-adim (remove-exp0 U)
  where
    remove-exp0 : (U : 𝕌s) → 𝕌s
    remove-exp0 I = I
    remove-exp0 (u · U) with ℤiszero (ℚ.numerator (𝕌.expo u) )
    ...| true  = remove-exp0 U
    ...| false = u · remove-exp0 U

    remove-adim : (U : 𝕌s) → 𝕌s
    remove-adim I = I
    remove-adim (u · U) with ℕiszero (b𝕌.id-num (𝕌.base u))
      where
        ℕiszero : (n : ℕ) → Bool
        ℕiszero zero       = true
        ℕiszero (ℕ.suc n) = false
    ... | false = u · (remove-adim U)
    ... | true  = remove-adim U

-- Insert a Unit type inside a Units type
-- if there is already a Unit type which shares
-- the same base. Then the two Unit elements
-- will be merged into a single one with
-- the exponent summed
-- (multiplication between two physical quantities)
insert : (u : 𝕌) (U : 𝕌s) → 𝕌s
insert u U = 𝕌s-simplify (𝕌→𝕌s-insert u U)
  where
    𝕌→𝕌s-insert : (u : 𝕌) (U : 𝕌s)  → 𝕌s
    𝕌→𝕌s-insert u I = u · I
    𝕌→𝕌s-insert u (w · Us) with (𝕌sim u w)
    ...| true  = (𝕌sum-exp u w ) · Us
    ...| false = w · (𝕌→𝕌s-insert u Us)

-- Merge every Unit element of a Units
-- type (by using insert)  with another Units type.
merge : (U W : 𝕌s) → 𝕌s
merge U W = 𝕌s-simplify (merge-w/o-simplify U W)
  where
    merge-w/o-simplify : (U W : 𝕌s) → 𝕌s
    merge-w/o-simplify  I       W = W
    merge-w/o-simplify (u · U)  I = (u · U)
    merge-w/o-simplify (u · U)  W = merge U (insert u W)

-- Multiply every exponent in 𝕌s by a value q : ℚ
-- Since q can be zero, 𝕌s-simplify will be applied
-- at the end
_𝕌s*_ : (U : 𝕌s) → (q : ℚ) → 𝕌s
U 𝕌s* q = 𝕌s-simplify (exp-multiplication U q)
  where
    exp-multiplication : (U : 𝕌s) → (q : ℚ) → 𝕌s
    exp-multiplication  I      q = I
    exp-multiplication (u · U) q = (u 𝕌× q) · (exp-multiplication U q)

-- Divide every exponent in 𝕌s by a value q : ℚ {q ≠ 0}
_𝕌s÷_ : (U : 𝕌s) → (q : ℚ) → .{n≢0 : ℤ.∣ ↥ q ∣ ≢0} → 𝕌s
_𝕌s÷_ U q {n≢0}  with (ℚ1/ q) {n≢0}
...| 1/q = U 𝕌s* 1/q

-- Apply inversion of every exponent in 𝕌s
𝕌s-inv : (U : 𝕌s) → 𝕌s
𝕌s-inv I = I
𝕌s-inv (u · U) = (𝕌inv u {𝕌pos1 u}) · 𝕌s-inv U

-- Merge two 𝕌s into one, the second one is opposite
-- This operation is required when dividing two physical
-- quantities
÷-merge : (U V : 𝕌s) → 𝕌s
÷-merge U V = merge U (_𝕌s*_ V (-[1+ 0 ] / 1))

-------------------------
-------------------------
