module Quantities.Physical.Base where

open import Quantities.Units.SI.Base
open import Quantities.Units.Composed.Base as 𝕌s
open import Data.Rational as ℚ
open import Quantities.Units.Composed.Examples
open import Data.Integer
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ; mkℚᵘ; _≢0)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Bool.Base

import Data.Integer.DivMod as ℤ
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; -[1+_])
open import Relation.Nullary.Decidable using (True)

------------------------------------------------------------------------
-- - - - - - - - - - PHYSICAL QUANTITY (PQ) UNIT TYPE - - - - - - - - --
------------------------------------------------------------------------
record PQ : Set where
  constructor conPQ
  field
    number    : ℚ
    dimension : 𝕌s.𝕌s

-- Constructor for a Physical Quantity Type:
-- Example:
--  a-force = 1ℚ ×[ [ (kilo- g) ^ 1ℚ ] · ( [ m ^ 1ℚ ] · ([ s ^ ( -[1+ 1 ] / 1 ) ] · I) ) ]
--    or
--  (first you define newton)
--  newton = [ (kilo- g) ^ 1ℚ ] · ( [ m ^ 1ℚ ] · ([ s ^ ( -[1+ 1 ] / 1 ) ] · I) )
--  (then we use the constructor)
--  another-force = 1ℚ ×[ newton ]
--  which is easier to read
_×[_] : (number : ℚ) (dim : 𝕌s) → PQ
_×[_] number dim = conPQ number (𝕌s.𝕌s-simplify dim)

-- Takes two Physical Quantities. It returns
--  > ⊥ if the two dimensions are NOT the same
--  > ⊤ if the two dimensions are the same
same-dimension : PQ → PQ → Set
same-dimension q1 q2 with PQ.dimension q1 | PQ.dimension q2
...| dim1 | dim2 = T (dim1 𝕌≡ᵇ dim2)
  where
    _𝕌≡ᵇ_ : 𝕌s → 𝕌s → Bool
    dim1 𝕌≡ᵇ dim2 with ÷-merge dim1 dim2
    ...| I = true
    ...| _ = false

--------------------------------------------------
-- - - - - - - - - - OPERATIONS - - - - - - - - --
--------------------------------------------------

-- 1. MULTIPLICATION BETWEEN PQ
-- Multiply two PQ quantities, merge the two dimensions
_PQ×_ : (q1 : PQ) → (q2 : PQ) → PQ
(conPQ n1 d1) PQ× (conPQ n2 d2) = conPQ (n1 ℚ.* n2) (merge d1 d2)

-- 2. INVERSION OF A PQ
-- Apply 1/_ to the number part, multiply with (-1) the exponents of the
-- dimensions
PQ1/_ : (q : PQ) →  .{n≢0 : ℤ.∣ ℚ.numerator (PQ.number q) ∣ ≢0} → PQ
PQ1/_ q {n≢0} with (1/ (PQ.number q)) {n≢0}
...| 1/number = conPQ 1/number (PQ.dimension q 𝕌s* (-[1+ 0 ] / 1) )

-- 3. DIVISION BETWEEN PQ
-- Multiply the first PQ with the inverse of the second PQ
_PQ÷_ : (q1 : PQ) → (q2 : PQ) →  .{n≢0 : ℤ.∣ ℚ.numerator (PQ.number q2) ∣ ≢0} → PQ
_PQ÷_ q1 q2 {n≢0} with PQ1/_ q2 {n≢0}
...| 1/q2 = q1 PQ× 1/q2

-- 4. ADDITION BETWEEN PQ
-- Add two PQ together, assuming the two PQ have the same dimension
_PQ+_ : (q1 : PQ) (q2 : PQ) → .{q1≡q2 : same-dimension q1 q2} → PQ
_PQ+_ q1 q2 = conPQ ((PQ.number q1) ℚ.+ (PQ.number q2)) (PQ.dimension q1)

-- 5. SUBTRACTION BETWEEN PQ
-- Subtract the two PQ, assuming the two PQ have the same dimension
_PQ-_ : (q1 : PQ) (q2 : PQ) → .{q1≡q2 : same-dimension q1 q2} → PQ
_PQ-_ q1 q2 = conPQ ((PQ.number q1) ℚ.- (PQ.number q2)) (PQ.dimension q1)

-- 6. Multiplication with a number
-- Multiply a PQ with a number
_ℚPQ×_ : (pq : PQ) (q : ℚ) → PQ
pq ℚPQ× q = conPQ ((PQ.number pq) ℚ.* q) (PQ.dimension pq)

-- 7. Division with a number
-- DIvide a PQ with a number
_ℚPQ÷_ : (pq : PQ) → (q : ℚ) → .{n≢0 : ℤ.∣ ℚ.numerator q ∣ ≢0} → PQ
_ℚPQ÷_ pq q {n≢0} with ℚ.1/_ q {n≢0}
...| 1/q = conPQ ((PQ.number pq) ℚ.* 1/q) (PQ.dimension pq)
