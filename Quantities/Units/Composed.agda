module Quantities.Units.Composed where

open import Quantities.Units.SI.Base
open import Data.Rational.Base renaming (_+_ to _ℚ+_; NonZero to ℚNonZero)
open import Data.Integer.Base
open import Data.Bool.Base
open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl)

----------------------
-- Helping Function --
----------------------
ℤiszero : (z : ℤ) → Bool
ℤiszero (+0)       = true  --  0
ℤiszero +[1+ n ]   = false -- +1, +2, +3, ...
ℤiszero (-[1+_] n) = false -- -1, -2, -3, ...
----------------------
---------------------

-- Composed Units, are list of Unit types.
-- A composed unit is a unit with multiple SI units:
-- Example : Newton (N) = kg · m · s^(-2)
data 𝕌s : Set where
  I : 𝕌s
  _·_ : 𝕌 → 𝕌s → 𝕌s

-- This function reduces a Unit into Adimensional
-- in case that its exponent is 0
-- Example : m^0 does not mean anything
-- While performing calculations, if we multiply m and m^(-1)
-- we get m^0 while in reality is just an adimensional number
-- By contruction, units automatically removes any dimension
-- with a 0 exponent.
-- This function will be used while combining Units
𝕌-simplify : (u : 𝕌) → 𝕌
𝕌-simplify u  with ℤiszero (ℚ.numerator (𝕌.expo u) )
...| true  = con𝕌 adim (+[1+ 0 ] / 1 )
...| false = u


𝕌s-simplify : (U : 𝕌s) → 𝕌s
𝕌s-simplify I = I
𝕌s-simplify (u · U) with ℕiszero (b𝕌.id (𝕌.base u))
  where
    ℕiszero : (n : ℕ) → Bool
    ℕiszero zero  = true
    ℕiszero (ℕ.suc n) = false
... | false = (𝕌-simplify u) · (𝕌s-simplify U)
... | true  = 𝕌s-simplify U

𝕌sum-exp : (u w : 𝕌) → 𝕌
𝕌sum-exp u w = 𝕌-simplify ( con𝕌 (𝕌.base u) ( (𝕌.expo u) ℚ+ (𝕌.expo w) ) )

insert : (u : 𝕌) (U : 𝕌s) → 𝕌s
insert u U = 𝕌s-simplify (𝕌→𝕌s-insert u U)
  where
    𝕌→𝕌s-insert : (u : 𝕌) (U : 𝕌s)  → 𝕌s
    𝕌→𝕌s-insert u I = u · I
    𝕌→𝕌s-insert u (w · Us) with (𝕌sim u w)
    ...| true  = (𝕌sum-exp u w ) · Us
    ...| false = w · (𝕌→𝕌s-insert u Us)

merge : (U W : 𝕌s) → 𝕌s
merge I W = 𝕌s-simplify W
merge U I = 𝕌s-simplify U
merge (u · U) (w · W) with 𝕌sim u w
... | false = w · (merge (u · U) W) 
... | true  = insert (𝕌sum-exp u w) (merge U W)

𝕌-inverse : (u : 𝕌) → .{{_ : ℚNonZero (𝕌.expo u)}}  → 𝕌
𝕌-inverse u with 𝕌.expo u
...| exp = con𝕌 (𝕌.base u) (1/ exp )

kg-1 : 𝕌; kg-1 = [ (kilo- g) ^ -[1+ 0 ] / 1 ]
s+2  : 𝕌; s+2  = [ s         ^ +[1+ 1 ] / 1 ]
newton : 𝕌s; newton = [ (kilo- g) ^ 1ℚ ] · ( [ m ^ 1ℚ ] · ([ s ^ ( -[1+ 1 ] / 1 ) ] · I) )
ohm    : 𝕌s; ohm    = [ (kilo- g) ^ 1ℚ ] · ( [ m ^ +[1+ 1 ] / 1 ] · ( [ s ^ -[1+ 2 ] / 1 ] · ( [ A ^ -[1+ 1 ] / 1 ] · I ) ) )

-- (From Quantities.Units.Show)
-- >> show (insert s+2 (insert kg-1 newton))
-- "m^(1) "

