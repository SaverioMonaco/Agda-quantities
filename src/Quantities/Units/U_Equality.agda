module Quantities.Units.U_Equality where

open import Quantities.Units.SI.Base
open import Quantities.Units.Composed.Base as 𝕌s
open import Data.Nat
open import Data.Integer
open import Data.Rational

U-append : 𝕌s → 𝕌 → 𝕌s
U-append I u = u · I
U-append (x · us) u = x · (U-append us u)

U-reverse : 𝕌s → 𝕌s
U-reverse I = I
U-reverse (u · us) = U-append (U-reverse us) u

-- Permutations invariant equality for the units
data _≡ᵤ_ : 𝕌s → 𝕌s → Set where
  -- A Units is PI-equal to itself
  permRefl  : {us : 𝕌s}      → us ≡ᵤ us
  -- Symmetry property: If unit1 is PI-equal to unit2, then unit2 is PI-equal to unit1
  permSymm  : {us1 us2 : 𝕌s} → us1 ≡ᵤ us2 → us2 ≡ᵤ us1

  -- If two units are PI-equal, prepending a base unit to both of them does not
  -- remove PI-equality
  permPrep  : {u : 𝕌} {us1 us2 : 𝕌s} → us1 ≡ᵤ us2 → (u · us1) ≡ᵤ (u · us2)
  -- If two units are PI-equal, appending a base unit to both of them does not
  -- remove PI-equality
  permApp   : {u : 𝕌} {us1 us2 : 𝕌s} → us1 ≡ᵤ us2 → (U-append us1 u) ≡ᵤ (U-append us2 u)

  -- A unit is PI-equal to its reverse
  permRev   : {us : 𝕌s}      → us  ≡ᵤ (U-reverse us)
  -- If two units are equal, reversing one of them does not remove PI-equality
  permRev2  : {us1 us2 : 𝕌s} → us1 ≡ᵤ us2 → us1 ≡ᵤ (U-reverse us2)

  -- Swapping the first two base units does not remove PI-equality
  permSwap  : {u1 u2 : 𝕌} {us : 𝕌s} → (u1 · (u2 · us)) ≡ᵤ (u2 · (u1 · us))
  -- Transitivity rule
  permTrans : {us1 us2 us3 : 𝕌s} → us1 ≡ᵤ us2 → us2 ≡ᵤ us3 → us1 ≡ᵤ us3

  -- If two units are equal, merging a base unit to both of them does not remove
  -- PI-equality
  permFuse  : {us1 us2 usfuse : 𝕌s} → us1 ≡ᵤ us2 → (𝕌s.merge us1 usfuse) ≡ᵤ (𝕌s.merge us2 usfuse)
  -- Appending a base unit to a unit is PI-equal to inserting it (adding
  -- the exponents)
  permIns   : {u : 𝕌} {us : 𝕌s}    → (u · us) ≡ᵤ (𝕌s.insert u us)
  -- Congruence rule
  permCong  : {f : 𝕌s → 𝕌s} {us1 us2 : 𝕌s} → us1 ≡ᵤ us2 → (f us1) ≡ᵤ (f us2)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -
-- EXAMPLE : MOMENTUM × FREQUENCY ≡ᵤ NEWTON --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -

momentum  = [ g ^ 1ℚ ] · ( [ m ^ 1ℚ ] · ( [ s ^ -[1+ 0 ] / 1 ] · I ))
newton    = [ g ^ 1ℚ ] · ([ m ^ 1ℚ ] · ([ s ^ -[1+ 1 ] / 1 ] · I))
frequency = [ s ^ -[1+ 0 ] / 1 ]

lemma-h1 : (frequency · momentum) ≡ᵤ ([ s ^ -[1+ 1 ] / 1 ] · ( [ m ^ 1ℚ ] · ( [ g ^ 1ℚ ] · I )))
lemma-h1 = permRev2 (permIns {frequency} {momentum})

lemma-h2 : newton ≡ᵤ ([ s ^ -[1+ 1 ] / 1 ] · ( [ m ^ 1ℚ ] · ( [ g ^ 1ℚ ] · I )))
lemma-h2 = permRev {newton}

lemma : (frequency · momentum) ≡ᵤ newton
lemma = permTrans lemma-h1 (permSymm lemma-h2)

