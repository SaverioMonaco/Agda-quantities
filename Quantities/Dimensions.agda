module Quantities.Dimensions where

open import Data.Integer.Base
open import Data.Nat.Base
open import Data.Rational


-- 𝕌 Datatype is just a finite set of definitions
data 𝕌 : Set where
  second   : 𝕌 -- time
  meter    : 𝕌 -- lenght
  kilogram : 𝕌 -- mass
  ampere   : 𝕌 -- electric current
  kelvin   : 𝕌 -- temperature
  mole     : 𝕌 -- amout of substance
  candela  : 𝕌 -- luminosity
  ⊥        : 𝕌

-- Abbreviations:
s   : 𝕌; s   = second
m   : 𝕌; m   = meter
kg  : 𝕌; kg  = kilogram
A   : 𝕌; A   = ampere
K   : 𝕌; K   = kelvin
mol : 𝕌; mol = mole
cd  : 𝕌; cd  = candela

record Unit : Set where
  constructor [_^_]
  field
    type : 𝕌
    exp  : ℚ
    
data Units : Set where
  -- Alone it refers to an adimensional quantity
  []  : Units
  -- The concatenation ∷ is the multiplication
  -- of quantities
  _∷_ : Unit → Units → Units

data Bool : Set where
  false : Bool
  true  : Bool

-- EQUIVALENCE BETWEEN UNITS
-- TO BE IMPROVED THIS DOES NOT SCALE
_is_ : (u v : 𝕌) → Bool
meter    is meter     = true
second   is second    = true
kilogram is kilogram  = true
ampere   is ampere    = true
kelvin   is kelvin    = true
mole     is mole      = true
candela  is candela   = true
_        is _         = false

-- Multiplication between two units.
-- if they are the same their exponent
-- get summed.
-- Otherwise they just get concatenated
_ₓ_ : (a : Unit) → (b : Unit) → Unit
a ₓ b with Unit.type a is Unit.type b
...| true  = [_^_] (Unit.type a) (Unit.exp a Data.Rational.+ Unit.exp b)
...| false = [_^_] ⊥ (+0 / 1)

_x_ : (a : Unit) → (b : Unit) → Units
a x b  with Unit.type a is Unit.type b
...| true  = [_^_] (Unit.type a) (Unit.exp a Data.Rational.+ Unit.exp b) ∷ []
...| false = a ∷ (b ∷ [])

_X_ : (a : Unit) → (B : Units) → Units
a X [] = a ∷ []
a X (b ∷ B) with Unit.type a is Unit.type b
...| true  = (a ₓ b) ∷ B
...| false = b ∷ (a X B)

Umerge : (A B : Units) → Units
Umerge [] B            = B
Umerge A []            = A
Umerge (a ∷ A) (b ∷ B) with Unit.type a is Unit.type b
...| true  = (a ₓ b) X (Umerge A B)
...| false = b ∷ Umerge (a ∷ A) B

u1 : Unit; u1 = [ s  ^ (+ 1 / 2) ]
u2 : Unit; u2 = [ s  ^ (+ 3 / 2) ]
u3 : Unit; u3 = [ kg ^ (+ 1 / 1) ]
u4 : Unit; u4 = [ m  ^ (-[1+ 0 ] / 1 ) ]







