module Quantities.Tests where

open import Data.Integer.Base
open import Data.Nat.Base
open import Data.Rational

------------------------------------------------
------------ HELPING FUNCTIONS: ----------------
------------------------------------------------
-- Simple Bool type, it has just
-- two elements:
data Bool : Set where
  false : Bool
  true  : Bool
-- Operators were not defined for it because
-- elements of Bools will be used just for the
-- case-split in the 'with' abstraction

-- ℤiszero will return:
-- > true if the integer is +0
-- > false otherwise
ℤiszero : (z : ℤ) → Bool
ℤiszero (+_ zero)  = true  --    0,
ℤiszero +[1+ n ]   = false -- +1+0, +1+1, +1+2, ...
ℤiszero (-[1+_] n) = false -- -1+0, -1+1, -1+2, ...

-- ℚiszero will return:
-- > true if the rational is 0
-- > false otherwise
ℚiszero : (q : ℚ) → Bool
-- for q to be zero, its numerator (ℤ) must be zero
ℚiszero q with ℤiszero (ℚ.numerator q)
...| true  = true
...| false = false
------------------------------------------------
------------------------------------------------


------------------------------------------------
------------------ TYPES: ----------------------
------------------------------------------------

-- DATAs : 
-- 1. 𝕌 Datatype is just a finite set of definitions
-- 2. Unit is a type that combines a unit (𝕌) element
--    and an exponent (ℚ)
--    (for example, the Area is [ meter ^ +[1+ 1 ] ]
--     A = m^2 )
-- 3. Units is a type similar to List that combines
--    multiple Unit elements together.
--    (for example, Newton is
--     [ kg ^ +[1+ 0 ] ∷ ([ m ^ +[1+ 0 ] ∷ ([ s ^ -[1+ 1 ] ∷ []))
--     N = kg · m · s^(-2) )
data 𝕌 : Set where
  adim     : 𝕌
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

𝕀 : Unit; 𝕀 = [_^_] adim (+[1+ 0 ] / 1)
    
data Units : Set where
  -- Alone it refers to an adimensional quantity
  []  : Units
  -- The concatenation ∷ is the multiplication
  -- of quantities
  _∷_ : Unit → Units → Units

------------------------------------------------
------------------------------------------------

------------------------------------------------
------- COMBINE UNIT(s) TOGETHER: --------------
------------------------------------------------

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

-- if a Unit has 0 as exponent,
-- it is adimensional and it can just
-- be ignored
simplify-Unit : (u : Unit) → Unit
simplify-Unit u with Unit.type u
-- return 𝕀 if the Unit type (𝕌) is already adimensional
...| adim = 𝕀
-- Considering the value of the exponent...
...| _      with ℚiszero (Unit.exp u)
--           ... if it is zero, it is adimensional
...          | true   = 𝕀
--           ... otherwise the Unit u does not need
--               any simplification
...          | false  = u

-- Simplify-Unit, but for a list of Unit
simplify-Units : (U : Units) → Units
simplify-Units [] = []
simplify-Units (u ∷ U) = (simplify-Unit u) ∷ (simplify-Units U)

-- Combine two Unit elements together in a single Unit
-- IT REQUIRES THE TWO UNIT TO HAVE THE SAME TYPE
_ₓ_ : (a : Unit) → (b : Unit) → Unit
a ₓ b with Unit.type a is Unit.type b
...| true  = simplify-Unit ([_^_] (Unit.type a) (Unit.exp a Data.Rational.+ Unit.exp b))
...| false = 𝕀

-- Combine two (non necessarily equal) Unit element together
-- in a Units type
-- if the two Unit have the same type then the exponents get
-- summed
-- otherwise they just get concatenated
_x_ : (a : Unit) → (b : Unit) → Units
a x b  with Unit.type a is Unit.type b
...| true  = simplify-Units ([_^_] (Unit.type a) (Unit.exp a Data.Rational.+ Unit.exp b) ∷ [])
...| false = simplify-Units (a ∷ (b ∷ []))

-- Combine a Unit element and a List Unit in a List Unit type
-- it checks if there is already a unit with the same type
-- within the list, in that case the two Unit elements become
-- one with the exponent summed
_X_ : (a : Unit) → (B : Units) → Units
a X [] = a ∷ []
a X (b ∷ B) with Unit.type a is Unit.type b
...| true  = simplify-Units ((a ₓ b) ∷ B)
...| false = simplify-Units (b ∷ (a X B))

-- Merge two units together considering Unit elements
-- having the same types
Umerge : (A B : Units) → Units
Umerge [] B = simplify-Units B
Umerge A [] = simplify-Units A
Umerge (a ∷ A) (b ∷ B) with Unit.type a is Unit.type b
...| true  = (a ₓ b) X (Umerge A B)
...| false = b ∷ Umerge (a ∷ A) B

------------------------------------------------
------------------------------------------------

u1 : Unit; u1 = [ s  ^ (+ 1 / 2) ]
u2 : Unit; u2 = [ s  ^ (+ 3 / 2) ]
u3 : Unit; u3 = [ kg ^ (+ 1 / 1) ]
u4 : Unit; u4 = [ m  ^ (-[1+ 0 ] / 1 ) ]

------------------------------------------------
------------------------------------------------

-- MOVING ON:
-- 1. 𝕀needs to be removed in the concatenation
--    functions
-- 2. _is_ can be better
-- 3. I am getting some warnings in:
--      3.1 Umerge
--      3.2 _is_
--      3.3 simplify-Unit
--    because some cases are considered more than
--    once (?).
-- 4. Do not know how to 'return ⊥' when
--    messing up concatenations

------------------------------------------------
------------------------------------------------









