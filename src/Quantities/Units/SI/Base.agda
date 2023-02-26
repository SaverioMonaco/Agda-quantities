module Quantities.Units.SI.Base where

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Integer.Base
open import Data.Rational.Base renaming (NonZero to ℚNonZero; 1/_ to ℚ1/_; _*_ to _ℚ*_; _+_ to _ℚ+_; _-_ to _ℚ-_; _÷_ to _ℚ÷_)
open import Data.String.Base using (String)
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; -[1+_])
import Data.Integer.DivMod as ℤ
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ; mkℚᵘ; _≢0)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

-----------------------
-- Helping Functions --
-----------------------
ℤiszero : (z : ℤ) → Bool
ℤiszero (+0)       = true  --  0
ℤiszero +[1+ n ]   = false -- +1, +2, +3, ...
ℤiszero (-[1+_] n) = false -- -1, -2, -3, ...
----------------------
----------------------

------------------------------------
-- - - - - BASE-UNIT TYPE - - - - --
------------------------------------

record Prefix : Set where
  constructor c-Prefix
  field
    str   : String
    10pow : ℤ

record b𝕌 : Set where
  constructor c-b𝕌
  field
    prefix  : Prefix
    id-num  : ℕ
    str     : String
    
----------------------------------
-- - - - - - PREFIXES - - - - - --
----------------------------------

exa   = c-Prefix "exa-"   +[1+ 17 ]  -- 10^18
peta  = c-Prefix "peta-"  +[1+ 14 ]  -- 10^15
tera  = c-Prefix "tera-"  +[1+ 11 ]  -- 10^12
giga  = c-Prefix "giga-"  +[1+ 8  ]  -- 10^9
mega  = c-Prefix "mega-"  +[1+ 5  ]  -- 10^6
kilo  = c-Prefix "kilo-"  +[1+ 2  ]  -- 1000
hecto = c-Prefix "hecto-" +[1+ 1  ]  -- 100
deka  = c-Prefix "deka-"  +[1+ 0  ]  -- 10
id-   = c-Prefix ""       +0         -- 1
deci  = c-Prefix "deci-"  -[1+ 0  ]  -- 0.1
centi = c-Prefix "centi-" -[1+ 1  ]  -- 0.01
milli = c-Prefix "milli-" -[1+ 2  ]  -- 0.001
micro = c-Prefix "micro-" -[1+ 5  ]  -- 10^(-6)
nano  = c-Prefix "nano-"  -[1+ 8  ]  -- 10^(-9)
pico  = c-Prefix "pico-"  -[1+ 11 ]  -- 10^(-12)
femto = c-Prefix "femto-" -[1+ 14 ]  -- 10^(-15)
atto  = c-Prefix "atto-"  -[1+ 17 ]  -- 10^(-18)

------------------------------------
-- - - - - - BASE UNITS - - - - - --
------------------------------------
adim    : b𝕌; adim    = c-b𝕌 id- 0 " "
second  : b𝕌; second  = c-b𝕌 id- 1 "s"
meter   : b𝕌; meter   = c-b𝕌 id- 2 "m"
gram    : b𝕌; gram    = c-b𝕌 id- 3 "g"
ampere  : b𝕌; ampere  = c-b𝕌 id- 4 "A"
kelvin  : b𝕌; kelvin  = c-b𝕌 id- 5 "K"
mole    : b𝕌; mole    = c-b𝕌 id- 6 "mol"
candela : b𝕌; candela = c-b𝕌 id- 7 "cd"

-- Abbreviations:
s   : b𝕌; s   = second
m   : b𝕌; m   = meter
g   : b𝕌; g   = gram
A   : b𝕌; A   = ampere
K   : b𝕌; K   = kelvin
mol : b𝕌; mol = mole
cd  : b𝕌; cd  = candela

----------------------------------------------
-- - - - - - CONVERSION FUNCTIONS - - - - - --
----------------------------------------------
-- Each of the following function transforms a base unit with
-- the base unit with the given prefix

--         |-> ...
--         |-> deka- meter
--  meter -|->       meter
--         |-> deci- meter
--         |-> ...

exa-   : (u : b𝕌) → b𝕌; exa-   u = c-b𝕌 exa   (b𝕌.id-num u) (b𝕌.str u)
peta-  : (u : b𝕌) → b𝕌; peta-  u = c-b𝕌 peta  (b𝕌.id-num u) (b𝕌.str u)
tera-  : (u : b𝕌) → b𝕌; tera-  u = c-b𝕌 tera  (b𝕌.id-num u) (b𝕌.str u)
giga-  : (u : b𝕌) → b𝕌; giga-  u = c-b𝕌 giga  (b𝕌.id-num u) (b𝕌.str u) 
mega-  : (u : b𝕌) → b𝕌; mega-  u = c-b𝕌 mega  (b𝕌.id-num u) (b𝕌.str u)
kilo-  : (u : b𝕌) → b𝕌; kilo-  u = c-b𝕌 kilo  (b𝕌.id-num u) (b𝕌.str u)
hecto- : (u : b𝕌) → b𝕌; hecto- u = c-b𝕌 hecto (b𝕌.id-num u) (b𝕌.str u)
deka-  : (u : b𝕌) → b𝕌; deka-  u = c-b𝕌 deka  (b𝕌.id-num u) (b𝕌.str u) 
deci-  : (u : b𝕌) → b𝕌; deci-  u = c-b𝕌 deci  (b𝕌.id-num u) (b𝕌.str u)
centi- : (u : b𝕌) → b𝕌; centi- u = c-b𝕌 centi (b𝕌.id-num u) (b𝕌.str u)
milli- : (u : b𝕌) → b𝕌; milli- u = c-b𝕌 milli (b𝕌.id-num u) (b𝕌.str u)
micro- : (u : b𝕌) → b𝕌; micro- u = c-b𝕌 micro (b𝕌.id-num u) (b𝕌.str u)
nano-  : (u : b𝕌) → b𝕌; nano-  u = c-b𝕌 nano  (b𝕌.id-num u) (b𝕌.str u)
pico-  : (u : b𝕌) → b𝕌; pico-  u = c-b𝕌 pico  (b𝕌.id-num u) (b𝕌.str u)
femto- : (u : b𝕌) → b𝕌; femto- u = c-b𝕌 femto (b𝕌.id-num u) (b𝕌.str u)
atto-  : (u : b𝕌) → b𝕌; atto-  u = c-b𝕌 atto  (b𝕌.id-num u) (b𝕌.str u)

-------------------------------
-- - - - - UNIT TYPE - - - - --
-------------------------------

-- Unit type (𝕌): it takes a base-unit type and an exponent
-- Example:
-- milli- meter is a base Unit type
-- [ milli- meter ^ 3 ] is a Unit type
record 𝕌 : Set where
    constructor con𝕌
    field
      base : b𝕌
      expo : ℚ

-- This postulate states that every exponent is not zero
-- which is not technically true since it is possible to
-- use con𝕌 to construct a Unit with 0 as exponent.
-- However the following constructor [_^_] will avoid that
-- as well as all the (following) operations.
postulate 𝕌pos1 : (U : 𝕌) → ℤ.∣ ↥ 𝕌.expo U ∣ ≢0

-- Constructor of the Unit type
-- [ (base-u : b𝕌) ^ (expo : ℚ) ]
-- It also checks wether the inputted exponent
-- if zero, in that case it transform the unit in
-- the basic adimensional one 
[_^_] : (base : b𝕌) (expo : ℚ) → 𝕌
[_^_] base expo with (ℤiszero (ℚ.numerator expo))
...| true  = con𝕌 adim (+[1+ 0 ] / 1 )
...| false = con𝕌 base expo

--------------------------------------------
-- - - - - - - - EQUALITIES - - - - - - - -- 
--------------------------------------------

-- true:  if the base is the same
-- false: otherwise
𝕌sim : (u v : 𝕌) → Bool
𝕌sim u v with (ℕeq (b𝕌.id-num (𝕌.base u)) (b𝕌.id-num (𝕌.base v)))
  where
    ℕeq : (n m : ℕ) → Bool
    ℕeq zero zero             = true
    ℕeq zero (ℕ.suc m)       = false
    ℕeq (ℕ.suc n) zero       = false
    ℕeq (ℕ.suc n) (ℕ.suc m) = ℕeq n m
...| bool = bool

-- true:  if both base and exponent are the same
-- false: otherwise
𝕌eq : (u v : 𝕌) → Bool
𝕌eq u v with 𝕌sim u v | ℚeq (𝕌.expo u) (𝕌.expo v)
  where
    ℕeq : (n m : ℕ) → Bool
    ℕeq zero zero             = true
    ℕeq zero (ℕ.suc m)       = false
    ℕeq (ℕ.suc n) zero       = false
    ℕeq (ℕ.suc n) (ℕ.suc m) = ℕeq n m
    
    ℤeq : (z x : ℤ) → Bool
    ℤeq (+_ n) (+_ m) = ℕeq n m
    ℤeq (-[1+_] n) (+_ m) = false
    ℤeq (+_ n) (-[1+_] m) = false
    ℤeq (-[1+_] n) (-[1+_] m) = ℕeq n m
    
    ℚeq : (q p : ℚ) → Bool
    ℚeq p q with ℤeq (ℚ.numerator p) (ℚ.numerator q) | ℕeq (ℚ.denominatorℕ p) (ℚ.denominatorℕ q)
    ... | false | _    = false
    ... | true  | bool = bool
... | false | _    = false
... | true  | bool = bool

--------------------------------------------
-- - - - - - - - OPERATIONS - - - - - - - -- 
--------------------------------------------

-- This function reduces a Unit into Adimensional
-- in case that its exponent is 0
-- Example : m^0 does not mean anything
-- While performing calculations, if we multiply m and m^(-1)
-- we get m^0 while in reality is just an adimensional number
-- By contruction, the Unit type automatically removes any dimension
-- with a 0 exponent.
-- This function will be used while combining Units
𝕌-simplify : (u : 𝕌) → 𝕌
𝕌-simplify u  with ℤiszero (ℚ.numerator (𝕌.expo u) )
...| true  = con𝕌 adim (+[1+ 0 ] / 1 )
...| false = u

-- 1. ADDITION
-- (u : 𝕌) 𝕌+ (q : ℚ) → (w : 𝕌)
-- Performs the addition of the exponent of
-- the unit by a rational number
_𝕌+_ : (u : 𝕌) → (q : ℚ) → 𝕌
_𝕌+_ u q = [_^_] (𝕌.base u) (𝕌.expo u ℚ+ q)

-- 2. SUBTRACTION
-- (u : 𝕌) 𝕌- (q : ℚ) → (w : 𝕌)
-- Performs the subtraction of the exponent of
-- the unit by a rational number
_𝕌-_ : (u : 𝕌) → (q : ℚ) → 𝕌
_𝕌-_ u q = [_^_] (𝕌.base u) (𝕌.expo u ℚ- q)

-- 3. MULTIPLICATION
-- (u : 𝕌) 𝕌× (q : ℚ) → (w : 𝕌)
-- multiply the exponent of a Unit by a
-- rational number
_𝕌×_ : (u : 𝕌) → (q : ℚ) → 𝕌
_𝕌×_ u q = [_^_] (𝕌.base u) (𝕌.expo u ℚ* q) 

-- 4. DIVISION
-- (u : 𝕌) 𝕌÷ (q : ℚ) → (w : 𝕌)
-- divide the exponent of a Unit by a
-- rational number
_𝕌÷_ : (u : 𝕌) → (q : ℚ) → .{n≢0 : ℤ.∣ ↥ q ∣ ≢0} → 𝕌
_𝕌÷_ u q {n≢0} with (ℚ1/ q) {n≢0}
...| 1/q = _𝕌×_ u 1/q

-- 5. INVERSION
-- 𝕌inv (u : 𝕌) → (w : 𝕌)
-- divide the exponent of a Unit by a
-- rational number
𝕌inv : (u : 𝕌) → .{n≢0 : ℤ.∣ ↥ ( 𝕌.expo u ) ∣ ≢0} → 𝕌
𝕌inv u {n≢0} with (ℚ1/ ( 𝕌.expo u )) {n≢0}
...| 1/expo = [_^_] (𝕌.base u) (1/expo)

-- 6. SUM EXPONENTS
-- 𝕌sum-exp (u : 𝕌) → (v : 𝕌) → (w : 𝕌)
-- Creates a new Unit by summing the exponents.
-- It is intended to be used internally by two
-- Unit elements with the same base.
-- However if the base is different the resultin
-- type will be adimensional
𝕌sum-exp : (u v : 𝕌) → 𝕌
𝕌sum-exp u v with 𝕌sim u v
...| true  = [_^_] (𝕌.base u) (( (𝕌.expo u) ℚ+ (𝕌.expo v) ))
...| false = [_^_] (adim)      (( (𝕌.expo u) ℚ+ (𝕌.expo v) ))
--------------------------------------------
--------------------------------------------
