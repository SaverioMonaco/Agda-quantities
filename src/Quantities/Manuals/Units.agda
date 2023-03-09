module Quantities.Manuals.Units where

-- Import the simple Units (No exponents)
open import Quantities.Units.SI.Base
open import Quantities.Units.SI.Show renaming (show to 𝕌-show)

-- Import the Units type (unit + exponent)
open import Quantities.Units.Composed.Base
open import Quantities.Units.Composed.Show renaming (show to 𝕌s-show)

-- Other
open import Data.Rational
open import Data.Integer

-----------------------------------------------------------------
-- - - - - - - - - - - UNIT TYPE (𝕌)  - - - - - - - - - - - - --
-----------------------------------------------------------------

-- How to Create a Unit type element (single simple quantity)
Area = [ meter ^ (+[1+ 1 ] / 1) ]

-- The definition of Area would be : km²
-- To print it closer to our standard way we can use
-- the show function 𝕌-show:
string-Area = 𝕌-show Area
-- Entering in Evaluation mode (Ctrl+c + Ctrl+n)
-- >> string-Area
-- "m^(2)"

-- The constructor [_^_] automatically transforms
-- a quantity to adimensional (adim) if the exponent is zero

unit1 = [ kelvin ^ 0ℚ ]
-- Ctrl+c + Ctrl+n
-- >> 𝕌-show unit1
-- " ^(1)"

unit2 = [ second ^ +[1+ 0 ] / 2 ]        -- s^½
unit3 = [ second ^ +[1+ 0 ] / 1 ]        -- s
unit4 = [ second ^ +[1+ 0 ] / 2 ]        -- s^½
unit5 = [ candela ^ +[1+ 1 ] / 1 ]       -- cd^2

-- There are two equivalences between Unit types:
-- ----------------------------------------------
-- SIM: (𝕌sim) : (u : 𝕌) → (v : 𝕌) → Bool
-- 𝕌sim is:
--   > true:  if the base is the same
--              (regardless of the prefix)
--   > false: otherwise
--
-- Ctrl+c + Ctrl+n
-- >> 𝕌sim unit2 unit3
-- true
-- >> 𝕌sim unit3 unit4
-- true
-- >> 𝕌sim unit2 unit5
-- false
-- ----------------------------------------------
-- EQ:  (𝕌eq) : (u : 𝕌) → (v : 𝕌) → Bool
-- 𝕌eq is:
--   > true:  if both the base and the exponent
--            are the same
--            (regardless of the prefix)
--   > false: otherwise
--
-- Ctrl+c + Ctrl+n
-- >> 𝕌eq unit2 unit3
-- false
-- >> 𝕌eq unit2 unit4
-- true
-- >> 𝕌eq unit2 unit5
-- false
-- ----------------------------------------------

-- The Operations between Units are:
-- 1. ADDITION (𝕌+) and SUBTRACTION (𝕌-)
Lenght = [ meter ^ 1ℚ ]
Area1  = Lenght 𝕌+ 1ℚ
-- Ctrl+c + Ctrl+n
-- >> 𝕌-show Area1
-- "m^(2)"

-- 2. MULTIPLICATION (𝕌×) and DIVISION (𝕌÷)
Lenght1 = Area1 𝕌× (+[1+ 0 ] / 2)
-- Ctrl+c + Ctrl+n
-- >> 𝕌eq Lenght Lenght1
-- true

-- 3. INVERSION (𝕌inv)
something = 𝕌inv Area1
-- Ctrl+c + Ctrl+n
-- >> 𝕌-show something
-- "m^(1/2)"

-----------------------------------------------------------------
-- - - - - - - - - - - UNITS TYPE (𝕌s)  - - - - - - - - - - - --
-----------------------------------------------------------------

-- How to Create a Composed Unit type element (𝕌s)
-- N = kg · m · s²
newton = [ (g) ^ 1ℚ ] · ( [ m ^ 1ℚ ] · ([ s ^ ( -[1+ 1 ] / 1 ) ] · I) )

-- To show it:
-- Ctrl+c + Ctrl+n
-- >> 𝕌s-show newton
-- "g^(1) m^(1) s^(-2) "

-- Is it possible to insert a unit to a Units type by considering what
-- is inside the Units type.
-- When inserting a Unit into a Units, if the same unit is already
-- inside it, the exponents get summed.
-- This is the operation done when multiplying two physical quantities
-- together.

s^3    = [ s ^ +[1+ 2 ] / 1 ]
m^-3/2 = [ m ^ (-[1+ 2 ] / 2) ] 

something-else = insert m^-3/2 (insert s^3 newton)
-- Ctrl+c + Ctrl+n
-- >> 𝕌s-show something-else
-- "g^(1) m^(-1/2) s^(1) "

-- There is a similar operation called merge,
-- between Units types (𝕌s)
-- This is related to the multiplication of physical quantities
strange-quantity = [ s ^ +[1+ 6 ] / 2 ] · ([ m ^ (-[1+ 0 ] / 1) ] · I)
something-elser  = merge newton strange-quantity
--               = ( g m s^-2 ) (s^7/2 m^-1) = g s^(7/2 -2) m^0 =
--               = g s^(3/2)
-- Ctrl+c + Ctrl+n
-- >> 𝕌s-show something-elser
-- "s^(3/2) g^(1) "

-- There is aswell an operation related to the division of physical
-- quantities:
nothing = ÷-merge newton newton
-- Ctrl+c + Ctrl+n
-- >> 𝕌s-show nothing
-- ""

-- MULTIPLICATION (𝕌s×) and DIVISION (𝕌s÷):
newton√2 = newton 𝕌s÷ (+[1+ 1 ] / 1)
-- Ctrl+c + Ctrl+n
-- >> 𝕌s-show newton
-- "g^(1/2) m^(1/2) s^(-1) "

-- INVERSION:
inv-newton = 𝕌s-inv newton
-- Ctrl+c + Ctrl+n
-- >> 𝕌s-show inv-newton
-- "kilo-g^(1) m^(1) s^(-1/2) "
