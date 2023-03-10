module Quantities.Manuals.Units where

-- Import the simple Units (No exponents)
open import Quantities.Units.SI.Base
open import Quantities.Units.SI.Show renaming (show to ð-show)

-- Import the Units type (unit + exponent)
open import Quantities.Units.Composed.Base
open import Quantities.Units.Composed.Show renaming (show to ðs-show)

-- Other
open import Data.Rational
open import Data.Integer

-----------------------------------------------------------------
-- - - - - - - - - - - UNIT TYPE (ð)  - - - - - - - - - - - - --
-----------------------------------------------------------------

-- How to Create a Unit type element (single simple quantity)
Area = [ meter ^ (+[1+ 1 ] / 1) ]

-- The definition of Area would be : kmÂ²
-- To print it closer to our standard way we can use
-- the show function ð-show:
string-Area = ð-show Area
-- Entering in Evaluation mode (Ctrl+c + Ctrl+n)
-- >> string-Area
-- "m^(2)"

-- The constructor [_^_] automatically transforms
-- a quantity to adimensional (adim) if the exponent is zero

unit1 = [ kelvin ^ 0â ]
-- Ctrl+c + Ctrl+n
-- >> ð-show unit1
-- " ^(1)"

unit2 = [ second ^ +[1+ 0 ] / 2 ]        -- s^Â½
unit3 = [ second ^ +[1+ 0 ] / 1 ]        -- s
unit4 = [ second ^ +[1+ 0 ] / 2 ]        -- s^Â½
unit5 = [ candela ^ +[1+ 1 ] / 1 ]       -- cd^2

-- There are two equivalences between Unit types:
-- ----------------------------------------------
-- SIM: (ðsim) : (u : ð) â (v : ð) â Bool
-- ðsim is:
--   > true:  if the base is the same
--              (regardless of the prefix)
--   > false: otherwise
--
-- Ctrl+c + Ctrl+n
-- >> ðsim unit2 unit3
-- true
-- >> ðsim unit3 unit4
-- true
-- >> ðsim unit2 unit5
-- false
-- ----------------------------------------------
-- EQ:  (ðeq) : (u : ð) â (v : ð) â Bool
-- ðeq is:
--   > true:  if both the base and the exponent
--            are the same
--            (regardless of the prefix)
--   > false: otherwise
--
-- Ctrl+c + Ctrl+n
-- >> ðeq unit2 unit3
-- false
-- >> ðeq unit2 unit4
-- true
-- >> ðeq unit2 unit5
-- false
-- ----------------------------------------------

-- The Operations between Units are:
-- 1. ADDITION (ð+) and SUBTRACTION (ð-)
Lenght = [ meter ^ 1â ]
Area1  = Lenght ð+ 1â
-- Ctrl+c + Ctrl+n
-- >> ð-show Area1
-- "m^(2)"

-- 2. MULTIPLICATION (ðÃ) and DIVISION (ðÃ·)
Lenght1 = Area1 ðÃ (+[1+ 0 ] / 2)
-- Ctrl+c + Ctrl+n
-- >> ðeq Lenght Lenght1
-- true

-- 3. INVERSION (ðinv)
something = ðinv Area1
-- Ctrl+c + Ctrl+n
-- >> ð-show something
-- "m^(1/2)"

-----------------------------------------------------------------
-- - - - - - - - - - - UNITS TYPE (ðs)  - - - - - - - - - - - --
-----------------------------------------------------------------

-- How to Create a Composed Unit type element (ðs)
-- N = kg Â· m Â· sÂ²
newton = [ (g) ^ 1â ] Â· ( [ m ^ 1â ] Â· ([ s ^ ( -[1+ 1 ] / 1 ) ] Â· I) )

-- To show it:
-- Ctrl+c + Ctrl+n
-- >> ðs-show newton
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
-- >> ðs-show something-else
-- "g^(1) m^(-1/2) s^(1) "

-- There is a similar operation called merge,
-- between Units types (ðs)
-- This is related to the multiplication of physical quantities
strange-quantity = [ s ^ +[1+ 6 ] / 2 ] Â· ([ m ^ (-[1+ 0 ] / 1) ] Â· I)
something-elser  = merge newton strange-quantity
--               = ( g m s^-2 ) (s^7/2 m^-1) = g s^(7/2 -2) m^0 =
--               = g s^(3/2)
-- Ctrl+c + Ctrl+n
-- >> ðs-show something-elser
-- "s^(3/2) g^(1) "

-- There is aswell an operation related to the division of physical
-- quantities:
nothing = Ã·-merge newton newton
-- Ctrl+c + Ctrl+n
-- >> ðs-show nothing
-- ""

-- MULTIPLICATION (ðsÃ) and DIVISION (ðsÃ·):
newtonâ2 = newton ðsÃ· (+[1+ 1 ] / 1)
-- Ctrl+c + Ctrl+n
-- >> ðs-show newton
-- "g^(1/2) m^(1/2) s^(-1) "

-- INVERSION:
inv-newton = ðs-inv newton
-- Ctrl+c + Ctrl+n
-- >> ðs-show inv-newton
-- "kilo-g^(1) m^(1) s^(-1/2) "
