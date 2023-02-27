module Quantities.Units.Composed-examples where

open import Quantities.Units.Composed
open import Quantities.Units.SI.Base

-- Other
open import Data.Rational
open import Data.Integer

-- Area = m^2
area         = [ m ^ +[1+ 1 ] / 1 ] · I
-- Volume = m^3
volume       = [ m ^ +[1+ 2 ] / 1 ] · I
-- Density = kg/volume
density      = insert [ kilo- g ^ 1ℚ ] (volume 𝕌s* (-[1+ 0 ] / 1) )
-- Speed = m/s
speed        = [ m ^ +[1+ 0 ] / 1 ] · ([ s ^ -[1+ 0 ] / 1 ] · I)
-- Acceleration = m/s^2
acceleration = [ m ^ +[1+ 0 ] / 1 ] · ([ s ^ -[1+ 1 ] / 1 ] · I)
-- Newton = kg m / s^2
newton       = [ m ^ 1ℚ ] · ([ kilo- g ^ 1ℚ ] · ([ s ^ -[1+ 1 ] / 1 ] · I))
-- Joule = N m
joule        = insert [ m ^ 1ℚ ] newton
-- Power = N m/s
watt         = merge speed newton
-- Pascal = N/m^2
pascal       = insert [ m ^ -[1+ 1 ] / 1 ] newton
