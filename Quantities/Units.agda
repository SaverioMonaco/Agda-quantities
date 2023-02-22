-----------------------------------
-- Agda Quantities library
--
-- Units
-----------------------------------


module Quantities.Units where

-- Set for Units

-- Idea: Define a Set for the Units
--       and a constructor
--       After that we can add the prefix
--       and in a separate file we can define
--       the conversion (which involve also the
--       numbers.
data 𝕌 : Set where
  second   : 𝕌 -- time
  meter    : 𝕌 -- lenght
  kilogram : 𝕌 -- mass
  ampere   : 𝕌 -- electric current
  kelvin   : 𝕌 -- temperature
  mole     : 𝕌 -- amout of substance
  candela  : 𝕌 -- luminosity

-- Abbreviations:
s   : 𝕌; s   = second
m   : 𝕌; m   = meter
kg  : 𝕌; kg  = kilogram
A   : 𝕌; A   = ampere
K   : 𝕌; K   = kelvin
mol : 𝕌; mol = mole
cd  : 𝕌; cd  = candela

-- In this way when writing
-- s
-- Agda automatically interpets it as seconds

