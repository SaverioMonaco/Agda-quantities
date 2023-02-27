module Quantities.Units.Composed.Show where

open import Quantities.Units.SI.Show using () renaming (show to show𝕌)
open import Quantities.Units.Composed.Base
open import Data.String.Base using (String; _++_)

-- show function for the Units type. It iteratively
-- applies Quantities.Units.SI.Show function for every
-- Unit element
show : (U : 𝕌s) → String
show I       = ""
show (u · U) = (show𝕌 u) ++ " " ++  (show U)

-- EXAMPLES:
-- newton : 𝕌s; newton = [ (kilo- g) ^ 1ℚ ] · ( [ m ^ 1ℚ ] · ([ s ^ ( -[1+ 1 ] / 1 ) ] · I) )
-- >> show newton
-- "kilo-g^(1) m^(1) s^(-2) "

