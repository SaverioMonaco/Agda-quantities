module Quantities.Units.SI.Show where

open import Data.Bool.Base
open import Data.Nat.Base
open import Quantities.Units.SI.Base
open import Data.String.Base using (String; _++_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.Rational.Base

-- Show function for Unit types:
-- If denominator of the exponent is 1, then the exponent
-- will be printed as an Integer
show : (u : 𝕌) → String
show u with denominator-is-one (𝕌.expo u)
  where
    denominator-is-one : (q : ℚ) → Bool
    denominator-is-one q with (ℕisone (ℚ.denominatorℕ q) )
      where
        ℕisone : (n : ℕ) → Bool
        ℕisone zero          = false
        ℕisone (suc zero)    = true
        ℕisone (suc (suc n)) = false
    ...| bool = bool
...| true  = b𝕌.str (𝕌.base u)  ++ "^(" ++ showℤ (ℚ.numerator (𝕌.expo u) ) ++  ")"
...| false = b𝕌.str (𝕌.base u)  ++ "^(" ++ showℤ (ℚ.numerator (𝕌.expo u) ) ++  "/" ++ showℕ (ℚ.denominatorℕ (𝕌.expo u) ) ++ ")"

-- EXAMPLES:
-- ν    = [ (s) ^ ( -[1+ 0 ] / 1) ]
-- >> show ν
-- "s^(-1)"
-- Area = [ (m) ^ (+[1+ 1 ] / 1) ]
-- >> show Area
-- "m^(2)"
-- idk  = [ (cd) ^ ( 0ℚ ) ]
-- >> show idk
-- " ^(0)"
--idk2 = [ (g)  ^ ( -[1+ 8 ] / 2) ]
-- >> show idk2
-- "g^(-9/2)"

