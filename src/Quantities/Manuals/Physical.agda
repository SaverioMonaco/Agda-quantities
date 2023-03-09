module Quantities.Manuals.Physical where

open import Quantities.Units.SI.Base
open import Quantities.Units.Composed.Base

-- Import the Physical Quantities modules
open import Quantities.Physical.Base
open import Quantities.Physical.Show renaming (show to PQshow)

-- Import definitions of Units types (newton, area ...)
open import Quantities.Units.Composed.Examples

-- Import helping modules
open import Data.Rational
open import Data.Integer
open import Data.Vec
open import Relation.Binary.PropositionalEquality as EQ
  using (_≡_; _≢_; refl; subst; cong; cong₂; module ≡-Reasoning)
open import Agda.Builtin.Unit

---------------------------------------
-- - PHYSICAL QUANTITIES TYPE (PQ) - --
---------------------------------------

-- CREATE A PHYSICAL QUANTITY
--   A vector and a Units type must be declared
--   with the following constructor _×[_]
1D-quantity = (1ℚ ∷ []) ×[ volume ]

-- The quantity can be shown using the PQshow function
str1 = PQshow 1D-quantity

-- Entering in Evaluation mode (Ctrl+c + Ctrl+n)
-- >> str1
-- "(1, )  [m^(3) ]"

-- Another example, let us define the gravitational acceleration
g-acc = (0ℚ ∷ (( -[1+ 90 ] / 10 ) ∷ (0ℚ ∷ []))) ×[ acceleration ]
str-g = PQshow g-acc

-- Ctrl+c + Ctrl+n
-- >> str-g
-- "(0, -91/10, 0, )  [m^(1) s^(-2) ]"

-- For 1-, 2-, 3-, and 4-dimensional quantities there is a shortcut
-- constructor
mass        = [[ 1ℚ ]]                 ×[ ([ g ^ 1ℚ ] · I) ] 
2d-speed    = [[ +[1+ 3 ] / 1 , 1ℚ ]]  ×[ speed ]
3d-force    = [[ 1ℚ , 1ℚ , 1ℚ ]]      ×[ newton ]
4d-density? = [[ 1ℚ , 0ℚ , 1ℚ , 0ℚ ]] ×[ density ]

-- As for now there is no check if a quantity makes physical sense.
-- Hence, it is possible to create a vector that represents a density

---------------------------------------
-- - ---OPERATIONS FOR SCALARS --- - --
---------------------------------------

-- MULTIPLICATIONS BETWEEN SCALARS

an-area = [[ -[1+ 1 ] / 3 ]] ×[ area ]
something = mass SC× an-area

-- Ctrl+c + Ctrl+n
-- >> PQshow something
-- "(-2/3, )  [m^(2) g^(1) ]"

-- DIVISIONS BETWEEN SCALARS

something-else = _SC÷_ mass an-area {refl} {refl} {step Agda.Builtin.Unit.tt trivial}

-- Ctrl+c + Ctrl+n
-- >> PQshow something-else
-- "(-3/2, )  [m^(-2) g^(1) ]"

---------------------------------------
-- - ---OPERATIONS FOR VECTORS --- - --
---------------------------------------

-- COMPUTE NORM²
a-norm    = PQ-norm² 4d-density?

-- ADDITION BETWEEN VECTORS
--   the two vectors must have same dimensionality and units
other-3dforce = [[ 1ℚ , -[1+ 0 ] / 1 , 1ℚ ]]      ×[ newton ]

sum1 = _PQ+_ 3d-force other-3dforce {refl} {refl}

-- Ctrl+c + Ctrl+n
-- >> PQshow sum1
-- "(2, 0, 2, )  [m^(1) g^(1) s^(-2) ]"

-- SUBTRACTION BETWEEN VECTORS
--   the two vectors must have same dimensionality and units
diff1 = _PQ-_ 3d-force other-3dforce {refl} {refl}

-- Ctrl+c + Ctrl+n
-- >> PWshow diff1
-- "(0, 2, 0, )  [m^(1) g^(1) s^(-2) ]"

-- NUMBER-VECTOR MULTIPLICATION

less-force = (-[1+ 0 ] / 11) PQnum× diff1

-- Ctrl+c + Ctrl+n
-- >> PQshow less-force
-- "(0, -2/11, 0, )  [m^(1) g^(1) s^(-2) ]"

-- SCALAR-VECTOR MULTIPLICATION

mass-x-force = mass PQ× diff1

-- Ctrl+c + Ctrl+n
-- >> PQshow mass-x-force
-- "(0, 2, 0, )  [m^(1) g^(2) s^(-2) ]"
