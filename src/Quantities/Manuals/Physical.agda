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

---------------------------------------
-- - PHYSICAL QUANTITIES TYPE (PQ) - --
---------------------------------------
-- How to construct a Physical Type
number = -[1+ 19 ] / 32       -- -20/32 newton
pq1    = number ×[ newton ]
--                   ↑
--                 Units (𝕌s)

-- The quantity can also be shown
pq-string = PQshow pq1
-- which can be displayed by typing pq-string in the
-- evaluate tab
-- Ctrl+c + Ctrl+n
-- >> pq-string
-- "-5/8  [m^(1) g^(1) s^(-2) ]"

----------------
-- EQUALITIES --
----------------
-- A function can tell if two physical quantities can be
-- added together (when they share the same dimensions)

pq2 = 1ℚ ×[ pascal ]              -- 1 pascal
pq3 = (-[1+ 0 ] / 12) ×[ pascal ] -- -1/12 pascal
-- Takes two Physical Quantities. It returns
--  > ⊥ if the two dimensions are NOT the same
--  > ⊤ if the two dimensions are the same
check1 = same-dimension pq2 pq3
check2 = same-dimension pq1 pq2
-- Ctrl+c + Ctrl+n
-- >> check1
--    Agda.Builtin.Unit.⊤
-- >> check2
--    Data.Empty.⊥

----------------
-- OPERATIONS --
----------------
a-length = (+[1+ 4 ] / 3)  ×[ [ meter ^ 1ℚ ]  · I ]
a-time   = (+[1+ 29 ] / 1) ×[ [ second ^ 1ℚ ] · I ]

-- 1. MUTLIPLICATION BETWEEN PQ
a-length×time = a-length PQ× a-time
-- >> PQshow a-length×time
--    "50  [s^(1) m^(1) ]"

-- 2. INVERSION OF A PQ
a-frequency = PQ1/ a-time
-- >> PQshow a-frequency
--    "1/30  [s^(-1) ]"

-- 3. DIVISION BETWEEN PQ
a-speed = a-length PQ÷ a-time
-- >> PQshow a-speed
--    "1/18  [s^(-1) m^(1) ]"

-- 4. ADDITION BETWEEN PQ
another-time =  1ℚ ×[ [ second ^ 1ℚ ] · I ]

time-summed = a-time PQ+ another-time
-- >> PQshow time-summed
--    "31  [s^(1) ]"

-- 5. SUBTRACTION BETWEEN PQ
time-subtracted = another-time PQ- a-time
-- >> PQshow time-subtracted
--    "-29  [s^(1) ]"

-- 6. Multiplication of a PQ with a number
a-speed×3 = a-speed ℚPQ× (+[1+ 2 ] / 1)
-- >> PQshow a-speed×3
--    "1/6  [s^(-1) m^(1) ]"

a-speed×3÷2 = a-speed×3 ℚPQ÷ (+[1+ 1 ] / 1)
-- >> PQshow a-speed×3÷2
--    "1/12  [s^(-1) m^(1) ]"
