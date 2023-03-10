module Quantities.Physical.Base where

open import Quantities.Units.SI.Base
open import Quantities.Units.Composed.Base as 𝕌s
open import Data.Rational as ℚ
open import Quantities.Units.Composed.Examples
open import Data.Integer
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ; mkℚᵘ; _≢0)
open import Relation.Binary.PropositionalEquality as EQ
  using (_≡_; _≢_; refl; subst; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Bool.Base

import Data.Integer.DivMod as ℤ
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; -[1+_])
open import Relation.Nullary.Decidable using (True)

import Data.Integer.DivMod as ℤ
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ; mkℚᵘ; _≢0)

open import Data.Vec.Base
open import Data.Nat.Base

------------------------------------------------------------------------
-- - - - - - - - - - PHYSICAL QUANTITY (PQ) UNIT TYPE - - - - - - - - --
------------------------------------------------------------------------

-- Quick constructor for 1-dimensional vectors : scalar
[[_]] : (q : ℚ) → Vec ℚ (ℕ.suc zero)
[[_]] q = (q ∷ [])

-- Quick constructor for 2-dimensional vectors
[[_,_]] : (q1 q2 : ℚ) → Vec ℚ (ℕ.suc (ℕ.suc zero))
[[_,_]] q1 q2 = q1 ∷ (q2 ∷ [])

-- Quick constructor for 3-dimensional vectors
[[_,_,_]] : (q1 q2 q3 : ℚ) → Vec ℚ (ℕ.suc (ℕ.suc (ℕ.suc zero)))
[[_,_,_]] q1 q2 q3 = q1 ∷ (q2 ∷ (q3 ∷ []))

-- Quick constructor for 4-dimensional vectors
[[_,_,_,_]] : (q1 q2 q3 q4 : ℚ) → Vec ℚ (ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc zero))))
[[_,_,_,_]] q1 q2 q3 q4 = q1 ∷ (q2 ∷ (q3 ∷ (q4 ∷ [])))

record PQ : Set where
  constructor conPQ
  field
    dim    : ℕ
    vector : Vec ℚ dim
    units  : 𝕌s.𝕌s

-- Constructor for a Physical Quantity Type:
_×[_] : {dim : ℕ} (vector : Vec ℚ dim) (units : 𝕌s) → PQ
_×[_] {dim} vector units = conPQ dim vector (𝕌s.𝕌s-simplify units)

vector1   = [[ 1ℚ , 0ℚ , 0ℚ ]]
quantity1 = vector1 ×[ newton ]

vector2   = [[ 1ℚ , 1ℚ , 1ℚ ]]
quantity2 = vector2 ×[ newton ]

vector3   = [[ 0ℚ , 1ℚ , 0ℚ ]]
quantity3 = vector3 ×[ volume ]
      
--------------------------------------------------
-- - - - - - - - - - OPERATIONS - - - - - - - - --
--------------------------------------------------

-------------- Helping functions  ----------------
vector-add : {n : ℕ} → (vec1 : Vec ℚ n) → (vec2 : Vec ℚ n) → Vec ℚ n
vector-add [] [] = []
vector-add {n} (u ∷ U) (v ∷ V) = (u ℚ.+ v) ∷ (vector-add U V)

vector-sub : {n : ℕ} → (vec1 : Vec ℚ n) → (vec2 : Vec ℚ n) → Vec ℚ n
vector-sub [] [] = []
vector-sub {n} (u ∷ U) (v ∷ V) = (u ℚ.- v) ∷ (vector-sub U V)

vector-mult : {n m : ℕ} → (vec1 : Vec ℚ n) → (vec2 : Vec ℚ m) → {n ≡ m} → Vec ℚ n
vector-mult [] [] = []
vector-mult {n} {m} (u ∷ U) (v ∷ V) {p} = (u ℚ.* v) ∷ (vector-mult U V {cong Data.Nat.Base.pred ( p )})

--------------------------------------------------

--------------------------------------------------
-- OPERATIONS BETWEEN SCALARS --------------------
--------------------------------------------------

-- SCALAR-SCALAR MULTIPLICATION
--   As certificates, it is required that the two physical quantities are
--   indeed scalars
_SC×_ : (pq1 pq2 : PQ) → {(PQ.dim pq1) ≡ (ℕ.suc zero)} →  {(PQ.dim pq2) ≡ (ℕ.suc zero)} → PQ
_SC×_ pq1 pq2 {p1} {p2} =  _×[_] (vector-mult (PQ.vector pq1) (PQ.vector pq2) {EQ.sym (EQ.trans p2 (EQ.sym p1))}) (𝕌s.merge (PQ.units pq1) (PQ.units pq2))

-- Set of certificates that a given vector of rational
-- does NOT containt 0ℚ in it.
-- it is required when performing the inversion of a scalar
data 0∉Vec : {n : ℕ} → (Vec ℚ n) → Set where
  trivial : 0∉Vec []
  step    : {n : ℕ} → {V : Vec ℚ n} → {q : ℚ} → (ℤ.∣ ↥ q ∣ ≢0) → 0∉Vec V → 0∉Vec (q ∷ V)

-- SCALAR INVERSION
--   Apply ^(-1) to a scalar, inverting the physical units
--   aswell.
--   It is required that the physical quantity is both a scalar (dim = 1)
--   and that does not have 0 in its components (which is just one)
SC-inv : (pq : PQ) → {(PQ.dim pq) ≡ (ℕ.suc zero)} → {0∉Vec (PQ.vector pq)} → PQ
SC-inv pq {p1} {p2} = _×[_] (vec-inv (PQ.vector pq) p2) ((PQ.units pq) 𝕌s.𝕌s* (-[1+ 0 ] / 1))
  where
    vec-inv : {n : ℕ} → (vec : Vec ℚ n) → (0∉Vec vec) → Vec ℚ n
    vec-inv [] p = []
    vec-inv (v ∷ V) (step p1 p2) = ((ℚ.1/ v) {p1}) ∷ (vec-inv V p2)

-- SCALAR DIVISION
--   Divide a scalar to another scalar. It is required that both quantities
--   are scalars and that the second scalar can be inverted
_SC÷_ : (pq1 pq2 : PQ) → {(PQ.dim pq1) ≡ (ℕ.suc zero)} →  {(PQ.dim pq2) ≡ (ℕ.suc zero)} → {0∉Vec (PQ.vector pq2)} → PQ
_SC÷_ pq1 pq2 {p1} {p2} {p3} = _SC×_ pq1 (SC-inv pq2 {p2} {p3}) {p1} {p2}

--------------------------------------------------
-- VECTORIAL AND SCALAR OPERATIONS ---------------
--------------------------------------------------

-- NORM SQUARED
--   Computers the norm squared of a the vector of
--   a quantity.
--   (The norm cannot be computed without irrational numbers)
PQ-norm² : (pq : PQ) → ℚ
PQ-norm² pq = vec-norm² (PQ.vector pq)
  where
    vec-norm² : {n : ℕ} (vec : Vec ℚ n) → ℚ
    vec-norm² [] = 0ℚ
    vec-norm² (v ∷ V) = (v ℚ.* v) ℚ.+ (vec-norm² V)

-- ADDITION
--   addition between physical quantities
--   You must provide a proof that:
--   1. the two physical quantities have the same (vectorial) dimension
--   2. the two physical quantities have the same units
_PQ+_ : (pq1 pq2 : PQ) → {(PQ.dim pq1) ≡ (PQ.dim pq2)} → {𝕌s.÷-merge (PQ.units pq1) (PQ.units pq2) ≡ I} → PQ
_PQ+_ pq1 pq2 {refl} = _×[_] {PQ.dim pq1} (vector-add (PQ.vector pq1) (PQ.vector pq2)) (PQ.units pq1)

-- SUBTRACTION
--   same as addition, but the components will be subtracted
_PQ-_ : (pq1 pq2 : PQ) → {(PQ.dim pq1) ≡ (PQ.dim pq2)} → {𝕌s.÷-merge (PQ.units pq1) (PQ.units pq2) ≡ I} → PQ
_PQ-_ pq1 pq2 {refl} = _×[_] {PQ.dim pq1} (vector-sub (PQ.vector pq1) (PQ.vector pq2)) (PQ.units pq1)

-- NUMBER × QUANTITY OPERATION
_PQnum×_ : (num : ℚ) → (pq : PQ) → PQ
_PQnum×_ num pq = _×[_] (scalar-times-vec num (PQ.vector pq)) (PQ.units pq)
  where
    scalar-times-vec : {n : ℕ} → ℚ → Vec ℚ n → Vec ℚ n
    scalar-times-vec {.zero} s [] = []
    scalar-times-vec {.(ℕ.suc _)} s (v ∷ V) = (s ℚ.* v) ∷ (scalar-times-vec s V)

-- SCALAR × QUANTITY OPERATION
_PQ×_ : (pq1 pq2 : PQ) → {(PQ.dim pq1) ≡ (ℕ.suc zero)} → PQ
_PQ×_ pq1 pq2 {p} = _×[_] (PQ.vector ((PQ-to-q pq1 {p}) PQnum× pq2)) (merge (PQ.units pq1) (PQ.units pq2))
  where
    PQ-to-q : (pq : PQ) → {(PQ.dim pq) ≡ (ℕ.suc zero)} → ℚ
    PQ-to-q (conPQ (ℕ.suc zero) (x ∷ []) units) {p} = x

--------------------------------------------------
-- Impossible operations:
-- 1. You cannot add two vectors of different dimensions
--    (this includes additions between a vector and a scalar)
-- 2. You cannot just multiply two vectors. You either
--    scalar multiply them or vector multiply them

----------------------------------------------------------------
--|   MISSING OPERATIONS     |     WHY THEY ARE MISSING        |
--|--------------------------|---------------------------------|
--| 1. Scalar multiplication : cos(theta) is an irrational     |
--|                          | number                          |
--|--------------------------|---------------------------------|
--| 2. Vector multiplication : sin(theta) is an irrational     |
--|                          | number                          |
--|--------------------------|---------------------------------|
--| 3. Conversion between    | conversion between derived      |
--|    derived units         : units may result in irratiional |
--|    eg: gram -> kilogram  | numbers when the starting expo- |
--|                          | nent is rational                |
--|                          | eg: kg^¾ -> ? g^¾               |
--|                          |          -> (1000)^¾ g^¾        |
--|--------------------------|---------------------------------|
