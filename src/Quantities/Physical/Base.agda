module Quantities.Physical.Base where

open import Quantities.Units.SI.Base
open import Quantities.Units.Composed.Base as πs
open import Data.Rational as β
open import Quantities.Units.Composed.Examples
open import Data.Integer
open import Data.Rational.Unnormalised.Base as βα΅ using (βα΅; mkβα΅; _β’0)
open import Relation.Binary.PropositionalEquality as EQ
  using (_β‘_; _β’_; refl; subst; cong; congβ; module β‘-Reasoning)
open β‘-Reasoning
open import Data.Bool.Base

import Data.Integer.DivMod as β€
open import Data.Integer.Base as β€ using (β€; +_; +0; -[1+_])
open import Relation.Nullary.Decidable using (True)

import Data.Integer.DivMod as β€
open import Data.Rational.Unnormalised.Base as βα΅ using (βα΅; mkβα΅; _β’0)

open import Data.Vec.Base
open import Data.Nat.Base

------------------------------------------------------------------------
-- - - - - - - - - - PHYSICAL QUANTITY (PQ) UNIT TYPE - - - - - - - - --
------------------------------------------------------------------------

-- Quick constructor for 1-dimensional vectors : scalar
[[_]] : (q : β) β Vec β (β.suc zero)
[[_]] q = (q β· [])

-- Quick constructor for 2-dimensional vectors
[[_,_]] : (q1 q2 : β) β Vec β (β.suc (β.suc zero))
[[_,_]] q1 q2 = q1 β· (q2 β· [])

-- Quick constructor for 3-dimensional vectors
[[_,_,_]] : (q1 q2 q3 : β) β Vec β (β.suc (β.suc (β.suc zero)))
[[_,_,_]] q1 q2 q3 = q1 β· (q2 β· (q3 β· []))

-- Quick constructor for 4-dimensional vectors
[[_,_,_,_]] : (q1 q2 q3 q4 : β) β Vec β (β.suc (β.suc (β.suc (β.suc zero))))
[[_,_,_,_]] q1 q2 q3 q4 = q1 β· (q2 β· (q3 β· (q4 β· [])))

record PQ : Set where
  constructor conPQ
  field
    dim    : β
    vector : Vec β dim
    units  : πs.πs

-- Constructor for a Physical Quantity Type:
_Γ[_] : {dim : β} (vector : Vec β dim) (units : πs) β PQ
_Γ[_] {dim} vector units = conPQ dim vector (πs.πs-simplify units)

vector1   = [[ 1β , 0β , 0β ]]
quantity1 = vector1 Γ[ newton ]

vector2   = [[ 1β , 1β , 1β ]]
quantity2 = vector2 Γ[ newton ]

vector3   = [[ 0β , 1β , 0β ]]
quantity3 = vector3 Γ[ volume ]
      
--------------------------------------------------
-- - - - - - - - - - OPERATIONS - - - - - - - - --
--------------------------------------------------

-------------- Helping functions  ----------------
vector-add : {n : β} β (vec1 : Vec β n) β (vec2 : Vec β n) β Vec β n
vector-add [] [] = []
vector-add {n} (u β· U) (v β· V) = (u β.+ v) β· (vector-add U V)

vector-sub : {n : β} β (vec1 : Vec β n) β (vec2 : Vec β n) β Vec β n
vector-sub [] [] = []
vector-sub {n} (u β· U) (v β· V) = (u β.- v) β· (vector-sub U V)

vector-mult : {n m : β} β (vec1 : Vec β n) β (vec2 : Vec β m) β {n β‘ m} β Vec β n
vector-mult [] [] = []
vector-mult {n} {m} (u β· U) (v β· V) {p} = (u β.* v) β· (vector-mult U V {cong Data.Nat.Base.pred ( p )})

--------------------------------------------------

--------------------------------------------------
-- OPERATIONS BETWEEN SCALARS --------------------
--------------------------------------------------

-- SCALAR-SCALAR MULTIPLICATION
--   As certificates, it is required that the two physical quantities are
--   indeed scalars
_SCΓ_ : (pq1 pq2 : PQ) β {(PQ.dim pq1) β‘ (β.suc zero)} β  {(PQ.dim pq2) β‘ (β.suc zero)} β PQ
_SCΓ_ pq1 pq2 {p1} {p2} =  _Γ[_] (vector-mult (PQ.vector pq1) (PQ.vector pq2) {EQ.sym (EQ.trans p2 (EQ.sym p1))}) (πs.merge (PQ.units pq1) (PQ.units pq2))

-- Set of certificates that a given vector of rational
-- does NOT containt 0β in it.
-- it is required when performing the inversion of a scalar
data 0βVec : {n : β} β (Vec β n) β Set where
  trivial : 0βVec []
  step    : {n : β} β {V : Vec β n} β {q : β} β (β€.β£ β₯ q β£ β’0) β 0βVec V β 0βVec (q β· V)

-- SCALAR INVERSION
--   Apply ^(-1) to a scalar, inverting the physical units
--   aswell.
--   It is required that the physical quantity is both a scalar (dim = 1)
--   and that does not have 0 in its components (which is just one)
SC-inv : (pq : PQ) β {(PQ.dim pq) β‘ (β.suc zero)} β {0βVec (PQ.vector pq)} β PQ
SC-inv pq {p1} {p2} = _Γ[_] (vec-inv (PQ.vector pq) p2) ((PQ.units pq) πs.πs* (-[1+ 0 ] / 1))
  where
    vec-inv : {n : β} β (vec : Vec β n) β (0βVec vec) β Vec β n
    vec-inv [] p = []
    vec-inv (v β· V) (step p1 p2) = ((β.1/ v) {p1}) β· (vec-inv V p2)

-- SCALAR DIVISION
--   Divide a scalar to another scalar. It is required that both quantities
--   are scalars and that the second scalar can be inverted
_SCΓ·_ : (pq1 pq2 : PQ) β {(PQ.dim pq1) β‘ (β.suc zero)} β  {(PQ.dim pq2) β‘ (β.suc zero)} β {0βVec (PQ.vector pq2)} β PQ
_SCΓ·_ pq1 pq2 {p1} {p2} {p3} = _SCΓ_ pq1 (SC-inv pq2 {p2} {p3}) {p1} {p2}

--------------------------------------------------
-- VECTORIAL AND SCALAR OPERATIONS ---------------
--------------------------------------------------

-- NORM SQUARED
--   Computers the norm squared of a the vector of
--   a quantity.
--   (The norm cannot be computed without irrational numbers)
PQ-normΒ² : (pq : PQ) β β
PQ-normΒ² pq = vec-normΒ² (PQ.vector pq)
  where
    vec-normΒ² : {n : β} (vec : Vec β n) β β
    vec-normΒ² [] = 0β
    vec-normΒ² (v β· V) = (v β.* v) β.+ (vec-normΒ² V)

-- ADDITION
--   addition between physical quantities
--   You must provide a proof that:
--   1. the two physical quantities have the same (vectorial) dimension
--   2. the two physical quantities have the same units
_PQ+_ : (pq1 pq2 : PQ) β {(PQ.dim pq1) β‘ (PQ.dim pq2)} β {πs.Γ·-merge (PQ.units pq1) (PQ.units pq2) β‘ I} β PQ
_PQ+_ pq1 pq2 {refl} = _Γ[_] {PQ.dim pq1} (vector-add (PQ.vector pq1) (PQ.vector pq2)) (PQ.units pq1)

-- SUBTRACTION
--   same as addition, but the components will be subtracted
_PQ-_ : (pq1 pq2 : PQ) β {(PQ.dim pq1) β‘ (PQ.dim pq2)} β {πs.Γ·-merge (PQ.units pq1) (PQ.units pq2) β‘ I} β PQ
_PQ-_ pq1 pq2 {refl} = _Γ[_] {PQ.dim pq1} (vector-sub (PQ.vector pq1) (PQ.vector pq2)) (PQ.units pq1)

-- NUMBER Γ QUANTITY OPERATION
_PQnumΓ_ : (num : β) β (pq : PQ) β PQ
_PQnumΓ_ num pq = _Γ[_] (scalar-times-vec num (PQ.vector pq)) (PQ.units pq)
  where
    scalar-times-vec : {n : β} β β β Vec β n β Vec β n
    scalar-times-vec {.zero} s [] = []
    scalar-times-vec {.(β.suc _)} s (v β· V) = (s β.* v) β· (scalar-times-vec s V)

-- SCALAR Γ QUANTITY OPERATION
_PQΓ_ : (pq1 pq2 : PQ) β {(PQ.dim pq1) β‘ (β.suc zero)} β PQ
_PQΓ_ pq1 pq2 {p} = _Γ[_] (PQ.vector ((PQ-to-q pq1 {p}) PQnumΓ pq2)) (merge (PQ.units pq1) (PQ.units pq2))
  where
    PQ-to-q : (pq : PQ) β {(PQ.dim pq) β‘ (β.suc zero)} β β
    PQ-to-q (conPQ (β.suc zero) (x β· []) units) {p} = x

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
--|                          | eg: kg^ΒΎ -> ? g^ΒΎ               |
--|                          |          -> (1000)^ΒΎ g^ΒΎ        |
--|--------------------------|---------------------------------|
