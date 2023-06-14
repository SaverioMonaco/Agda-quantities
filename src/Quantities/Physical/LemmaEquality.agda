module Quantities.Physical.LemmaEquality where

open import Quantities.Physical.Base
open import Quantities.Units.U_Equality
open import Quantities.Units.Composed.Base as 𝕌s
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Vec.Base
open import Data.Rational.Base

lemma-units : {dim1 dim2 : ℕ} {vector1 : Vec ℚ dim1} {vector2 : Vec ℚ dim2} {units1 units2 : 𝕌s} → (conPQ dim1 vector1 units1) ≡ (conPQ dim2 vector2 units2) → units1 ≡ᵤ units2
lemma-units refl = permRefl

lemma-units2 : {pq1 pq2 : PQ} → pq1 ≡ pq2 → (PQ.units pq1) ≡ᵤ (PQ.units pq2) 
lemma-units2 refl = permRefl
