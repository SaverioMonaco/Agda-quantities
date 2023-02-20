-------------------------------
-- TUTORIAL: Integer Numbers --
-------------------------------

-- Import the dedicated files:
open import Data.Integer.Base

-- In Agda stdlib (and Builtin) the Integers are defined
-- on top on the naturals ℕ.
--

-- This is how you define an integer:
x : ℤ
x = + 1       -- x = +1

y : ℤ
y = -[1+ 0 ]  -- y = -1

z : ℤ
z = -[1+ 3 ]  -- z = -4

-- Why do we write -[1+ 3 ] instead of -4?
-- Integers ℤ are defined on top of ℕ,
-- + n : n ∈ ℕ      is a constructor that outputs
--                   a positive integer ℤ (zero
--                   INCLUDED) from a natural ℕ
-- -[1+ n ] : n ∈ ℕ is a constuctor that outputs
--                   a negative integer ℤ (zero
--                   EXCLUDED) from a natural ℕ
--
-- - n : n ∈ ℕ      would not work because it
--                   would create two definitions
--                   of zero:
--                   1. zero = + zero
--                   2. zero = - zero

-- Let us play a bit with the integers

-- import ≡
open import Relation.Binary.PropositionalEquality.Core
-- import naturals
open import Data.Nat.Base

-- succ and then pred applied to any integer number is that number
pred-succ : (z : ℤ) → Data.Integer.Base.pred (Data.Integer.Base.suc z) ≡ z
pred-succ (+_ n) = refl
pred-succ (-[1+_] 0) = refl
pred-succ (-[1+_] (suc n)) = refl

-- pred and then succ applied to any integer number is that number
succ-pred : (z : ℤ) → Data.Integer.Base.suc (Data.Integer.Base.pred z) ≡ z
succ-pred (+_ zero) = refl
succ-pred +[1+ n ] = refl
succ-pred (-[1+_] n) = refl

-- here we prove that for any integer number,
-- pred (succ z) ≡ succ (pred z)
pred-succ≡succ-pred : (z : ℤ) → Data.Integer.Base.pred (Data.Integer.Base.suc z) ≡ Data.Integer.Base.suc (Data.Integer.Base.pred z)
pred-succ≡succ-pred z = trans (pred-succ z) (sym (succ-pred z))

-- z → -z
opposite : ℤ → ℤ
opposite (+_ zero) = +_ zero
opposite +[1+ n ] = -[1+ n ]
opposite (-[1+_] n) = +[1+_] n

-- LEMMA-TRIVIAL: if x ≡ z then (-x) ≡ (-z)
lemma-trivial : (x z : ℤ) → z ≡ x → opposite z ≡ opposite x
lemma-trivial x z p = cong opposite p

-- LEMMA-OPP-OPP: - (- z) ≡ z
--                the opposite of the opposite of z is z
lemma-opp-opp : (z : ℤ) → opposite (opposite z) ≡ z
lemma-opp-opp (+_ zero) = refl
lemma-opp-opp +[1+ n ] = refl
lemma-opp-opp (-[1+_] n) = refl

-- LEMMA-+-ZERO: any integer number z + 0 is z 
lemma-+-zero : (z : ℤ) → z Data.Integer.Base.+ +0 ≡ z
lemma-+-zero (+_ zero) = refl
-- Goal: +[1+ n Data.Nat.Base.+ 0 ] ≡ +[1+ n ]
lemma-+-zero +[1+ n ] = cong (λ n → +[1+ n ]) (n+0 n)
  where
  n+0 : (n : ℕ) → n Data.Nat.Base.+ 0 ≡ n
  n+0 zero = refl
  n+0 (ℕ.suc n) = cong ℕ.suc (n+0 n)
lemma-+-zero (-[1+_] zero) = refl
lemma-+-zero (-[1+_] (ℕ.suc n)) = refl

-- I did not come up with a property by myself, fortunately
-- a helper lemma was already proven inside the stdlib
open import Data.Integer.Properties

-- LEMMA-0: for any integer z → z + (- z) ≡ 0
lemma-0 : (z : ℤ) → z Data.Integer.Base.+ (opposite z) ≡ +0
lemma-0 (+_ zero) = refl
lemma-0 +[1+ n ] = lemma-0 -[1+ n ]
lemma-0 (-[1+_] zero) = refl
lemma-0 (-[1+_] (ℕ.suc n)) = n⊖n≡0 (ℕ.suc (ℕ.suc n))



