-------------------------------
-- TUTORIAL: Natural Numbers --
-------------------------------

open import Data.Nat.Base

-- Here we define some natural numbers for quicker testings
one   = Data.Nat.Base.suc zero
two   = Data.Nat.Base.suc one
three = Data.Nat.Base.suc two
four  = Data.Nat.Base.suc three
five  = Data.Nat.Base.suc four

-- However, the arabic numbers are defined upon importing
-- Data.Nat.Base, you can try it:
-- >> Ctrl-C + Ctrl-N
-- >> 1 + 99
-- Output: 100

--Halving function (rounded up)
half : ℕ → ℕ
half zero = zero            -- 0 / 2 = 0
half (suc zero) = suc zero  -- 1 / 2 = 0.5 → 1
half (suc n) = suc (half n) -- (n + 1)/2 = n/2 + 1  

-- We can define the same using arabic numbers
half' : ℕ → ℕ
half' 0 = 0
half' (suc 0) = 1
half' (suc n) = suc (half n)

_add_ : ℕ → ℕ → ℕ
a add zero = a
a add suc b = suc (a add b) -- a + (b + 1) = 1 + (a + b)

-- Now that we can use the standard-library, there is no need
-- to define the most basic functions and lemmas, for example
-- by importing Data.Nat.Base we imported the _+_ function.
-- We can demonstrate that our custom _add_ function has
-- the same outputs of the _+_ functions.

-- To prove the equivalence we need the equivalence ≡
-- this can be done by importing the following:
open import Relation.Binary.PropositionalEquality.Core
-- Other than the ≡, we imported its properties
-- cong  (congruence)
-- trans (transitivity)
-- sym   (symmetry)
-- ...

same-thing : (n m : ℕ) → n add m ≡ n + m
same-thing n zero = helper n
  where
    helper : (n : ℕ) → n ≡ n + zero
    helper zero = refl
    helper (suc n) = cong suc (helper n)
same-thing n (suc m) = trans ((cong suc (same-thing n m))) (sym (helper' n m))
  where
    helper' : (n m : ℕ) → n + suc m ≡ suc (n + m)
    helper' zero m = refl
    helper' (suc n) m = cong suc (helper' n m)

