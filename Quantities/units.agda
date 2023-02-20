module Quantities.units where

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

-- Natural Numbers
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- Addition
_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)