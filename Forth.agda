module Forth where
open import Data.Nat

data Term : Set where
  start : Term
  true false : Term → Term
  AND NOT : Term → Term

data _⊢_ : (Bool : ℕ) → Term → Set where
  start : 0 ⊢ start
  true : ∀ {b t} →
    b ⊢ t → suc b ⊢ true t
  AND : ∀ {b t} →
    suc (suc b) ⊢ t → b ⊢ AND t
