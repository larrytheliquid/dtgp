module Rel where
open import Data.Nat

data Term (A : ℕ) : ℕ → Set where
  []  : Term A A
  true : {n : ℕ} → Term A n → Term A (1 + n)
  not  : {n : ℕ} → Term A (1 + n) → Term A (1 + n)
  and  : {n : ℕ} → Term A (2 + n) → Term A (1 + n)
