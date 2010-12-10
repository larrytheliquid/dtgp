module Forth where
open import Data.Nat

data Term : Set where
  start : Term
  true false : Term → Term
  AND NOT : Term → Term
  nat : ℕ → Term → Term
  ADD : Term → Term
  LT GT : Term → Term

data _∣_⊢_ : (Bool Nat : ℕ) → Term → Set where
  start : 0 ∣ 0 ⊢ start

  true : ∀ {B N t} →
    B ∣ N ⊢ t → suc B ∣ N ⊢ true t
  false : ∀ {B N t} →
    B ∣ N ⊢ t → suc B ∣ N ⊢ false t
  AND : ∀ {B N t} →
    suc (suc B) ∣ N ⊢ t → suc B ∣ N ⊢ AND t
  NOT : ∀ {B N t} →
    suc B ∣ N ⊢ t → suc B ∣ N ⊢ NOT t

  nat : ∀ {B N n t} →
    B ∣ N ⊢ t → B ∣ suc N ⊢ (nat n) t
  ADD : ∀ {B N t} →
    B ∣ suc (suc N) ⊢ t → B ∣ suc N ⊢ ADD t
  LT : ∀ {B N t} →
    B ∣ suc (suc N) ⊢ t → suc B ∣ N ⊢ LT t
  GT : ∀ {B N t} →
    B ∣ suc (suc N) ⊢ t → suc B ∣ N ⊢ GT t

