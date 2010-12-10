module Forth where
open import Data.Nat

data Term : Set where
  end : Term
  true false : Term → Term
  Bool-POP : Term → Term
  AND NOT : Term → Term
  nat : ℕ → Term → Term
  Nat-POP : Term → Term
  ADD : Term → Term
  LT GT : Term → Term

data _∣_⊢_ : (Bool Nat : ℕ) → Term → Set where
  end : 0 ∣ 0 ⊢ end

  true : ∀ {B N t} →
    B ∣ N ⊢ t → suc B ∣ N ⊢ true t
  false : ∀ {B N t} →
    B ∣ N ⊢ t → suc B ∣ N ⊢ false t
  Bool-POP : ∀ {B N t} →
    suc B ∣ N ⊢ t → B ∣ N ⊢ Bool-POP t
  AND : ∀ {B N t} →
    suc (suc B) ∣ N ⊢ t → suc B ∣ N ⊢ AND t
  NOT : ∀ {B N t} →
    suc B ∣ N ⊢ t → suc B ∣ N ⊢ NOT t

  nat : ∀ {B N n t} →
    B ∣ N ⊢ t → B ∣ suc N ⊢ (nat n) t
  Nat-POP : ∀ {B N t} →
    B ∣ suc N ⊢ t → B ∣ N ⊢ Nat-POP t
  ADD : ∀ {B N t} →
    B ∣ suc (suc N) ⊢ t → B ∣ suc N ⊢ ADD t
  LT : ∀ {B N t} →
    B ∣ suc (suc N) ⊢ t → suc B ∣ N ⊢ LT t
  GT : ∀ {B N t} →
    B ∣ suc (suc N) ⊢ t → suc B ∣ N ⊢ GT t

