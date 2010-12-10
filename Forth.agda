module Forth where
open import Data.Bool
open import Data.Nat

data Term : Bool → ℕ → Set where
  end : Term false 0
  exec : ∀ {b n} → Term b (suc n) → Term true n
  true false Bool-POP AND NOT Nat-POP ADD LT GT :
    ∀ {n} → Term false n → Term false (suc n)
  nat : ℕ → ∀ {n} → Term false n → Term false (suc n)

eg-I : Term false 3
eg-I = AND (true (false end))

eg-E : Term true 0
eg-E = exec (exec (exec eg-I))

-- data _∣_⊢_ : (Bool Nat : ℕ) → Term → Set where
--   end : 0 ∣ 0 ⊢ end

--   true : ∀ {B N t} →
--     B ∣ N ⊢ t → suc B ∣ N ⊢ true t
--   false : ∀ {B N t} →
--     B ∣ N ⊢ t → suc B ∣ N ⊢ false t
--   Bool-POP : ∀ {B N t} →
--     suc B ∣ N ⊢ t → B ∣ N ⊢ Bool-POP t
--   AND : ∀ {B N t} →
--     suc (suc B) ∣ N ⊢ t → suc B ∣ N ⊢ AND t
--   NOT : ∀ {B N t} →
--     suc B ∣ N ⊢ t → suc B ∣ N ⊢ NOT t

--   nat : ∀ {B N n t} →
--     B ∣ N ⊢ t → B ∣ suc N ⊢ (nat n) t
--   Nat-POP : ∀ {B N t} →
--     B ∣ suc N ⊢ t → B ∣ N ⊢ Nat-POP t
--   ADD : ∀ {B N t} →
--     B ∣ suc (suc N) ⊢ t → B ∣ suc N ⊢ ADD t
--   LT : ∀ {B N t} →
--     B ∣ suc (suc N) ⊢ t → suc B ∣ N ⊢ LT t
--   GT : ∀ {B N t} →
--     B ∣ suc (suc N) ⊢ t → suc B ∣ N ⊢ GT t

