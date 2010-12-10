module Forth where
open import Data.Nat
open import Data.List

data Term : Set where
  end : Term
  true false Bool-POP AND NOT Nat-POP ADD LT GT :
    Term → Term
  nat : ℕ → Term → Term

data _∣_∣_⊢_ : (Exec : Term) (Bool Nat : ℕ) (t : Term) → Set where
  end : end ∣ 0 ∣ 0 ⊢ end

  I-true : ∀ {E B N t} →
    E ∣ B ∣ N ⊢ t →
    true E ∣ B ∣ N ⊢ true t

  E-true : ∀ {E B N t} →
    true E ∣ B ∣ N ⊢ t →
    E ∣ suc B ∣ N ⊢ t

  I-false : ∀ {E B N t} →
    E ∣ B ∣ N ⊢ t →
    false E ∣ B ∣ N ⊢ false t

  E-false : ∀ {E B N t} →
    false E ∣ B ∣ N ⊢ t →
    E ∣ suc B ∣ N ⊢ t

  I-Bool-POP : ∀ {E B N t} →
    E ∣ B ∣ N ⊢ t →
    Bool-POP E ∣ B ∣ N ⊢ Bool-POP t

  E-Bool-POP : ∀ {E B N t} →
    Bool-POP E ∣ suc B ∣ N ⊢ t →
    E ∣ B ∣ N ⊢ t

  I-AND : ∀ {E B N t} →
    E ∣ B ∣ N ⊢ t →
    AND E ∣ B ∣ N ⊢ AND t

  E-AND : ∀ {E B N t} →
    AND E ∣ suc (suc B) ∣ N ⊢ t →
    E ∣ suc B ∣ N ⊢ t

  I-NOT : ∀ {E B N t} →
    E ∣ B ∣ N ⊢ t →
    NOT E ∣ B ∣ N ⊢ NOT t

  E-NOT : ∀ {E B N t} →
    NOT E ∣ suc B ∣ N ⊢ t →
    E ∣ suc B ∣ N ⊢ t

  I-nat : ∀ {E B N n t} →
    E ∣ B ∣ N ⊢ t →
    (nat n) E ∣ B ∣ N ⊢ (nat n) t

  E-nat : ∀ {E B N n t} →
    (nat n) E ∣ B ∣ N ⊢ t →
    E ∣ B ∣ suc N ⊢ t

  I-Nat-POP : ∀ {E B N t} →
    E ∣ B ∣ N ⊢ t →
    Nat-POP E ∣ B ∣ N ⊢ Nat-POP t

  E-Nat-POP : ∀ {E B N t} →
    Nat-POP E ∣ B ∣ suc N ⊢ t →
    E ∣ B ∣ N ⊢ t

  I-ADD : ∀ {E B N t} →
    E ∣ B ∣ N ⊢ t →
    ADD E ∣ B ∣ N ⊢ ADD t

  E-ADD : ∀ {E B N t} →
    ADD E ∣ B ∣ suc (suc N) ⊢ t →
    E ∣ B ∣ suc N ⊢ t

  I-LT : ∀ {E B N t} →
    E ∣ B ∣ N ⊢ t →
    LT E ∣ B ∣ N ⊢ LT t

  E-LT : ∀ {E B N t} →
    LT E ∣ B ∣ suc (suc N) ⊢ t →
    E ∣ suc B ∣ N ⊢ t

  I-GT : ∀ {E B N t} →
    E ∣ B ∣ N ⊢ t →
    GT E ∣ B ∣ N ⊢ GT t

  E-GT : ∀ {E B N t} →
    GT E ∣ B ∣ suc (suc N) ⊢ t →
    E ∣ suc B ∣ N ⊢ t

