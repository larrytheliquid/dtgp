module Combined where
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Data.Maybe
open import Term

infixl 2 _⊢_∶_∣_

data _⊢_∶_∣_ : ∀ {m n} (E : Term m) (t : Term n) (Bool Nat : ℕ) → Set where
  empty : ∀ {n B} {t : Term n} → [] ⊢ t ∶ B ∣ 0

  Exec-POP : ∀ {m n B N w} {E : Term m} {t : Term n} →
                   E ⊢ t ∶ B ∣ N →
    Exec-POP ∷ w ∷ E ⊢ t ∶ B ∣ N

  Exec-DUP : ∀ {m n B N w} {E : Term m} {t : Term n} →
                   E ⊢ t ∶ B ∣ N →
    Exec-DUP ∷ w ∷ E ⊢ t ∶ B ∣ N

  Exec-EQ : ∀ {m n B N w₁ w₂} {E : Term m} {t : Term n} →
                       E ⊢ t ∶     B ∣ N →
    Exec-EQ ∷ w₁ ∷ w₂ ∷ E ⊢ t ∶ suc B ∣ N

  Exec-K : ∀ {m n B N w₁ w₂} {E : Term m} {t : Term n} →
                 w₁ ∷ E ⊢ t ∶ B ∣ N →
    Exec-K ∷ w₁ ∷ w₂ ∷ E ⊢ t ∶ B ∣ N

  Exec-SWAP : ∀ {m n B N w₁ w₂} {E : Term m} {t : Term n} →
                w₂ ∷ w₁ ∷ E ⊢ t ∶ B ∣ N →
    Exec-SWAP ∷ w₁ ∷ w₂ ∷ E ⊢ t ∶ B ∣ N

  Exec-ROT : ∀ {m n B N w₁ w₂ w₃} {E : Term m} {t : Term n} →
               w₃ ∷ w₁ ∷ w₂ ∷ E ⊢ t ∶ B ∣ N →
    Exec-ROT ∷ w₁ ∷ w₂ ∷ w₃ ∷ E ⊢ t ∶ B ∣ N

  Exec-S : ∀ {m n B N w₁ w₂ w₃} {E : Term m} {t : Term n} →
        w₂ ∷ w₃ ∷ w₃ ∷ w₁ ∷ E ⊢ t ∶ B ∣ N →
    Exec-S ∷ w₁ ∷ w₂ ∷ w₃ ∷ E ⊢ t ∶ B ∣ N

  Exec-STACKDEPTH : ∀ {m n B N} {E : Term m} {t : Term n} →
                      E ⊢ t ∶ B ∣     N →
    Exec-STACKDEPTH ∷ E ⊢ t ∶ B ∣ suc N

  true : ∀ {m n B N} {E : Term m} {t : Term n} →
           E ⊢ t ∷ʳ true ∶ suc B ∣ N →
    true ∷ E ⊢ t         ∶     B ∣ N

  false : ∀ {m n B N} {E : Term m} {t : Term n} →
            E ⊢ t ∷ʳ false ∶ suc B ∣ N →
    false ∷ E ⊢ t          ∶     B ∣ N

  Bool-POP : ∀ {m n B N} {E : Term m} {t : Term n} →
               E ⊢ t             ∶ suc B ∣ N →
    Bool-POP ∷ E ⊢ t ∷ʳ Bool-POP ∶     B ∣ N

  AND : ∀ {m n B N} {E : Term m} {t : Term n} →
          E ⊢ t ∷ʳ AND ∶      suc B  ∣ N →
    AND ∷ E ⊢ t        ∶ suc (suc B) ∣ N

  NOT : ∀ {m n B N} {E : Term m} {t : Term n} →
          E ⊢ t ∷ʳ NOT ∶ suc B ∣ N →
    NOT ∷ E ⊢ t        ∶ suc B ∣ N

  nat : ∀ {m n B N v} {E : Term m} {t : Term n} →
            E ⊢ t          ∶     B ∣     N →
    nat v ∷ E ⊢ t ∷ʳ nat v ∶     B ∣ suc N

  Nat-POP : ∀ {m n B N} {E : Term m} {t : Term n} →
              E ⊢ t            ∶ B ∣ suc N →
    Nat-POP ∷ E ⊢ t ∷ʳ Nat-POP ∶ B ∣     N

  ADD : ∀ {m n B N} {E : Term m} {t : Term n} →
          E ⊢ t        ∶ B ∣ suc (suc N) →
    ADD ∷ E ⊢ t ∷ʳ ADD ∶ B ∣      suc N

  LT : ∀ {m n B N} {E : Term m} {t : Term n} →
         E ⊢ t       ∶     B ∣ suc (suc N) →
    LT ∷ E ⊢ t ∷ʳ LT ∶ suc B ∣          N

  GT : ∀ {m n B N} {E : Term m} {t : Term n} →
         E ⊢ t       ∶     B ∣ suc (suc N) →
    GT ∷ E ⊢ t ∷ʳ GT ∶ suc B ∣          N
